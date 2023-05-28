use std::collections::HashMap;
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::fmt::Display;
use std::iter::{self, FromIterator};
use std::result::Result as StdResult;
use std::str::FromStr;

use std::marker::PhantomData;


/// Return pattern for all required argument kinds.
macro_rules! required_kinds {
    () => { Kind::Required | Kind::List(1..) };
}

/// Represents a string that is found in the command line arguments.
#[derive(Debug, Clone)]
pub struct Arg {
    value: String,
    type_: Key,
}

impl Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// The way a string found in command line arguments is interpreted as.
#[derive(Debug, Clone)]
pub enum Key {
    Position,
    // TODO: Use the field for referring to the _original_ group where the key
    // eventually gets split from.
    Short { group_size: usize },
    Long,
}

/// Type for keeping track of the kind of argument associated with the
/// program argument.
#[derive(Debug, Clone)]
pub enum Value {
    None,
    Just(String),
    List(Vec<String>),
}

impl Value {
    /// Add the string to the value and "upgrade" to the bigger variant along
    /// the way.
    fn push(&mut self, value: String) {
        match self {
            Self::None     => {
                *self = Self::Just(value);
            },
            Self::Just(x)  => {
                *self = Self::List(vec![x.to_owned(), value]);
            },
            Self::List(xs) => {
                xs.push(value);
            },
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f, "{}", match self {
                Self::None     => "".to_owned(),
                Self::Just(x)  => x.clone(),
                Self::List(xs) => xs.join(", "),
            },
        )
    }
}

pub trait FromSmarg: Sized {
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error>;
}

impl<T> FromSmarg for List<T>
where
    T: FromStr + fmt::Debug,
    <T as FromStr>::Err: error::Error + 'static,
{
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error> {
        match &smarg.value {
            Value::None     => Err(Error::Missing(smarg)),
            Value::Just(x)  => Ok(List(vec![<T as FromStr>::from_str(x).map_err(|e| Error::Parsing { of: smarg, failed_with: Box::new(e) })?])),
            Value::List(xs) => {
                let mut results: Vec<Option<StdResult<T, _>>> = xs.iter().map(|x| Some(<T as FromStr>::from_str(x))).collect();
                let mut found_error = None;
                for (i, result) in results.iter().enumerate() {
                    if result.as_ref().unwrap().is_err() {
                        found_error = Some(i);
                        break;
                    }
                }
                if let Some(i) = found_error {
                    let error = results[i].take().unwrap().unwrap_err();
                    Err(Error::Parsing { of: smarg, failed_with: Box::new(error) })
                } else {
                    let values = results.into_iter().map(|x| x.unwrap().unwrap()).collect();
                    Ok(List(values))
                }
            },
        }
    }
}

impl<T> FromSmarg for T
where
    T: FromStr,
    <T as FromStr>::Err: error::Error + 'static,
{
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error> {
        match &smarg.value {
            Value::None     => Err(Error::Missing(smarg)),
            Value::Just(x)  => <T as FromStr>::from_str(x).map_err(|e| Error::Parsing { of: smarg.clone(), failed_with: Box::new(e) }),
            Value::List(_xs) => panic!("bad"),
        }
    }
}

/// Wrapper to `Vec` that allows support for multiple values per one argument
/// definition.
/// TODO: Make this always contain a minimum number of items to work together
/// with the SmargKind::List(min).
pub struct List<T: FromStr>(pub Vec<T>);

        
impl<T: FromStr> From<List<T>> for Vec<T> {
    fn from(value: List<T>) -> Self {
        value.0
    }
}

/// Struct for defining program arguments and parsing them from command line
/// syntax into required types.
#[derive(Debug)]
pub struct Smargs<Ts> {
    /// Thing to iterate over values with when parsing.
    index: usize,
    /// Name of the program (from the first item in argument list).
    name: String,
    description: String,
    /// Mapping of positions to argument definitions and given arguments
    /// stored for parsing later.
    list: Vec<Smarg>,
    /// Mapping of keys to to positions.
    map: HashMap<String, usize>,
    /// NOTE: This is here in order to support the `smärgs`-macro implementing
    /// `TryFrom<Smargs<_>> for CustomOutput`.
    output: PhantomData<Ts>,
}

impl<Ts> Smargs<Ts>
where
    Ts: TryFrom<Self, Error = Error>,
{
    /// Build a new `Smargs` instance from an ordered collection of `Smarg`
    /// definitions in tuple form.
    pub fn with_definition<const N: usize>(
        desc: &'static str,
        definition: [(&'static str, Vec<&'static str>, Kind); N]
    ) -> Self {
        let mut smargs = Smargs::new(desc);
        for (s, ks, k) in definition {
            smargs.push(Smarg { desc: s, keys: ks, kind: k, value: Value::None });
        }
        smargs
    }

    /// Parse the argument strings into the type `Ts` according to the
    /// definition of `self` which may include using default values for some
    /// fields.
    /// 
    /// Note that the name of the program/command is assumed to be the first
    /// item in `args`.
    pub fn parse(mut self, mut args: impl DoubleEndedIterator<Item = String>) -> StdResult<Ts, Box<Break>>
    {
        if let Some(name) = args.next() {
            self.name = name;
        }

        // Now that no more arguments can be defined, generate the help message.
        let help = self.get_help();

        let mut values = self.explicit_values(args, &help)?;

        // Handle missing values based on kinds and defaults.
        for (i, value) in values
            .iter_mut()
            .enumerate()
            .filter(|(_, x)| x.is_none())
        {
            let fillin = match self.list[i].kind {
                    Kind::Optional(default) => Value::Just(default.to_owned()),
                    Kind::Flag | Kind::Help => Value::Just(false.to_string()),
                    required_kinds!() => {
                        return Err(help.short_break(Error::Missing(self.list[i].clone())));
                    },
                    Kind::List(_) => Value::List(vec![]),
                    Kind::Maybe => Value::None,
            };
            value.replace(fillin);
        }

        // Update self with the resolved values.
        for (i, value) in values.into_iter().map(|x| x.expect("not all values handled")).enumerate() {
            self.list[i].value = value;
        }

        Ts::try_from(self).map_err(|err| help.short_break(err))
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env(self) -> StdResult<Ts, Box<Break>> {
        self.parse(std::env::args())
    }

    /// Set the help keys to: "-h" and "--help". See `Self::help_keys`.
    pub fn help_default(self) -> Self {
        self.help_keys(vec!["h", "help"])
    }

    /// Convenience method for defining the argument with which to request for a
    /// help message. When any of the `keys` are encountered, the argument
    /// parsing will be interrupted and return an automatically generated help
    /// message.
    pub fn help_keys(mut self, keys: Vec<&'static str>) -> Self {
        self.push(Smarg { desc: "Show this help message", keys, kind: Kind::Help, value: Value::None });

        self
    }

    /// Generate and return help messages based on `self`.
    fn get_help(&self) -> Help {
        // Generate some quick and short how-to reminder.
        let usage = &format!(
            "Usage: {} {}",
            self.name,
            self.list
                .iter()
                // Do _not_ include Help in usage list.
                .filter_map(|x| (!matches!(x.kind, Kind::Help)).then_some(x.kind.to_string()))
                .zip(iter::repeat(' '))
                .fold(
                    String::new(),
                    |mut acc, (l, r)| { acc.push_str(&l); acc.push(r); acc }
                )
        );

        let mut short = usage.clone();
        if let Smarg { keys, kind: Kind::Help, .. } = &self.list[0] {
            short.push_str(&format!(
                "\nTry '{} {}' for more information.",
                self.name,
                // TODO: `keys` is not guaranteed to be something. Check for
                // keys.len() in self.push(Smarg)?
                match keys.iter().max().unwrap() {
                    s if s.len() == 1 => format!("-{}", s),
                    s => format!("--{}", s)
                },
            ));
        }

        let mut long = format!("{}\n{}", usage, self.description);

        long.push_str("\n\nArgument descriptions:\n");
        // Find the longest Smarg-string in order to nicely line up the
        // descriptions to start from the same column.
        let (max_width, details) = self.list
            .iter()
            .fold(
                (0, Vec::with_capacity(self.list.len())),
                |(max_len, mut acc), x| {
                    let usage = x.to_string();
                    let len = usage.len();
                    acc.push((usage, x.desc));
                    (if len > max_len { len } else { max_len }, acc)
                }
            );

        let pad_len = max_width + 5;
        for (arg_usage, arg_desc) in details {
            let pad_right = " ".repeat(pad_len);
            let row_padded = format!("  {}{}", arg_usage, pad_right);
            long.extend(row_padded.chars().take(pad_len));
            long.push_str(arg_desc);
            long.push('\n');
        }

        Help { short, long }
    }

    /// Find the explicitly provided values based on definition and `args`.
    ///
    /// NOTE: The amount of resulting values must be equal to the amount of
    /// definitions!
    fn explicit_values(
        &self,
        args: impl DoubleEndedIterator<Item = String>,
        help: &Help
    ) -> StdResult<Vec<Option<Value>>, Box<Break>> {
        let mut state: ValueParserState = ValueParserState::new(args, self.list.len());
        state.rindex = self.list.iter().position(|x| x.kind.is_required());

        while let Some(arg) = state.stack.pop() {
            // Remove the cli-syntax off of keys and normalize the
            // multi-character groups.

            // Assume prefix length is max 2.
            // Invalid keys like ones with >2 prefixed dashes will be catched
            // when querying from the key set validated at definition time.
            let arg = {
                let (prefix_len, stripped_key) = {
                    let (fst, snd) = arg.split_at(arg.bytes().take(2).take_while(|b| *b == b'-').count());
                    let n = fst.len();
                    // Check that things like negative numbers are not
                    // interpreted as keys.
                    if n == 1 && Self::validate_key_name(snd).is_err() {
                        (0, arg)
                    } else {
                        (n, snd.to_string())
                    }
                };
                Arg {
                    // NOTE: 'arg' is redefined as not having the prefixed
                    // dashes.
                    value: stripped_key.to_owned(),
                    type_: match prefix_len {
                        0 => Key::Position,
                        1 => Key::Short { group_size: stripped_key.len() },
                        _ => Key::Long,
                    }
                }
            };

            match arg.type_ {
                Key::Position => {
                    // TODO: CHECK IMPLEMENTATION: The positioned options
                    // have lower precedence compared to the explicit
                    // key-value method.
                    let idx = state.rindex
                        .ok_or_else(|| help.short_break(Error::UndefinedArgument(arg.clone())))?;
                    if let Some(first_val) = state.values[idx].replace(Value::Just(arg.clone().value)) {
                        return Err(help.short_break(
                            Error::Duplicate {
                                first: (
                                    state.history[idx].as_mut().unwrap().pop().unwrap(),
                                    first_val
                                ),
                                extra: (
                                    arg,
                                    state.values[idx].take().unwrap(),
                                )
                            }
                        ));
                    }
                    state.next_unsatisfied_required_position(&self.list);
                },
                Key::Short { group_size: 2.. } => {
                    // Replace the args-queue's front with the "normalized"
                    // multi-character group (which consist of multiple flags +
                    // possibly a key at the end
                    // i.e., "-abk <value>" => "-a -b -k <value>").
                    let keys = arg.value.chars().map(|c| format!("-{}", c));
                    // Insert the keys "in order" to the "stack" i.e.,
                    // order:  0, 1,..     0, 1, 2,..     0, 1, 2, 3,..
                    // elem:  -a:-_:xs -> -a:-b:-_:xs -> -a:-b:-k:-_:xs -> ...
                    state.stack.extend(keys.rev());
                    // Let the main-loop handle these added "new" keys normally.
                },
                Key::Long | Key::Short { group_size: 1 } => {
                    // Save the handled arg and how it was got for future
                    // reference in case of errors.
                    state.resolve_keyed_value(self, arg, help)?;
                },
                Key::Short { .. } => {
                    panic!("should be impossible to have matched '-'");
                }
            }
        }

        Ok(state.values.to_vec())
    }

    /// NOTE: Not to be called by user directly; instead use the `From`
    /// implementations or `smärgs` macro!
    /// 
    /// Parse into the type `T` the next value of arg defined in running order.
    pub fn parse_next<T>(&mut self) -> StdResult<T, Error>
    where
        T: FromSmarg,
    {
        // TODO This seems unnecessarily complex...
        let index = self.index;
        let smarg = self
            .list
            .get(index)
            .take()
            .unwrap_or_else(|| panic!("nothing in index {}", index));

        let return_value = <T as FromSmarg>::from_smarg(smarg.to_owned());

        // Update index.
        self.index += 1;

        return_value
    }

    /// Initialize an empty `Smargs` struct.
    ///
    /// `description` is the general description of the program.
    pub fn new(description: &str) -> Self {
        Self {
            index: 0,
            name: String::default(),
            description: description.to_owned(),
            list: Vec::new(),
            map: HashMap::new(),
            output: PhantomData,
        }
    }

    /// Perform checks on new argument definition and add it to the collection
    /// or panic if checks fail.
    pub fn push(&mut self, smarg: Smarg) {
        Self::validate_key_names(&smarg.keys);

        // Get the correct index to insert (not push) into.
        let handle = if let Kind::Help = smarg.kind {
            if let Some(Smarg { kind: Kind::Help, .. }) = self.list.get(0) {
                panic!("the help argument can not be defined more than once");
            }
            // The zeroth index is reserved for Help so all the others will be
            // shifted once to the right, which is equivalent to incrementing
            // each existing handle by one.
            for handle in self.map.values_mut() {
                *handle += 1;
            }
            // Skip the Help-index when parsing.
            self.index = 1;
            0
        } else {
            self.list.len()
        };

        // Save and check for duplicate keys in definition.
        for key in &smarg.keys {
            if self.map.insert(key.to_string(), handle).is_some() {
                panic!("duplicate key defined: '{}'", key);
            }
        }

        // Finally add the definition.
        self.list.insert(handle, smarg);
    }

    /// Check that the keys (__without prefixes__) conform to rules and panic
    /// otherwise.
    fn validate_key_names(keys: &[&'static str]) {
        // __Whitelist__ the allowed characters.
        for key in keys {
            if let Err(msg) = Self::validate_key_name(key) {
                panic!("{}", msg)
            }
        }
    }

    fn validate_key_name(key: &str) -> StdResult<(), String> {
        const START_CHARACTERS: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const POST_START_CHARACTERS: &[u8] = b"-0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        if key.is_empty() {
            return Err("a key must not be empty".to_owned());
        }
        if key.contains(' ') {
            return Err(format!("a key must not contain spaces: '{}'", key));
        }
        if !key.is_ascii() {
            return Err(format!("a key must only contain ASCII characters: {}", key));
        }
        
        let mut bytes = key.bytes();
        // This is OK as key is guaranteed to contain >0 bytes AND all
        // characters in key at this point are confirmed to be ASCII.
        let first_char = bytes.next().unwrap() as char;
        if !START_CHARACTERS.contains(first_char) {
            return Err(format!(
                "a key must begin with ASCII alphabet: {}",
                key.replace(first_char, &format!("***{}***", first_char))
            ));
        }
        for byte in bytes {
            if !POST_START_CHARACTERS.contains(&byte) {
                let bad_char = byte as char;
                return Err(format!(
                    "a key must only contain ASCII alphabet, numbers or dash '-': {}",
                    key.replace(bad_char, &format!("***{}***", bad_char))
                ));
            }
        }
        Ok(())
    }
}

struct ValueParserState {
    /// "RequiredINDEX"; index of the next required definition.
    rindex: Option<usize>,
    stack: Vec<String>,
    /// Record for how each value was collected.
    history: Vec<Option<Vec<Arg>>>,
    /// Values found matching each received argument. The index is a
    /// handle to the history, where this value was picked from.
    values: Vec<Option<Value>>,
}
impl ValueParserState {
    fn new(args: impl DoubleEndedIterator<Item = String>, n: usize) -> Self {
        Self {
            rindex: None,
            stack: Vec::from_iter(args.rev()),
            history: iter::repeat_with(|| None).take(n).collect(),
            values: iter::repeat_with(|| None).take(n).collect(),
        }
    }

    fn next_unsatisfied_required_position(&mut self, definitions: &[Smarg]) {
        self.rindex = definitions
            .iter()
            .enumerate()
            .find_map(|(i, x)|
                (
                    x.kind.is_required() && self.values[i].is_none()
                    || matches!((&x.kind, &self.values[i]), (Kind::List(n), Some(Value::List(xs))) if xs.len() < *n)
                )
                .then_some(i)
            );
    }

    /// Select and update state based on the matched value for given key, i.e.,
    /// the thing "resolved" here is definitely a "-key [value]" type of deal.
    fn resolve_keyed_value<Ts>(
        &mut self,
        smargs: &Smargs<Ts>,
        arg: Arg,
        help: &Help,
    ) -> StdResult<(), Box<Break>> {
        let key_matched_index = *smargs.map
            .get(&arg.value)
            .ok_or_else(|| help.short_break(Error::UndefinedKey(arg.clone())))?;

        let smarg = smargs.list
            .get(key_matched_index)
            .expect("position not found");

        match smarg.kind {
            Kind::Help => {
                // In case help is requested in the arguments e.g.
                // in the form of `--help`, interrupt the parsing
                // here and return the more detailed help-message.
                return Err(help.long_break(Error::Help));
            },
            Kind::Flag => {
                if let Some(first_val) = self.values[key_matched_index].replace(Value::Just(true.to_string())) {
                    return Err(help.short_break(
                        Error::Duplicate {
                            first: (
                                self.history[key_matched_index].as_mut().unwrap().pop().unwrap(),
                                first_val,
                            ),
                            extra: (
                                arg,
                                self.values[key_matched_index].take().unwrap(),
                            )
                        }
                    ));
                }
                // Update history; index matches with chosen value.
                let history = vec![arg];
                assert!(
                    self.history[key_matched_index].replace(history).is_none(),
                    "should be impossible to overwrite flag's history"
                );
            },
            Kind::List(_min) => {
                if let Some(list) = self.values[key_matched_index].as_mut() {
                    if let Some(value) = self.stack.pop() {
                        list.push(value);
                    } else {
                        return Err(help.short_break(
                            Error::Missing(smargs.list[key_matched_index].clone()),
                        ));
                    }
                }
                // Update history; index matches with chosen value.
                if self.history[key_matched_index].is_some() {
                    self.history[key_matched_index].as_mut().unwrap().push(arg);
                } else {
                    self.history[key_matched_index].replace(vec![]);
                }
            },
            _ => {
                if let Some(value) = self.stack.pop() {
                    if let Some(first_val) = self.values[key_matched_index].replace(Value::Just(value)) {
                        return Err(help.short_break(
                            Error::Duplicate {
                                first: (
                                    self.history[key_matched_index].as_mut().unwrap().pop().unwrap(),
                                    first_val,
                                ),
                                extra: (
                                    arg,
                                    self.values[key_matched_index].take().unwrap(),
                                ),
                            }
                        ));
                    }
                    // Update the position because this required was received
                    // based on key-value.
                    self.next_unsatisfied_required_position(&smargs.list);
                    // Update history; index matches with chosen value.
                    let history = vec![arg];
                    assert!(
                        self.history[key_matched_index].replace(history).is_none(),
                        "should be impossible to overwrite option's history"
                    );
                } else {
                    return Err(help.short_break(Error::Missing(smarg.clone())));
                }
            },
        }
        Ok(())
    }
}


/// More elaborative explanation for an error.
#[derive(Debug)]
pub enum ErrorKind {
    Duplicate,
    MissingValue,
    Parsing(&'static str, String, Box<dyn error::Error>),
}

/// Struct containing short and long descriptions of a program and its
/// arguments. The `short` message is preferred during generic error conditions
/// and `long` when explicitly requesting for help.
#[derive(Debug)]
struct Help { short: String, long: String }

impl Help {
    fn short_break(&self, err: Error) -> Box<Break> {
        Box::new(Break { err, help: self.short.clone() })
    }

    fn long_break(&self, err: Error) -> Box<Break> {
        Box::new(Break { err, help: self.long.clone() })
    }
}

/// The reason for interruption or "break" when parsing based on `Smargs` can
/// either be because an error occurred or because of an explicit help-request
/// to describe the program by its arguments.
/// TODO: `impl ops::Try for Break`?
#[derive(Debug)]
pub struct Break { pub err: Error, pub help: String }

impl error::Error for Break { }

/// Error type for getting and parsing the values of arguments.
#[derive(Debug)]
pub enum Error {
    /// Convenience for users working with `Error`. Wrap the user-defined
    /// `error` in `Error::Dummy` so it can be passed around like other `Error`
    /// variants.
    Dummy(Box<dyn error::Error>),
    /// Found an unexpected extra match for `Smarg`.
    Duplicate { first: (Arg, Value), extra: (Arg, Value) },
    /// Instructions were explicitly request i.e., the help-key was found.
    Help,
    /// A matching value for `Smarg` was expected but is missing.
    Missing(Smarg),
    /// Parsing from `Value` as matched to `Smarg` failed.
    Parsing { of: Smarg, failed_with: Box<dyn error::Error> },
    /// No match found for given argument.
    UndefinedArgument(Arg),
    /// No match found for given key.
    UndefinedKey(Arg),
}

/// Select between generic or argument-specific error messages.
impl fmt::Display for Break {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Interrupted because {}\n\n{}", self.err, self.help)
    }
}

/// Generate nicer error-messages to print for user.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::Dummy(error) => format!("{}, baka.", error),
            Self::Duplicate { first, extra } => {
                format!(
                    "already matched {}: {} but then found {}: {}",
                    first.0, first.1, extra.0, extra.1,
                )
            },
            Self::Help => "help".to_owned(),
            Self::Missing(smarg) => format!("argument missing for {}", smarg),
            Self::Parsing { of, failed_with } => {
                format!(
                    "failed to parse {}: {:?}",
                    of, failed_with
                )
            },
            Self::UndefinedArgument(arg) => format!("extra argument '{}'", arg),
            // TODO Suggest similar existing arguments in case of user typo.
            Self::UndefinedKey(key) => format!("option '{}' does not exist", key),
        };
        write!(f, "{}", msg)
    }
}

/// Contains information about a definition (or declaration?) of
/// and the concrete value assigned to a program argument.
#[derive(Debug, Clone)]
pub struct Smarg {
    pub desc: &'static str,
    pub keys: Vec<&'static str>,
    pub kind: Kind,
    pub value: Value
}

impl Display for Smarg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keystring: String = {
            let mut xs = self.keys.clone();
            // Sort by alphabet + length as normal (shortest first).
            xs.sort();
            // Sort in reverse-length second.
            xs.sort_by(|x, y| x.len().cmp(&y.len()).reverse());
            xs.iter()
                .map(|x| format!("{}{} ", if x.len() == 1 { "-" } else { "--" }, x))
                .collect()
        };

        let note = match &self.kind {
            Kind::Required => "<required value>".to_owned(),
            Kind::Optional(default) => format!("<value OR '{}'>", default),
            Kind::Flag | Kind::Help => "Negated by default".to_owned(),
            Kind::List(n) => format!("List of {} or more values", n),
            Kind::Maybe => "<value OR ??>".to_owned(),
        };

        write!(f, "{}{}", keystring, note)
    }
}

/// Describes the argument and how it is supplied.
#[derive(Debug, Clone)]
pub enum Kind {
    /// Special flag for requesting the help message.
    Help,
    /// An argument which __needs__ to be provided by the user.
    Required,
    /// An argument with a default value that will be used if nothing is
    /// provided by the user.
    Optional(&'static str),
    /// A boolean argument defaulting to FALSE because using a flag essentially
    /// means signaling the event of or __turning on__ something, certainly not
    /// the contrary.
    Flag,
    /// A collection of some minimum number of arguments.
    List(usize),
    /// An argument that returns with its error instead of interrupting (i.e.,
    /// `Break`ing) so the default can be computed after when parsing has
    /// failed.
    Maybe,
}

impl Kind {
    /// Return whether this represents a required argument.
    fn is_required(&self) -> bool {
        matches!(self, required_kinds!())
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            Self::Help        => "(HELP)".to_owned(),
            Self::Required    => "REQUIRED".to_owned(),
            Self::Optional(_) => "<OPTIONAL>".to_owned(),
            Self::Flag        => "<FLAG>".to_owned(),
            Self::List(0)     => "[OPTIONAL]".to_owned(),
            Self::List(n)     => format!("[REQUIRED; {}]", n),
            Self::Maybe       => "MAYBE?".to_owned(),
        })
    }
}

#[derive(Debug)]
pub struct Result<T>(pub StdResult<T, Error>);

/// Generic implementation for all types that implement `FromStr` but
/// into the Result-wrapper for returning errors from parsing specific
/// arguments.
impl<T> FromSmarg for Result<T>
where
    T: FromSmarg,
{
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error> {
        // The Result-wrapper will always be constructed (containing the value or
        // an error), so "failing to parse" it from string is impossible.
        Ok(Result(<T as FromSmarg>::from_smarg(smarg)))
    }
}

/// This implementation supports adding a help message to an argumentless
/// program.
impl TryFrom<Smargs<Self>> for () {
    type Error = Error;
    fn try_from(_: Smargs<Self>) -> StdResult<Self, Self::Error> {
        Ok(())
    }
}

/// Mass-implement `TryFrom<Smargs<_>>` for tuples made up of types implementing
/// `FromStr`.
macro_rules! tryfrom_impl {
    ( $( $t:tt ),* ) => {
        impl<$( $t ),*> TryFrom<Smargs<Self>> for ( $( $t, )* )
        where
            $(
                $t: FromSmarg,
            )* {
            type Error = Error;
            fn try_from(mut smargs: Smargs<Self>) -> StdResult<Self, Error> {
                Ok( ($( smargs.parse_next::<$t>()?, )*) )
            }
        }       
    };
}

tryfrom_impl!(T1);
tryfrom_impl!(T1,T2);
tryfrom_impl!(T1,T2,T3);
tryfrom_impl!(T1,T2,T3,T4);
tryfrom_impl!(T1,T2,T3,T4,T5);
tryfrom_impl!(T1,T2,T3,T4,T5,T6);
tryfrom_impl!(T1,T2,T3,T4,T5,T6,T7);
tryfrom_impl!(T1,T2,T3,T4,T5,T6,T7,T8);

#[cfg(test)]
mod tests {
    use super::{Break, Error, Smargs, Smarg, Value, Key, Arg, Kind, List, Result};

    // NOTE: Naming conventions:
    // Scheme: <target method>_<scenario>_res[ults in]_<expected behavior>,
    // Abbreviations:
    // req == Required argument, opt == Optional argument,
    // <N>th == Argument position in definition,
    // Ordinality == Argument position in input.

    #[test]
    fn parse_2_reqs_by_position_res_reqs_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
                ("B", vec!["b"], Kind::Required),
            ])
            .parse("x 0 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_1st_req_by_short_key_fst_res_2nd_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
                ("B", vec!["b"], Kind::Required),
            ])
            .parse("x -a 0 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_1st_req_by_long_key_fst_res_2nd_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["aa"], Kind::Required),
                ("B", vec!["b"], Kind::Required),
            ])
            .parse("x --aa 0 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_2nd_req_by_key_fst_res_1st_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
                ("B", vec!["b"], Kind::Required),
            ])
            .parse("x -b 1 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_req_int_by_position_looks_like_key_res_req_from_position() {
        let (a,) = Smargs::<(i32,)>::with_definition(
            "Test program",
            [
                ("A" , vec!["a"], Kind::Required),
            ])
            .parse("x -1".split(' ').map(String::from))
            .unwrap();
        
        assert_eq!(a, -1);
    }

    #[test]
    fn parse_req_string_by_key_value_looks_like_another_key_res_req_from_value() {
        let (s, a) = Smargs::<(String, usize)>::with_definition(
            "Test program",
            [
                ("S" , vec!["s"], Kind::Required),
                ("A" , vec!["a"], Kind::Optional("0")),
            ])
            .parse("x -s -a".split(' ').map(String::from))
            .unwrap();
        
        assert_eq!(s, "-a");
        assert_eq!(a, 0);
    }

    // TODO: Would this be usual/logical behaviour? Could using the "--" before
    // positional arguments or smth help the confusion?
    //#[test]
    fn parse_req_string_by_position_looks_like_key_res_req_from_position() {
        let (s,) = Smargs::<(String,)>::with_definition(
            "Test program",
            [
                ("S" , vec![], Kind::Required),
            ])
            .parse("x -s".split(' ').map(String::from))
            .unwrap();
        
        assert_eq!(s, "-s");
    }

    #[test]
    fn parse_no_opt_res_opt_from_default() {
        let (a,) = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Optional("0")),
            ])
            .parse("x".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
    }

    #[test]
    fn parse_opt_by_key_res_opt_from_value() {
        let (a,) = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Optional("1")),
            ])
            .parse("x -a 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
    }

    #[test]
    fn parse_no_flag_res_flag_from_false() {
        let (a,) = Smargs::<(bool,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Flag),
            ])
            .parse("x".split(' ').map(String::from))
            .unwrap();

        assert!(!a);
    }

    #[test]
    fn parse_flag_by_key_res_flag_from_true() {
        let (a,) = Smargs::<(bool,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Flag),
            ])
            .parse("x -a".split(' ').map(String::from))
            .unwrap();

        assert!(a);
    }

    #[test]
    fn parse_1st_flag_2nd_req_by_key_group_res_2nd_req_from_value() {
        let (a, b) = Smargs::<(bool, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Flag),
                ("B", vec!["b"], Kind::Required),
            ])
            .parse("x -ab 1".split(' ').map(String::from))
            .unwrap();

        assert!(a);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_list2_by_keys_res_list2_from_values() {
        let (a,) = Smargs::<(List<usize>,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::List(2)),
            ])
            .parse("x -a 0 -a 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.first(), Some(&0));
        assert_eq!(a.0.get(1), Some(&1));
    }

    // TODO: Is this usual/logical behaviour?
    #[test]
    fn parse_list2_fst_by_position_snd_by_key_res_fst_from_position_snd_from_key() {
        let (a,) = Smargs::<(List<usize>,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::List(2)),
            ])
            .parse("x 0 -a 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.first(), Some(&0));
        assert_eq!(a.0.get(1), Some(&1));
    }

    #[test]
    fn parse_maybe_by_key_res_maybe_from_value() {
        let (a,) = Smargs::<(Result<usize>,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Maybe),
            ])
            .parse("x -a 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.unwrap(), 0);
    }

    // NOTE: Maybe "maybe" might be a bad name as the value needs to eventually
    // be something...
    #[test]
    fn parse_req_by_position_no_maybe_res_req_from_position_maybe_errors_missing() {
        let (a, b) = Smargs::<(usize, Result<usize>)>::with_definition(
            "Test program",
            [
                ("A",    vec![], Kind::Required),
                ("B", vec!["b"], Kind::Maybe),
            ])
            .parse("x 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        let b_err = b.0.unwrap_err();
        assert!(matches!(
            b_err,
            Error::Missing(Smarg { desc, ref keys, kind: Kind::Maybe, value: Value::None }) if desc == "B" && keys[0] == "b",
        ), "{}", b_err);
    }

    // This seems (too much?) like a use-case...
    #[test]
    fn parse_1st_and_3rd_req_by_pos_no_2nd_opt_res_opt_from_default() {
        let (a, b, c) = Smargs::<(usize, usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
                ("B", vec!["b"], Kind::Optional("1")),
                ("C", vec!["c"], Kind::Required),
            ])
            .parse("x 0 2".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(c, 2);
    }

    #[test]
    fn parse_help_by_key_res_errors_generated_help() {
        let err = Smargs::<()>::with_definition("Test program", [ ])
            .help_default()
            .parse("x --help".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break { err: Error::Help, help }
                if !help.is_empty(),
        ));
    }

    #[test]
    fn parse_no_1st_req_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
            ])
            .help_default()
            .parse("x --help".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            *err,
            Break { err: Error::Help, help }
                if !help.is_empty(),
        ));
    }

    #[test]
    fn parse_req_by_key_fst_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
            ])
            .help_default()
            .parse("x -a 0 --help".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break { err: Error::Help, help }
                if !help.is_empty(),
        ));
    }

    // Error/panic-conditions:

    #[test]
    fn parse_no_req_res_errors_req_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
            ])
            .parse("x".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break { err: Error::Missing(Smarg { desc, keys, kind: Kind::Required, value: Value::None }), .. } if desc == "A" && keys[0] == "a",
        ));
    }

    #[test]
    fn parse_1st_req_by_pos_2nd_opt_no_key_snd_extra_arg_res_errors_undefined_arg() {
        let err = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
                ("B", vec!["b"], Kind::Optional("1")),
            ])
            .parse("x 0 2".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            *err,
            Break { err: Error::UndefinedArgument(Arg { value: s, type_: Key::Position }), .. }
                if s == "2",
        ));
    }

    #[test]
    fn parse_multiple_reqs_by_pos_res_errors_undefined_argument() {
        let err = Smargs::<(usize, )>::with_definition(
            "Test program",
            [
                ("A", vec![], Kind::Required),
            ])
            .parse(
                "x 0 1".split(' ').map(String::from)
            )
            .unwrap_err();

        assert!(matches!(
            *err,
            Break { err: Error::UndefinedArgument(Arg { value: ref s, type_: Key::Position }), .. }
                if s == "1",
        ), "{}", err);
    }

    #[test]
    fn parse_multiple_reqs_by_key_res_errors_duplicate_value() {
        let err = Smargs::<(usize, )>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
            ])
            .parse(
                "x -a 0 -a 1".split(' ').map(String::from)
            )
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break {
                err: Error::Duplicate {
                    first: (
                        Arg { value: ref fst_k, type_: Key::Short { group_size: 1 } },
                        Value::Just(ref fst_v)
                    ),
                    extra: (
                        Arg { value: ref ext_k, type_: Key::Short { group_size: 1 } },
                        Value::Just(ref ext_v)
                    ),
                },
                ..
            } if fst_k == "a" && fst_v == "0" && ext_k == "a" && ext_v == "1",
        ), "{}", err);
    }

    #[test]
    fn parse_req_by_key_no_value_res_errors_req_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Required),
            ])
            .parse("x -a".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            *err,
            Break { err: Error::Missing(Smarg { kind: Kind::Required, .. }), .. },
        ));
    }

    #[test]
    fn parse_opt_by_key_no_value_res_errors_opt_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], Kind::Optional("0")),
            ])
            .parse("x -a".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            *err,
            Break { err: Error::Missing(Smarg { kind: Kind::Optional(_), .. }), .. },
        ));
    }

    #[test]
    fn parse_req_by_position_undefined_key_no_value_res_errors_undefined_key() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A" , vec!["a"], Kind::Required),
            ])
            .parse("x 0 -b".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break { err: Error::UndefinedKey(Arg { value: s, type_: Key::Short { group_size: 1 } }), .. } if s == "b",
        ));
    }

    #[test]
    fn parse_req_by_position_bad_value_res_errors_parsing_failed() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A" , vec!["a"], Kind::Required),
            ])
            .parse("x -1".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            *err,
            Break { err: Error::Parsing { of: Smarg { value: Value::Just(ref s), .. }, failed_with: ref boxed_err }, .. }
                if s == "-1" && boxed_err.is::<std::num::ParseIntError>(),
        ), "{}", err);
    }

    #[test]
    #[should_panic]
    fn from_init_tuple_flags_have_same_key_res_panics() {
        let _ = Smargs::<(bool, bool)>::with_definition(
            "Test program",
            [
                ("A",  vec!["a"], Kind::Flag),
                ("Aa", vec!["a"], Kind::Flag),
            ]
        );
    }
}
