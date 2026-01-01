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
    () => {
        Argument::Required | Argument::RequiredList
    };
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

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::None => "".to_owned(),
                Self::Just(x) => x.clone(),
                Self::List(xs) => xs.join(", "),
            },
        )
    }
}

pub trait FromSmarg: Sized {
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error>;
}

impl<T> FromSmarg for Vec<T>
where
    T: FromStr + fmt::Debug,
    <T as FromStr>::Err: error::Error + 'static,
{
    fn from_smarg(smarg: Smarg) -> StdResult<Self, Error> {
        let Some(values) = (match smarg.value {
            Value::None => None,
            Value::Just(x) => panic!(
                        "Type vs argument mismatch. Did you mean to define the argument {} of type {} as {} instead?",
                        {
                            let k = smarg
                            .keys
                            .iter()
                            .max()
                            .map(|x|
                                format!(
                                    "{}{} ",
                                    if x.len() > 1 { "--" } else {"-"},
                                    x
                                )
                            )
                            .unwrap_or_default();
 
                            format!("'{}{}'", k, x)
                        },
                        std::any::type_name::<Self>(),
                        std::any::type_name::<T>(),
                    ),

            Value::List(ref xs) => Some(xs.clone()),
        }) else {
            return Err(Error::Missing(smarg));
        };

        let mut results: Vec<Option<StdResult<T, _>>> = values
            .iter()
            .map(|x| Some(<T as FromStr>::from_str(x)))
            .collect();
        let mut found_error = None;
        for (i, result) in results.iter().enumerate() {
            if result.as_ref().unwrap().is_err() {
                found_error = Some(i);
                break;
            }
        }
        if let Some(i) = found_error {
            let error = results[i].take().unwrap().unwrap_err();
            Err(Error::Parsing {
                of: smarg,
                failed_with: Box::new(error),
            })
        } else {
            let values = results
                .into_iter()
                .map(|x| x.unwrap().unwrap())
                .collect::<Vec<T>>();

            Ok(values)
        }
    }
}

/// Mass-implement `FromSmarg` for all plausible std basic types.
macro_rules! fromsmarg_impl {
    ( $t:ty ) => {
        impl FromSmarg for $t {
            fn from_smarg(smarg: Smarg) -> StdResult<Self, Error> {
                match &smarg.value {
                    Value::None => Err(Error::Missing(smarg)),
                    Value::Just(x) => x.parse().map_err(|e| Error::Parsing {
                        of: smarg.clone(),
                        failed_with: Box::new(e),
                    }),
                    Value::List(xs) => panic!(
                        "Type vs argument mismatch. Did you mean to define the argument{} of type Vec<{}> as {} instead?",
                        {
                            let k = smarg
                            .keys
                            .iter()
                            .max()
                            .map(|x|
                                format!(
                                    "{}{} ",
                                    if x.len() > 1 { "--" } else {"-"},
                                    x
                                )
                            )
                            .unwrap_or_default();

                            let ys = xs
                                .iter()
                                .map(|x| format!("'{}{}'", k, x))
                                .collect::<Vec<String>>();

                            if ys.len() == 1 {
                                format!(" {}", ys[0])
                            } else {
                                format!("s {}", ys.join(", "))
                            }
                        },
                        stringify!($t),
                        stringify!($t)
                    ),
                }
            }
        }
    };
}

fromsmarg_impl!(usize);
fromsmarg_impl!(i32);
fromsmarg_impl!(String);
fromsmarg_impl!(bool);
fromsmarg_impl!(std::path::PathBuf);

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
    /// NOTE: This is here in order to support the `arguments`-macro implementing
    /// `TryFrom<Smargs<_>> for MyOutput`.
    output: PhantomData<Ts>,
}

impl<Ts> Smargs<Ts>
where
    Ts: TryFrom<Self, Error = Error>,
{
    /// Build a new `Smargs` instance from an ordered collection of `Smarg`
    /// definitions in tuple form.
    pub fn with_definition(
        desc: &'static str,
        definition: Vec<(&'static str, Vec<&'static str>, Argument)>,
    ) -> Self {
        let mut smargs = Self {
            index: 0,
            name: String::default(),
            description: desc.to_owned(),
            list: Vec::new(),
            map: HashMap::new(),
            output: PhantomData,
        };

        for (s, ks, k) in definition {
            smargs.push(Smarg {
                desc: s,
                keys: ks,
                kind: k,
                value: Value::None,
            });
        }

        // Generate some quick and short how-to reminder.
        let usage = &format!(
            "Usage: {} {}",
            smargs.name,
            smargs
                .list
                .iter()
                // Do _not_ include Help in usage list.
                .filter_map(|x| {
                    let display = x
                        .keys
                        .clone()
                        .into_iter()
                        .filter(|x| x.len() > 1)
                        .max()
                        .unwrap_or(x.desc);
                    match x.kind {
                        Argument::Help => None,
                        Argument::Required | Argument::RequiredList => {
                            Some(format!("<{}>", display))
                        }
                        Argument::Flag => Some(format!(
                            "[-{}]",
                            if display.len() > 1 {
                                format!("-{}", display)
                            } else {
                                display.to_string()
                            }
                        )),
                        Argument::OptionalList(_) | Argument::Optional(_) => {
                            Some(format!("[{}]", display))
                        }
                    }
                })
                .fold(String::new(), |mut acc, l| {
                    acc.push_str(&format!("{} ", l));
                    acc
                })
        );

        let mut short = usage.clone();

        if let Some(Smarg {
            keys,
            kind: Argument::Help,
            ..
        }) = &smargs.list.first()
        {
            short.push_str(&format!(
                "\nTry '{} {}' for more information.",
                smargs.name,
                // TODO: `keys` is not guaranteed to be something. Check for
                // keys.len() in self.push(Smarg)?
                match keys.iter().max().unwrap() {
                    s if s.len() == 1 => format!("-{}", s),
                    s => format!("--{}", s),
                },
            ));
        }

        smargs.description = format!("{}\n\n{}", smargs.description, short);

        smargs
    }

    /// Parse the argument strings into the type `Ts` according to the definition of `self` which
    /// may include using default values for some fields.
    ///
    /// Note that the name of the program/command name is assumed to be the first item in `args`.
    pub fn parse(
        mut self,
        mut args: impl DoubleEndedIterator<Item = String>,
    ) -> StdResult<Ts, Error> {
        if let Some(name) = args.next() {
            self.name = name;
        }

        let mut values = self.explicit_values(args)?;

        // Handle missing values based on kinds and defaults.
        for (i, value) in values.iter_mut().enumerate().filter(|(_, x)| x.is_none()) {
            let fillin = match self.list[i].kind {
                Argument::Optional(default) => Value::Just(default.to_owned()),
                Argument::Flag | Argument::Help => Value::Just(false.to_string()),
                required_kinds!() => {
                    return Err(Error::Missing(self.list[i].clone()));
                }
                Argument::OptionalList(ref defaults) => {
                    Value::List(defaults.iter().map(|&x| x.to_owned()).collect())
                }
            };
            value.replace(fillin);
        }

        // Update self with the resolved values.
        for (i, value) in values
            .into_iter()
            .map(|x| x.expect("not all values handled"))
            .enumerate()
        {
            self.list[i].value = value;
        }

        Ts::try_from(self)
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env(self) -> StdResult<Ts, Error> {
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
        self.push(Smarg {
            desc: "Show this help message",
            keys,
            kind: Argument::Help,
            value: Value::None,
        });

        self
    }

    /// Generate and return help messages based on `self`.
    fn get_help(&self) -> String {
        let mut long = self.description.clone();

        long.push_str("\n\nArgument descriptions:\n");
        // Find the longest Smarg-string in order to nicely line up the
        // descriptions to start from the same column.
        let (max_width, details) = self
            .list
            .iter()
            .skip(1)
            // Place the help arg last.
            .chain(self.list.first().into_iter())
            .fold(
                (0, Vec::with_capacity(self.list.len())),
                |(max_len, mut acc), x| {
                    let usage = x.to_string().replace(&format!(" - {}", x.desc), "");
                    let len = usage.len();
                    acc.push((usage, x.desc));
                    (if len > max_len { len } else { max_len }, acc)
                },
            );

        let pad_len = max_width + 5;
        for (arg_usage, arg_desc) in details {
            let pad_right = " ".repeat(pad_len);
            let row_padded = format!("  {}{}", arg_usage, pad_right);
            long.extend(row_padded.chars().take(pad_len));
            long.push_str(arg_desc);
            long.push('\n');
        }

        long
    }

    /// Find the explicitly provided values based on definition and `args`.
    ///
    /// NOTE: The amount of resulting values must be equal to the amount of
    /// definitions!
    fn explicit_values(
        &self,
        args: impl DoubleEndedIterator<Item = String>,
    ) -> StdResult<Vec<Option<Value>>, Error> {
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
                    let (fst, snd) =
                        arg.split_at(arg.bytes().take(2).take_while(|b| *b == b'-').count());
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
                        1 => Key::Short {
                            group_size: stripped_key.len(),
                        },
                        _ => Key::Long,
                    },
                }
            };

            match arg.type_ {
                Key::Position => {
                    // TODO: CHECK IMPLEMENTATION: The positioned options
                    // have lower precedence compared to the explicit
                    // key-value method.
                    // TODO: Related (maybe): Should (make sure that?) the required args be
                    // satisfied in order of definition i.e.,
                    // (Req1, List(min: 2), Req2)
                    // => [A1, A2, A3, A4, A5]
                    // => { Req1: A1, List(min: 2): [A2, A3, A5], Req2: A4 }
                    let idx = state
                        .rindex
                        .ok_or_else(|| Error::UndefinedArgument(arg.clone()))?;

                    if state.values[idx].is_none() {
                        match self.list[idx].kind {
                            Argument::Required => state.values[idx] = Some(Value::Just(arg.clone().value)),
                            Argument::RequiredList => state.values[idx] = Some(Value::List(vec![arg.clone().value])),
                            _ => panic!("Bug: Failed to normalize non-required argument as keyed and instead trying to parse as positional: \n{:?}\n{:?}", self.list[idx], state.values[idx]),
                        }
                    } else {
                        match self.list[idx].kind {
                            Argument::Required => {
                                return Err(Error::Duplicate {
                                    first: (
                                        state.history[idx].as_mut().unwrap().pop().unwrap(),
                                        state.values[idx].as_ref().unwrap().clone(),
                                    ),
                                    extra: (arg, state.values[idx].take().unwrap()),
                                });
                            }
                            Argument::RequiredList => {
                                match state.values[idx].as_mut() {
                                    Some(Value::List(ref mut xs)) => xs.push(arg.clone().value),
                                    _ => panic!("Bug: Failed to initialize list Argument as list Value"),
                                }
                            }
                            _ => panic!("Bug: Failed to normalize non-required argument as keyed and instead trying to parse as positional: \n{:?}\n{:?}", self.list[idx], state.values[idx])
                        }
                    }

                    state.next_unsatisfied_required_position(&self.list);

                    if state.history[idx].is_none() {
                        state.history[idx].replace(vec![]);
                    }
                    state.history[idx].as_mut().unwrap().push(arg);
                }
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
                }
                Key::Long | Key::Short { group_size: 1 } => {
                    // Save the handled arg and how it was got for future
                    // reference in case of errors.
                    state.resolve_keyed_value(self, arg)?;
                }
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

    /// Perform checks on new argument definition and add it to the collection
    /// or panic if checks fail.
    pub fn push(&mut self, smarg: Smarg) {
        Self::validate_key_names(&smarg.keys);

        // Get the correct index to insert (not push) into.
        let handle = if let Argument::Help = smarg.kind {
            if let Some(Smarg {
                kind: Argument::Help,
                ..
            }) = self.list.get(0)
            {
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
        const POST_START_CHARACTERS: &[u8] =
            b"-0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
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

#[derive(Debug)]
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
        let rindex = definitions
            .iter()
            .enumerate()
            .find_map(|(i, x)| (x.kind.is_required() && self.values[i].is_none()).then_some(i));
        // If all required arguments are satisfied, pass the rest to the (last) required list
        // argument.
        if !(rindex.is_none()
            && self.rindex.is_some()
            && matches!(
                definitions[self.rindex.unwrap()].kind,
                Argument::RequiredList
            ))
        {
            self.rindex = rindex;
        }
    }

    /// Select and update state based on the matched value for given key, i.e.,
    /// the thing "resolved" here is definitely a "-key [value]" type of deal.
    fn resolve_keyed_value<Ts>(&mut self, smargs: &Smargs<Ts>, arg: Arg) -> StdResult<(), Error>
    where
        Ts: TryFrom<Smargs<Ts>, Error = Error>,
    {
        let key_matched_index = *smargs
            .map
            .get(&arg.value)
            .ok_or_else(|| Error::UndefinedKey(arg.clone()))?;

        let smarg = smargs
            .list
            .get(key_matched_index)
            .expect("position not found");

        match smarg.kind {
            Argument::Help => {
                // In case help is requested in the arguments e.g.
                // in the form of `--help`, interrupt the parsing
                // here and return the more detailed help-message.
                return Err(Error::Help(smargs.get_help()));
            }
            Argument::Flag => {
                if let Some(first_val) =
                    self.values[key_matched_index].replace(Value::Just(true.to_string()))
                {
                    return Err(Error::Duplicate {
                        first: (
                            self.history[key_matched_index]
                                .as_mut()
                                .unwrap()
                                .pop()
                                .unwrap(),
                            first_val,
                        ),
                        extra: (arg, self.values[key_matched_index].take().unwrap()),
                    });
                }
                // Update history; index matches with chosen value.
                let history = vec![arg];
                assert!(
                    self.history[key_matched_index].replace(history).is_none(),
                    "should be impossible to overwrite flag's history"
                );
            }
            Argument::RequiredList | Argument::OptionalList(_) => {
                if self.values[key_matched_index].is_none() {
                    self.values[key_matched_index].replace(Value::List(vec![]));
                }

                if let Some(value) = self.stack.pop() {
                    match self.values[key_matched_index].as_mut() {
                        Some(Value::List(ref mut xs)) => xs.push(value),
                        _ => panic!("Bug: Failed to initialize list Argument as list Value"),
                    }
                } else {
                    return Err(Error::Missing(smargs.list[key_matched_index].clone()));
                }

                // Update history; index matches with chosen value.
                if self.history[key_matched_index].is_some() {
                    self.history[key_matched_index].as_mut().unwrap().push(arg);
                } else {
                    self.history[key_matched_index].replace(vec![arg]);
                }
            }
            _ => {
                if let Some(value) = self.stack.pop() {
                    if let Some(first_val) =
                        self.values[key_matched_index].replace(Value::Just(value))
                    {
                        return Err(Error::Duplicate {
                            first: (
                                self.history[key_matched_index]
                                    .as_mut()
                                    .unwrap()
                                    .pop()
                                    .unwrap(),
                                first_val,
                            ),
                            extra: (arg, self.values[key_matched_index].take().unwrap()),
                        });
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
                    return Err(Error::Missing(smarg.clone()));
                }
            }
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

/// Error type for getting and parsing the values of arguments.
#[derive(Debug)]
pub enum Error {
    /// Found an unexpected extra match for `Smarg`.
    Duplicate {
        first: (Arg, Value),
        extra: (Arg, Value),
    },
    /// Instructions were explicitly request i.e., the help-key was found. The contained message
    /// includes detailed description of the program and its arguments.
    Help(String),
    /// A matching value for `Smarg` was expected but is missing.
    Missing(Smarg),
    /// Parsing from `Value` as matched to `Smarg` failed.
    Parsing {
        of: Smarg,
        failed_with: Box<dyn error::Error>,
    },
    /// No match found for given argument.
    UndefinedArgument(Arg),
    /// No match found for given key.
    UndefinedKey(Arg),
}

/// Generate nicer error-messages to print for user.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::Duplicate { first, extra } => {
                format!(
                    "already matched {}: {} but then found {}: {}",
                    first.0, first.1, extra.0, extra.1,
                )
            }
            Self::Help(s) => s.clone(),
            Self::Missing(smarg) => format!("value missing for {}", smarg),
            Self::Parsing { of, failed_with } => {
                format!(
                    "failed to parse '{}{}' - {}",
                    of.keys
                        .iter()
                        .max()
                        .map(|x| format!(
                            "-{} ",
                            if x.len() > 1 {
                                format!("-{}", x)
                            } else {
                                x.to_string()
                            }
                        ))
                        .unwrap_or("".to_string()),
                    of.value,
                    failed_with
                )
            }
            Self::UndefinedArgument(arg) => format!("undefined argument '{}'", arg),
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
    pub kind: Argument,
    pub value: Value,
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
            Argument::Required => "<REQUIRED>".to_owned(),
            Argument::RequiredList => "[<REQUIRED>]".to_owned(),
            Argument::Optional(default) => format!("<VALUE default '{}'>", default),
            Argument::Flag | Argument::Help => "".to_owned(),
            Argument::OptionalList(defaults) => {
                format!("[<VALUE>] defaults [{}]", defaults.join(","))
            }
        };

        write!(f, "{}{} - {}", keystring, note, self.desc)
    }
}

/// Describes the argument and how it is supplied.
#[derive(Debug, Clone)]
pub enum Argument {
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
    /// A collection of some non-zero amount of arguments.
    RequiredList,
    /// A collection of zero or more amount of arguments.
    OptionalList(Vec<&'static str>),
}

impl Argument {
    /// Return whether this represents a required argument.
    fn is_required(&self) -> bool {
        matches!(self, required_kinds!())
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
tryfrom_impl!(T1, T2);
tryfrom_impl!(T1, T2, T3);
tryfrom_impl!(T1, T2, T3, T4);
tryfrom_impl!(T1, T2, T3, T4, T5);
tryfrom_impl!(T1, T2, T3, T4, T5, T6);
tryfrom_impl!(T1, T2, T3, T4, T5, T6, T7);
tryfrom_impl!(T1, T2, T3, T4, T5, T6, T7, T8);

/// # Usage
/// ```
/// let (foo, bar, baz): (usize, bool, String) = terminal_toys::smargs::arguments!(
///     "Example description",
///     (
///         "Is Foo",
///         ["f", "foo"],
///         terminal_toys::smargs::Argument::Optional("42")
///     ),
///     ("Sets Bar", ["b"], terminal_toys::smargs::Argument::Flag),
///     ("Uses Baz", [], terminal_toys::smargs::Argument::Required),
/// )
/// .parse(vec!["x", "-b", "Bazbaz"].into_iter().map(String::from))
/// .unwrap();

/// assert_eq!(foo, 42_usize);
/// assert_eq!(bar, true);
/// assert_eq!(baz, "Bazbaz".to_owned());
/// ```
///
/// # `arguments!`
/// Convenience-macro for describing your program and its expected arguments,
/// constructing a `Smargs` instance and then parsing the actual arguments.
///
/// Arguments are defined using a list of tuples `(description, keys, kind)` and
/// parsed from an `Iterator<Item = String>` into types of the (here destructured) tuple.
///
/// # Examples
/// ```
/// # fn main() -> Result<(), String> {
/// use terminal_toys::smargs::{arguments, Argument};
///
/// let args = vec![
///     "register",
///     "--no-newsletter",
///     "-a",
///     "26",
///     "-d",
///     "hatch",
///     "Matt",
///     "-n",
///     "Myman",
///     "-n",
///     "Jr",
/// ];
///
/// let (names, age, domain, no_news): (Vec<String>, usize, String, bool) = arguments!(
///     "Register for service",
///     (
///         "All portions of your full name listed",
///         ["n"],
///         Argument::RequiredList
///     ),
///     ("Your age", ["a", "age"], Argument::Required),
///     ("Email address domain", ["d"], Argument::Optional("getspam")),
///     (
///         "Opt-out from receiving newsletter",
///         ["no-newsletter"],
///         Argument::Flag
///     ),
/// )
/// .parse(args.into_iter().map(String::from))
/// .map_err(|e| e.to_string())?;
///
/// let mut newsletter_subscribers = vec![];
///
/// if age < 18 {
///     let ys = 18 - age;
///     let putdown = format!(
///         "come back in {}",
///         if ys == 1 {
///             "a year".to_owned()
///         } else {
///             format!("{} years", ys)
///         }
///     );
///     eprintln!("Failed to register: {}", putdown);
///     std::process::exit(1);
/// }
///
/// let user_email = format!("{}.{}@{}.com", names.join("."), age, domain)
///     .replace(' ', ".")
///     .to_lowercase();
///
/// let subscriber_count = newsletter_subscribers.len();
/// if !no_news {
///     newsletter_subscribers.push(&user_email);
/// }
///
/// assert_eq!(user_email, "matt.myman.jr.26@hatch.com".to_string());
/// assert_eq!(newsletter_subscribers.len(), subscriber_count);
/// # Ok(()) }
/// ```
///
/// Required arguments can be parsed based on the order in the macro's
/// definition-list. Missing, but optional, arguments use the given default
/// value.
/// ```
/// # fn main() -> Result<(), String> {
/// use terminal_toys::smargs::{arguments, Argument};
///
/// let args = vec!["register.exe", "Matt Myman", "26"];
///
/// let (names, age, domain, no_news): (Vec<String>, usize, String, bool) = arguments!(
///     "Register for service",
///     (
///         "All portions of your full name listed",
///         ["n"],
///         Argument::RequiredList
///     ),
///     ("Your age", ["a", "age"], Argument::Required),
///     ("Email address domain", ["d"], Argument::Optional("getspam")),
///     (
///         "Opt-out from receiving newsletter",
///         ["no-newsletter"],
///         Argument::Flag
///     )
/// )
/// .parse(args.into_iter().map(String::from))
/// .map_err(|e| e.to_string())?;
///
/// assert!(!no_news);
/// assert_eq!(names, vec!["Matt Myman"]);
/// assert_eq!(domain, "getspam".to_string());
/// assert_eq!(age, 26);
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! arguments {
    // Tuple-container (that is pre-impl'd).
    ( $program_desc:literal, $( ($arg_desc:literal, $keys:expr, $kind:expr) $(,)? ),+ ) => {
       {
            use terminal_toys::{
                smargs::{Smargs, Smarg, Argument, Error, Value}
            };

            let mut definition = vec![];
            $(
                definition.push((
                    $arg_desc,
                    $keys.to_vec(),
                    $kind,
                ));
            )+

            Smargs::with_definition($program_desc, definition)
        }
    };
}

pub use arguments;

#[cfg(test)]
mod tests {
    use super::{Arg, Argument, Error, Key, Smarg, Smargs, Value};

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
            vec![
                ("A", vec!["a"], Argument::Required),
                ("B", vec!["b"], Argument::Required),
            ],
        )
        .parse("x 0 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_1st_req_by_short_key_fst_res_2nd_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Required),
                ("B", vec!["b"], Argument::Required),
            ],
        )
        .parse("x -a 0 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_1st_req_by_long_key_fst_res_2nd_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["aa"], Argument::Required),
                ("B", vec!["b"], Argument::Required),
            ],
        )
        .parse("x --aa 0 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_2nd_req_by_key_fst_res_1st_req_from_position() {
        let (a, b) = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Required),
                ("B", vec!["b"], Argument::Required),
            ],
        )
        .parse("x -b 1 0".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_req_int_by_position_looks_like_key_res_req_from_position() {
        let (a,) = Smargs::<(i32,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x -1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, -1);
    }

    #[test]
    fn parse_req_string_by_key_value_looks_like_another_key_res_req_from_value() {
        let (s, a) = Smargs::<(String, usize)>::with_definition(
            "Test program",
            vec![
                ("S", vec!["s"], Argument::Required),
                ("A", vec!["a"], Argument::Optional("0")),
            ],
        )
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
            vec![("S", vec![], Argument::Required)],
        )
        .parse("x -s".split(' ').map(String::from))
        .unwrap();

        assert_eq!(s, "-s");
    }

    #[test]
    fn parse_no_opt_res_opt_from_default() {
        let (a,) = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Optional("0"))],
        )
        .parse("x".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
    }

    #[test]
    fn parse_opt_by_key_res_opt_from_value() {
        let (a,) = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Optional("1"))],
        )
        .parse("x -a 0".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
    }

    #[test]
    fn parse_no_flag_res_flag_from_false() {
        let (a,) = Smargs::<(bool,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Flag)],
        )
        .parse("x".split(' ').map(String::from))
        .unwrap();

        assert!(!a);
    }

    #[test]
    fn parse_flag_by_key_res_flag_from_true() {
        let (a,) = Smargs::<(bool,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Flag)],
        )
        .parse("x -a".split(' ').map(String::from))
        .unwrap();

        assert!(a);
    }

    #[test]
    fn parse_1st_flag_2nd_req_by_key_group_res_2nd_req_from_value() {
        let (a, b) = Smargs::<(bool, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Flag),
                ("B", vec!["b"], Argument::Required),
            ],
        )
        .parse("x -ab 1".split(' ').map(String::from))
        .unwrap();

        assert!(a);
        assert_eq!(b, 1);
    }

    #[test]
    fn parse_optlist0_no_args_res_list_empty() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec![], Argument::OptionalList(vec![]))],
        )
        .parse("x".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 0);
    }

    #[test]
    fn parse_reqlist_by_position_res_single_value_from_position() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec![], Argument::RequiredList)],
        )
        .parse("x 0".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 1);
        assert_eq!(a.first(), Some(&0));
    }

    #[test]
    fn parse_reqlist_by_two_positions_res_two_values_from_positions() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec![], Argument::RequiredList)],
        )
        .parse("x 0 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 2);
        assert_eq!(a.first(), Some(&0));
        assert_eq!(a.get(1), Some(&1));
    }

    #[test]
    fn parse_optlist2_by_key_res_list1_from_value() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::OptionalList(vec!["1", "2"]))],
        )
        .parse("x -a 0".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 1);
        assert_eq!(a.first(), Some(&0));
    }

    #[test]
    fn parse_reqlist_by_keys_res_list2_from_values() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::RequiredList)],
        )
        .parse("x -a 0 -a 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 2);
        assert_eq!(a.first(), Some(&0));
        assert_eq!(a.get(1), Some(&1));
    }

    // TODO: Is this usual/logical behaviour?
    #[test]
    fn parse_reqlist_fst_by_position_snd_by_key_res_fst_from_position_snd_from_key() {
        let (a,) = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::RequiredList)],
        )
        .parse("x 0 -a 1".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a.len(), 2);
        assert_eq!(a.first(), Some(&0));
        assert_eq!(a.get(1), Some(&1));
    }

    #[test]
    fn parse_reqlist_without_args_res_errors_req_arg_missing_value() {
        let err = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::RequiredList)],
        )
        .parse("x".split(' ').map(String::from))
        .unwrap_err();

        let Error::Missing(ref smarg) = err else {
            panic!("Expected err to match Error::Missing");
        };
        assert!(
            matches!(
                smarg,
                Smarg {
                    kind: Argument::RequiredList,
                    value: Value::None,
                    ..
                }
            ),
            "{:?}",
            err
        );
    }

    #[test]
    fn parse_1st_and_3rd_req_by_pos_no_2nd_opt_res_opt_from_default() {
        let (a, b, c) = Smargs::<(usize, usize, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Required),
                ("B", vec!["b"], Argument::Optional("1")),
                ("C", vec!["c"], Argument::Required),
            ],
        )
        .parse("x 0 2".split(' ').map(String::from))
        .unwrap();

        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(c, 2);
    }

    #[test]
    fn parse_help_by_key_res_errors_generated_help() {
        let err = Smargs::<()>::with_definition("Test program", vec![])
            .help_default()
            .parse("x --help".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(err, Error::Help(_),));
    }

    #[test]
    fn parse_no_1st_req_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .help_default()
        .parse("x --help".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(err, Error::Help(_)));
    }

    #[test]
    fn parse_req_by_key_fst_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .help_default()
        .parse("x -a 0 --help".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(err, Error::Help(_)));
    }

    #[test]
    fn parse_no_req_res_errors_req_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::Missing(Smarg {
                kind: Argument::Required,
                value: Value::None,
                ..
            })
        ));
    }

    #[test]
    fn parse_1st_req_by_pos_2nd_opt_no_key_snd_extra_arg_res_errors_undefined_arg() {
        let err = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Required),
                ("B", vec!["b"], Argument::Optional("1")),
            ],
        )
        .parse("x 0 2".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::UndefinedArgument(Arg {
                type_: Key::Position,
                ..
            })
        ));
    }

    #[test]
    fn parse_multiple_reqs_by_pos_res_errors_undefined_argument() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec![], Argument::Required)],
        )
        .parse("x 0 1".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::UndefinedArgument(Arg {
                type_: Key::Position,
                ..
            })
        ));
    }

    #[test]
    fn parse_multiple_reqs_by_key_res_errors_duplicate_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x -a 0 -a 1".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::Duplicate {
                first: (
                    Arg {
                        type_: Key::Short { group_size: 1 },
                        ..
                    },
                    Value::Just(_)
                ),
                extra: (
                    Arg {
                        type_: Key::Short { group_size: 1 },
                        ..
                    },
                    Value::Just(_)
                ),
            },
        ));
    }

    #[test]
    fn parse_req_by_key_no_value_res_errors_req_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x -a".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::Missing(Smarg {
                kind: Argument::Required,
                ..
            }),
        ));
    }

    #[test]
    fn parse_opt_by_key_no_value_res_errors_opt_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Optional("0"))],
        )
        .parse("x -a".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::Missing(Smarg {
                kind: Argument::Optional(_),
                ..
            }),
        ));
    }

    #[test]
    fn parse_req_by_position_undefined_key_no_value_res_errors_undefined_key() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x 0 -b".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::UndefinedKey(Arg {
                type_: Key::Short { group_size: 1 },
                ..
            })
        ));
    }

    #[test]
    fn parse_req_by_position_bad_value_res_errors_parsing_failed() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x -1".split(' ').map(String::from))
        .unwrap_err();

        assert!(matches!(
            err,
            Error::Parsing {
                of: Smarg {
                    value: Value::Just(_),
                    ..
                },
                ..
            }
        ));
    }

    #[test]
    #[should_panic]
    fn from_init_tuple_flags_have_same_key_res_panics() {
        let _ = Smargs::<(bool, bool)>::with_definition(
            "Test program",
            vec![
                ("A", vec!["a"], Argument::Flag),
                ("Aa", vec!["a"], Argument::Flag),
            ],
        );
    }

    /// List vs. single value typing will result in runtime error, which -- considering we're
    /// parsing program arguments -- would likely be caught early in the execution and testing.
    ///
    /// NOTE that in order to raise the chances of catching the logic error __panicking__ is
    /// preferrable, not returning an error.
    #[test]
    #[should_panic]
    fn parse_single_type_as_list_by_position_res_panics() {
        // Typing as a single value by accident.
        let _ = Smargs::<(usize,)>::with_definition(
            "Test program",
            // Defining as list argument.
            vec![("A", vec![], Argument::RequiredList)],
        )
        .parse("x 0".split(' ').map(String::from));
    }

    #[test]
    #[should_panic]
    fn parse_list_type_as_single_by_position_res_panics() {
        let _ = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec![], Argument::Required)],
        )
        .parse("x 0".split(' ').map(String::from));
    }

    #[test]
    #[should_panic]
    fn parse_single_type_as_list_by_key_res_panics() {
        let _ = Smargs::<(usize,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::RequiredList)],
        )
        .parse("x -a 0".split(' ').map(String::from));
    }

    #[test]
    #[should_panic]
    fn parse_list_type_as_single_by_key_res_panics() {
        let _ = Smargs::<(Vec<usize>,)>::with_definition(
            "Test program",
            vec![("A", vec!["a"], Argument::Required)],
        )
        .parse("x -a 0".split(' ').map(String::from));
    }
}
