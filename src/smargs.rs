use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::fmt::Display;
use std::iter::{self, FromIterator};

use std::marker::PhantomData;


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
    /// Mapping of positions to argument definitions.
    list: Vec<Smarg>,
    /// Mapping of keys to to positions.
    map: HashMap<String, usize>,
    /// Made-up field required for storing the output type `Ts`.
    output: PhantomData<Ts>,
    /// Field where the given arguments are stored for parsing later.
    values: Vec<Vec<String>>,
}

impl<Ts> Smargs<Ts>
where
    Ts: TryFrom<Self, Error = Error>,
{
    /// Build a new `Smargs` instance from an ordered collection of `Smarg`
    /// definitions in tuple form.
    pub fn with_definition<const N: usize>(
        desc: &'static str,
        definition: [(&'static str, Vec<&'static str>, SmargKind); N]
    ) -> Self {
        let mut smargs = Smargs::new(desc);
        for (s, ks, k) in definition {
            smargs.push(Smarg { desc: s, keys: ks, kind: k});
        }
        smargs
    }

    /// Parse the argument strings into the type `Ts` according to the
    /// definition of `self` which may include using default values for some
    /// fields.
    /// 
    /// Note that the name of the program/command is assumed to be the first
    /// item in `args`.
    pub fn parse(mut self, mut args: impl Iterator<Item = String>) -> Result<Ts, Break>
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
            value.replace(
                match self.list[i].kind {
                    SmargKind::Optional(default) => vec![default.to_owned()],
                    SmargKind::Flag | SmargKind::Help => vec![false.to_string()],
                    SmargKind::List(0) => vec![],
                    // TODO: A macro that basically expands to Self::is_required
                    // would be gooder here.
                    SmargKind::List(_) | SmargKind::Required => {
                        let expected_count = self.list.iter().filter(|x| Self::is_required(x)).count();
                        return Err(help.short_break(Error::MissingRequired { expected_count }))
                    },
                    // TODO: Is this right?
                    SmargKind::Maybe => vec![],
                }
            );
        }

        // HACK: Concat items with a RARE delimiter to support parsing a List
        // from string.
        for xs in values.iter_mut() {
            let single_string = xs.take().unwrap().join(",");
            xs.replace(vec![single_string]);
        }

        // Update self with the resolved values.
        self.values = values.into_iter().map(|x| x.expect("not all values handled")).collect();

        Ts::try_from(self).map_err(|err| help.short_break(err))
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env(self) -> Result<Ts, Break> {
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
        self.push(Smarg { desc: "Show this help message", keys, kind: SmargKind::Help });

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
                .filter_map(|x| (!matches!(x.kind, SmargKind::Help)).then_some(x.kind.to_string()))
                .zip(iter::repeat(' '))
                .fold(
                    String::new(),
                    |mut acc, (l, r)| { acc.push_str(&l); acc.push(r); acc }
                )
        );

        let mut short = usage.clone();
        if let Smarg { keys, kind: SmargKind::Help, .. } = &self.list[0] {
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
        args: impl Iterator<Item = String>,
        help: &Help
    ) -> Result<Vec<Option<Vec<String>>>, Break> {
        // TODO: A stack would work just as well (i.e., refactor to use Vec
        // instead -> avoids confusion as to why exactly use VecDeque).
        let mut args = VecDeque::from_iter(args);

        // Put the values encountered into their specified indices.
        // Items are Vec<String> in order to support the List-variant
        // (non-Lists will contain only 1 element).

        let mut values = vec![None; self.list.len()];
        let mut positioned_index = self.list.iter().position(Self::is_required);
        let next_unsatisfied_required_position = |valuesb: &Vec<Option<_>>|
                self.list
                .iter()
                .enumerate()
                .find_map(|(i, x)|
                    (Self::is_required(x) && valuesb[i].is_none()).then_some(i)
                );
        while let Some(arg) = args.pop_front() {
            // Remove the cli-syntax off of keys and normalize the
            // multi-character groups.

            // Assume prefix length is max 2.
            // Invalid keys like ones with >2 prefixed dashes will be catched
            // when querying from the key set validated at definition time.
            let (arg, arg_type) = {
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
                (
                    // NOTE: 'arg' is redefined as not having the prefixed
                    // dashes.
                    stripped_key.to_owned(),
                    match prefix_len {
                        // Poor man's enum.
                        0 => "value",
                        1 => "short",
                        _ => "long",
                    }
                )
            };
            match arg_type {
                "value" => {
                    // TODO: CHECK IMPLEMENTATION: The positioned options
                    // have lower precedence compared to the explicit
                    // key-value method.
                    let idx = positioned_index
                        .ok_or_else(|| help.short_break(Error::UndefinedArgument(arg.clone())))?;
                    if values[idx].is_none() {
                        values[idx].replace(vec![arg]);
                        positioned_index = next_unsatisfied_required_position(&values);
                    } else {
                        panic!(
                            "tried to replace explicitly specified argument '{}' == '{}' with '{}'",
                            self.list[idx], values[idx].as_ref().unwrap()[0], arg,
                        );
                    }
                },
                "short" if arg.len() > 1 => {
                    // Replace the args-queue's front with the "normalized"
                    // multi-character group (which consist of multiple flags +
                    // possibly a key at the end
                    // i.e., "-abk <value>" => "-a -b -k <value>").
                    let keys = arg.chars().map(|c| format!("-{}", c)).enumerate();
                    // NOTE: There did not seem to be a reverse method for
                    // VecDequeue::append e.g., "prepend" or smth.
                    // Insert the keys "in order" to the front i.e.,
                    // indx:  0, 1,..     0, 1, 2,..     0, 1, 2, 3,..
                    // elem: -a:-_:xs -> -a:-b:-_:xs -> -a:-b:-k:-_:xs -> ...
                    for (i, new_arg) in keys {
                        args.insert(i, new_arg);
                    }
                    // Let the main-loop handle these added "new" keys normally.
                },
                /* "long" | "short" if arg.len() == 1 */ _ => {
                    let key_matched_index = *self.map
                        .get(&arg)
                        .ok_or(help.short_break(Error::UndefinedKey(arg.clone())))?;
                    let smarg = self.list.get(key_matched_index).expect("position not found");

                    match smarg.kind {
                        SmargKind::Help => {
                            // In case help is requested in the arguments e.g.
                            // in the form of `--help`, interrupt the parsing
                            // here and return the more detailed help-message.
                            return Err(help.long_break(Error::Help))
                        },
                        SmargKind::Flag => {
                            if values[key_matched_index].replace(vec![true.to_string()]).is_some() {
                                // TODO: Wouldn't this more specifically be
                                // "Error::DuplicateFlag(arg)"?
                                panic!(
                                    "tried to replace already specified argument '{}' with '{}'",
                                    smarg, arg,
                                );
                            }
                        },
                        SmargKind::List(_min) => {
                            // This case here is why `values` contains Vec<String>'s.
                            if let Some(list) = values[key_matched_index].as_mut() {
                                if let Some(value) = args.pop_front() {
                                    list.push(value);
                                } else {
                                    return Err(help.short_break(
                                        Error::Smarg {
                                            printable_arg: smarg.to_string(),
                                            kind: ErrorKind::MissingValue,
                                        }
                                    ))
                                }
                            }
                        },
                        _ => {
                            if let Some(value) = args.pop_front() {
                                if values[key_matched_index].replace(vec![value]).is_some() {
                                    return Err(help.short_break(
                                        Error::Smarg {
                                            printable_arg: smarg.to_string(),
                                            kind: ErrorKind::Duplicate,
                                    }));
                                } else {
                                    // Update the position because this
                                    // required was received based on
                                    // key-value.
                                    positioned_index = next_unsatisfied_required_position(&values);
                                }
                            } else {
                                return Err(help.short_break(
                                    Error::Smarg { printable_arg: smarg.to_string(),
                                         kind: ErrorKind::MissingValue }))
                            }
                        }                       
                    }
                }
            }
        }

        Ok(values)
    }

    /// NOTE: Not to be called by user directly; instead use the `From`
    /// implementations or `smargs` macro!
    /// 
    /// Parse into the type `T` the next value of arg defined in running order.
    pub fn parse_next<T>(&mut self) -> Result<T, Error>
    where
        T: FromStr,
    {
        // TODO This seems unnecessarily complex...
        let index = self.index;
        let value = match self
            .values
            .get(index)
            .take()
            .ok_or(Error::MissingRequired {
                expected_count: self
                    .list
                    .iter()
                    .filter(|x| matches!(x, Smarg { kind: SmargKind::Required, ..}))
                    .count()
            })
        {
            // Manual unwrap-exiting because std::ops::Try is unstable.
            Ok(x) => x,
            Err(e) => return Err(e),
        };

        let return_value = <T as FromStr>::from_str(&value[0]).map_err(|e| e.into());

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
            values: Vec::new(),
        }
    }

    /// Perform checks on new argument definition and add it to the collection
    /// or panic if checks fail.
    pub fn push(&mut self, smarg: Smarg) {
        Self::validate_key_names(&smarg.keys);

        // Get the correct index to insert (not push) into.
        let handle = if let SmargKind::Help = smarg.kind {
            if let Some(Smarg { kind: SmargKind::Help, .. }) = self.list.get(0) {
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
                panic!("Duplicate key defined: '{}'", key);
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

    fn validate_key_name(key: &str) -> Result<(), String> {
        const START_CHARACTERS: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const POST_START_CHARACTERS: &[u8] = b"-0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        if key.is_empty() {
            return Err(format!("a key must not be empty"));
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

    /// Return if the definition represents a required argument.
    fn is_required(smarg: &Smarg) -> bool {
        matches!(smarg.kind, SmargKind::Required | SmargKind::List(1..))
    }
}

/// More elaborative explanation for an error.
#[derive(Debug)]
pub enum ErrorKind {
    Duplicate,
    MissingValue,
    // TODO: Could implementing From<FromStr::Err> for smargs::Error make
    // handling this case easier? See:
    // https://doc.rust-lang.org/std/convert/trait.From.html#examples
    Parsing(&'static str, String, Box<dyn error::Error>),
}

/// Struct containing short and long descriptions of a program and its
/// arguments. The `short` message is preferred during generic error conditions
/// and `long` when explicitly requesting for help.
#[derive(Debug)]
struct Help { short: String, long: String }

impl Help {
    fn short_break(&self, err: Error) -> Break {
        Break { err, help: self.short.clone() }
    }

    fn long_break(&self, err: Error) -> Break {
        Break { err, help: self.long.clone() }
    }
}

/// The reason for interruption or "break" when parsing based on `Smargs` can
/// either be because an error occurred or because of an explicit help-request
/// to describe the program by its arguments.
/// TODO: `impl ops::Try for Break`?
#[derive(Debug)]
pub struct Break { pub err: Error, pub help: String }

/// Error type for getting and parsing the values of arguments.
#[derive(Debug)]
pub enum Error {
    /// Represents explicit help request i.e., the help-key was found.
    Help,
    MissingRequired { expected_count: usize },
    UndefinedArgument(String),
    UndefinedKey(String),
    Smarg { printable_arg: String, kind: ErrorKind },
    /// Wrap a user-defined error.
    Dummy(Box<dyn error::Error>),
}

impl Error {
    /// Wrap the `error` in `Self::Dummy` by boxing it.
    pub fn dummy<E: error::Error + 'static>(error: E) -> Self {
        Self::Dummy(Box::new(error))
    }
}

/// Select between generic or argument-specific error messages.
impl fmt::Display for Break {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f, "Parsing interrupted because {}",
            match self.err {
                // Argument-specific error.
                Error::Smarg { .. } => self.err.to_string(),
                // Generic error.
                _ => format!("{}\n\n{}", self.err, self.help),
            }
        )
    }
}

/// Generate nicer error-messages to print for user.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::Help => "Help".to_owned(),
            Self::MissingRequired { expected_count: expected } => {
                // TODO What about "required _at least_ of X" in case of (future)
                // list-type arguments?
                format!("Not enough arguments (expected {}).", expected)
            },
            Self::UndefinedArgument(arg) => {
                format!("Extra argument '{}'", arg)
            },
            // TODO Suggest similar existing arguments in case of user typo.
            Self::UndefinedKey(key) => format!("Option '{}' does not exist", key),
            Self::Smarg { printable_arg, kind } => format!(
                "{}. Usage: {}",
                match kind {
                    // TODO Inform how many times the argument was illegally repeated.
                    ErrorKind::Duplicate => "Too many entries of this argument".to_owned(),
                    // TODO Elaborate on the type of value.
                    ErrorKind::MissingValue => "Option key used but missing the value".to_owned(),
                    ErrorKind::Parsing(tname, input, e) => format!(
                        "Failed to parse the type {} from input '{}': {}",
                        tname, input, e
                    ),
                },
                printable_arg
            ),
            Self::Dummy(msg) => format!("{}, baka.", msg),
        };
        write!(f, "{}", msg)
    }
}

/// Contains information about a single _definition_ (or declaration?) of an
/// argument i.e., this is not an abstraction for the concrete things that a
/// user would submit as arguments for a program.
#[derive(Debug)]
pub struct Smarg {
    pub desc: &'static str,
    pub keys: Vec<&'static str>,
    pub kind: SmargKind,
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
            SmargKind::Required => "<required value>".to_owned(),
            SmargKind::Optional(default) => format!("<value OR '{}'>", default),
            SmargKind::Flag | SmargKind::Help => "Negated by default".to_owned(),
            SmargKind::List(n) => format!("List of {} or more values", n),
            SmargKind::Maybe => "<value OR ??>".to_owned(),
        };

        write!(f, "{}{}", keystring, note)
    }
}

/// Describes the argument and how it is supplied.
#[derive(Debug, Clone)]
pub enum SmargKind {
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

impl fmt::Display for SmargKind {
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
pub struct SmargsResult<T>(pub Result<T, Error>);

/// "Newtrait" that allows implementing `FromStr` for `MyResult<T: FromStr>`
/// that actually calls the method from `<T as FromStr>`.
pub trait FromStr {
    type Err: Into<Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> where Self: Sized;
}

/// Generic implementation for all types that implement `std::str::FromStr`.
impl<T> FromStr for T
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Into<Error>,
{
    type Err = <T as std::str::FromStr>::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <Self as std::str::FromStr>::from_str(s)
    }
}

/// Generic implementation for all types that implement `std::str::FromStr` but
/// into the Result-wrapper for returning errors from parsing specific arguments.
impl<T> FromStr for SmargsResult<T>
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Into<Error>,
{
    type Err = std::convert::Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <T as FromStr>::from_str(s)
            .map(|x| SmargsResult(Ok(x)))
            // Wrap the error inside.
            .or_else(|e| Ok(SmargsResult(Err(e.into()))))
    }
}

impl<T> FromStr for List<T>
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: Into<Error>,
{
    type Err = <T as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> where Self: Sized {
        // TODO: Improve this HACK by, instead of using ',', searching for a
        // character not present in any of the original strings. This would
        // become a problem only when the __whole UTF-8 space__ is used in
        // arguments.
        let mut xs = Vec::new();
        for x in s.split(',') {
            xs.push(<T as FromStr>::from_str(x)?);
        }
        Ok(List(xs))
    }

}

/// This generic implementation prevents implementing `std::error::Error` for
/// `smargs::Error`, but probably a a smaller price to pay than having to
/// manually add support for each.
impl<E: error::Error + 'static> From<E> for Error {
    fn from(value: E) -> Self {
        Self::dummy(value)
    }
}

/// This implementation supports adding a help message to an argumentless
/// program.
impl TryFrom<Smargs<Self>> for () {
    type Error = Error;
    fn try_from(_: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok(())
    }
}

impl<T1> TryFrom<Smargs<Self>> for (T1,)
where
    T1: FromStr,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((smargs.parse_next()?,))
    }
}

impl<T1, T2> TryFrom<Smargs<Self>> for (T1, T2)
where
    T1: FromStr,
    T2: FromStr,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_next()?,
            smargs.parse_next()?
        ))
    }
}

impl<T1, T2, T3> TryFrom<Smargs<Self>> for (T1, T2, T3)
where
    T1: FromStr,
    T2: FromStr,
    T3: FromStr,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_next()?,
            smargs.parse_next()?,
            smargs.parse_next()?,
        ))
    }
}


#[cfg(test)]
mod tests {
    use super::{Break, Error, ErrorKind, Smargs, SmargKind, List, SmargsResult};

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
                ("A", vec!["a"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Required),
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
                ("A", vec!["a"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Required),
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
                ("A", vec!["aa"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Required),
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
                ("A", vec!["a"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Required),
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
                ("A" , vec!["a"], SmargKind::Required),
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
                ("S" , vec!["s"], SmargKind::Required),
                ("A" , vec!["a"], SmargKind::Optional("0")),
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
                ("S" , vec![], SmargKind::Required),
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
                ("A", vec!["a"], SmargKind::Optional("0")),
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
                ("A", vec!["a"], SmargKind::Optional("1")),
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
                ("A", vec!["a"], SmargKind::Flag),
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
                ("A", vec!["a"], SmargKind::Flag),
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
                ("A", vec!["a"], SmargKind::Flag),
                ("B", vec!["b"], SmargKind::Required),
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
                ("A", vec!["a"], SmargKind::List(2)),
            ])
            .parse("x -a 0 -a 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.get(0), Some(&0));
        assert_eq!(a.0.get(1), Some(&1));
    }

    // TODO: Is this usual/logical behaviour?
    #[test]
    fn parse_list2_fst_by_position_snd_by_key_res_fst_from_position_snd_from_key() {
        let (a,) = Smargs::<(List<usize>,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::List(2)),
            ])
            .parse("x 0 -a 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.get(0), Some(&0));
        assert_eq!(a.0.get(1), Some(&1));
    }

    #[test]
    fn parse_maybe_by_key_res_maybe_from_value() {
        let (a,) = Smargs::<(SmargsResult<usize>,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Maybe),
            ])
            .parse("x -a 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.0.unwrap(), 0);
    }

    // NOTE: Maybe "maybe" might be a bad name as the value needs to eventually
    // be something...
    #[test]
    fn parse_req_by_position_no_maybe_res_req_from_position_maybe_errors_missing_req() {
        let (a, b) = Smargs::<(usize, SmargsResult<usize>,)>::with_definition(
            "Test program",
            [
                ("A",    vec![], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Maybe),
            ])
            .parse("x 0".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a, 0);
        assert!(matches!(
            b.0.unwrap_err(),
            Error::Dummy(boxed_err)
                if boxed_err.is::<std::num::ParseIntError>(),
        ));
    }

    // This seems (too much?) like a use-case...
    #[test]
    fn parse_1st_and_3rd_req_by_pos_no_2nd_opt_res_opt_from_default() {
        let (a, b, c) = Smargs::<(usize, usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Optional("1")),
                ("C", vec!["c"], SmargKind::Required),
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
            err,
            Break { err: Error::Help, help }
                if !help.is_empty(),
        ));
    }

    #[test]
    fn parse_no_1st_req_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ])
            .help_default()
            .parse("x --help".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            err,
            Break { err: Error::Help, ref help }
                if !help.is_empty(),
        ), "{:?}", err);
    }

    #[test]
    fn parse_req_by_key_fst_help_by_key_res_errors_generated_help() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ])
            .help_default()
            .parse("x -a 0 --help".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break { err: Error::Help, help }
                if !help.is_empty(),
        ));
    }

    // Error/panic-conditions:

    #[test]
    fn parse_no_req_res_errors_missing_req() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ])
            .parse("x".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break { err: Error::MissingRequired { expected_count: 1 }, .. },
        ));
    }

    #[test]
    fn parse_1st_req_by_pos_2nd_opt_no_key_snd_extra_arg_res_errors_undefined_arg() {
        let err = Smargs::<(usize, usize)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
                ("B", vec!["b"], SmargKind::Optional("1")),
            ])
            .parse("x 0 2".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            err,
            Break { err: Error::UndefinedArgument(s), .. } if s == "2",
        ));
    }

    #[test]
    fn parse_multiple_reqs_by_key_res_errors_duplicate_value() {
        let err = Smargs::<(usize, )>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ])
            .parse(
                "x -a 0 -a 1".split(' ').map(String::from)
            )
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break { err: Error::Smarg { .. }, .. }
        ));
        assert!(matches!(
            match err.err { Error::Smarg { kind, .. } => kind, _ => panic!("impossible"), },
            ErrorKind::Duplicate,
        ));
    }

    #[test]
    fn parse_req_by_key_no_value_res_errors_arg_missing_value() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ])
            .parse("x -a".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break{err: Error::Smarg { .. }, .. },
        ));
        assert!(matches!(
            match err.err { Error::Smarg { kind, .. } => kind, _ => panic!("impossible"), },
            ErrorKind::MissingValue,
        ));
    }

    #[test]
    fn parse_req_by_position_undefined_key_no_value_res_errors_undefined_key() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Required),
            ])
            .parse("x 0 -b".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break { .. },
        ));
        assert_eq!(
            match err.err { Error::UndefinedKey(x) => x, _ => panic!("impossible"), },
            "b".to_string(),
        );
    }

    #[test]
    fn parse_req_by_position_bad_value_res_errors_parsing_failed() {
        let err = Smargs::<(usize,)>::with_definition(
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Required),
            ])
            .parse("x -1".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Break{err: Error::Dummy(_), .. },
        ));
        assert!(matches!(
            err.err,
            Error::Dummy(boxed_err)
                if boxed_err.is::<std::num::ParseIntError>(),
        ));
    }

    #[test]
    #[should_panic]
    fn from_init_tuple_flags_have_same_key_res_panics() {
        let _ = Smargs::<(bool, bool)>::with_definition(
            "Test program",
            [
                ("A",  vec!["a"], SmargKind::Flag),
                ("Aa", vec!["a"], SmargKind::Flag),
            ]
        );
    }
}
