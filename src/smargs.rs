use std::collections::HashMap;
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::fmt::Display;

use std::marker::PhantomData;
use std::str::FromStr;


/// Wrapper to `Vec` that allows support for multiple values per one argument
/// definition.
/// TODO: Make this always contain a minimum number of items to work together
/// with the SmargKind::List(min).
pub struct List<T: FromStr>(Vec<T>);

impl<T: FromStr> List<T> {
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }
}

impl<T> FromStr for List<T>
where
    T: FromStr,
    <T as FromStr>::Err: error::Error + 'static,
{
    type Err = <T as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
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

/// SiMpler thAn wRiting it once aGain Surely :)
///
/// # Examples:
/// Program arguments will be defined using the builder:
/// ```
/// let builder = terminal_toys::smargs!(
///     "Register for service",
///     ("Opt-out from receiving newsletter", vec!["no-newsletter"], bool),
///     ("Your full name",                    vec![],                String),
///     ("Email address domain",              vec!["d"],             String,    "getspam"),
///     ("Your age",                          vec!["a", "age"],      usize)
/// );
/// ```
/// The different arguments will be recognized from the command line syntax and
/// parsed into usable types:
/// ```
/// # fn main() -> Result<(), String> {
/// # let builder = terminal_toys::smargs!(
/// #     "Register for service",
/// #     ("Opt-out from receiving newsletter", vec!["no-newsletter"], bool),
/// #     ("Your full name",                    vec![],                String),
/// #     ("Email address domain",              vec!["d"],             String,    "getspam"),
/// #     ("Your age",                          vec!["a", "age"],      usize)
/// # );
/// # let mut newsletter_subscribers = vec![];
/// let args = vec!["register.exe", "--no-newsletter", "-a", "26", "-d", "hatch", "Matt Myman"].into_iter().map(String::from);
///
/// let (no_news, name, domain, age)
///     : (bool, String, String, usize)
///     = builder.parse(args).map_err(|e| e.to_string())?;
///
/// if age < 18 {
///     let ys = 18 - age;
///     let putdown = format!(
///         "come back in {}",
///          if ys == 1 { "a year".to_owned() } else { format!("{} years", ys) }
///     );
///     eprintln!("Failed to register: {}", putdown);
///     std::process::exit(1);
/// }
///
/// let user_email = format!("{}.{}@{}.com", name, age, domain).replace(' ', ".").to_lowercase();
///
/// let subscriber_count = newsletter_subscribers.len();
/// if !no_news {
///     newsletter_subscribers.push(&user_email);
/// }
///
/// assert_eq!(user_email, "matt.myman.26@hatch.com".to_string());
/// assert_eq!(newsletter_subscribers.len(), subscriber_count);
/// # Ok(()) }
/// ```
/// Required arguments can also be passed based on position defined by the
/// calling order of the builder-methods. Missing but optional arguments use the
/// given default value.
/// ```
/// # let builder = terminal_toys::smargs!(
/// #     "Register for service",
/// #     ("Opt-out from receiving newsletter", vec!["no-newsletter"], bool),
/// #     ("Your full name",                    vec![],                String),
/// #     ("Email address domain",              vec!["d"],             String,    "getspam"),
/// #     ("Your age",                          vec!["a", "age"],      usize)
/// # );
/// let args = vec!["register.exe", "Matt Myman", "26"].into_iter().map(String::from);
///
/// let (no_news, name, domain, age) : (bool, String, String, usize) = builder.parse(args).unwrap();
///
/// assert!(!no_news);
/// assert_eq!(name, "Matt Myman".to_string());
/// assert_eq!(domain, "getspam".to_string());
/// assert_eq!(age, 26);
/// ```
#[derive(Debug)]
pub struct Smargs<Ts> {
    /// Mapping of positions to argument definitions.
    list: Vec<Smarg>,
    /// Mapping of keys to to positions.
    map: HashMap<String, usize>,
    /// Made-up field required for storing the output type `Ts`.
    output: PhantomData<Ts>,
    /// Field where the given arguments are stored for parsing later.
    values: Vec<Option<Vec<String>>>,
}

impl<Ts: TryFrom<Self, Error = Error>> Smargs<Ts> {
    /// Parse the argument strings into the type `T` according to the
    /// definition of `self` which may include default values for some.
    pub fn parse(mut self, mut args: impl Iterator<Item = String>) -> Result<Ts, Error>
    {
        // Ignore the executable. TODO Allow saving exe with a .exe() -method?
        // TODO Save it anyway for error/help messages?
        args.next();

        self.values = {
            // Put the values encountered into their specified indices.
            // Items are Vec<String> in order to support the List-variant
            // (non-Lists only get 1 element).
            let mut values: Vec<Option<Vec<String>>> = vec![None; self.list.len()];
            let mut positioned_index = self.list.iter().position(Self::is_required);
            while let Some(arg) = args.next() {
                // Remove the cli-syntax off of keys and normalize the
                // multi-character groups.

                // Assume prefix length is max 2.
                // The validation of keys will handle invalid keys like ones
                // with >2 prefixed dashes.
                let arg_type = match arg.chars().take(2).take_while(|c| *c == '-').count() {
                    // Poor man's enum.
                    0 => "value",
                    1 => "short",
                    _ => "long",
                };
                match arg_type {
                    "value" => {
                        // TODO: CHECK IMPLEMENTATION: The positioned options
                        // have lower precedence compared to the explicit
                        // key-value method.
                        let idx = positioned_index.expect("remaining arguments are not required");
                        if values[idx].is_none() {
                            values[idx].replace(vec![arg]);
                            positioned_index = self.list.iter().enumerate().skip(idx + 1).find_map(|(i, x)| Self::is_required(x).then_some(i));
                        } else {
                            panic!(
                                "tried to replace explicitly specified argument '{}' == '{}' with '{}'",
                                self.list[idx], values[idx].as_ref().unwrap()[0], arg,
                            );
                        }
                    },
                    "short" => {
                        // Loop in order to handle multi-character group (which
                        // consist of multiple flags + possibly a key at the end
                        // i.e., "-abk <value>" => "-a -b -k <value>").
                        let mut keys = arg.chars().skip(1);
                        while let Some(key) = keys.next().map(String::from) {
                            let key_matched_index = *self.map.get(&key).ok_or(Error::UndefinedKey(key))?;
                            let smarg = self.list.get(key_matched_index).expect("position not found");
                            match smarg.kind {
                                SmargKind::Flag => {
                                    if values[key_matched_index].replace(vec![true.to_string()]).is_some() {
                                        panic!(
                                            "tried to replace already specified argument '{}' with '{}'",
                                            smarg, arg,
                                        );
                                    }
                                },
                                SmargKind::List(_min) => {
                                    // This case here is why `values` contains Vec<String>'s.
                                    if let Some(list) = values[key_matched_index].as_mut() {
                                        if let Some(value) = args.next() {
                                            list.push(value);
                                        } else {
                                            return Err(Error::Smarg { printable_arg: smarg.to_string(), kind: ErrorKind::MissingValue });
                                        }
                                    }
                                },
                                _ => {
                                    if let Some(_key) = keys.next() {
                                        panic!("expected value but got key in group");
                                    } else if let Some(value) = args.next() {
                                        if values[key_matched_index].replace(vec![value]).is_some() {
                                            return Err(Error::Smarg { printable_arg: smarg.to_string(), kind: ErrorKind::Duplicate });
                                        }
                                    } else {
                                        return Err(Error::Smarg { printable_arg: smarg.to_string(), kind: ErrorKind::MissingValue });
                                    }
                                }
                            }
                        }
                    },
                    /* "long" */ _ => {
                        let key = arg.chars().skip(2).collect();
                        let key_matched_index = *self.map.get(&key).ok_or(Error::UndefinedKey(key))?;
                        let smarg = self.list.get(key_matched_index).expect("position not found");

                        match smarg.kind {
                            SmargKind::Flag => {
                                if values[key_matched_index].replace(vec![true.to_string()]).is_some() {
                                    panic!(
                                        "tried to replace already specified argument '{}' with '{}'",
                                        smarg, arg,
                                    );
                                }
                            },
                            SmargKind::List(_min) => {
                                // This case here is why `values` contains Vec<String>'s.
                                if let Some(list) = values[key_matched_index].as_mut() {
                                    if let Some(value) = args.next() {
                                        list.push(value);
                                    } else {
                                        return Err(Error::Smarg { printable_arg: smarg.to_string(), kind: ErrorKind::MissingValue });
                                    }
                                }
                            },
                            _ => {
                                if let Some(value) = args.next() {
                                    values[key_matched_index].replace(vec![value]);
                                }
                            }                       
                        }
                    }
                }
            }
            values
        };

        if self.values.iter().all(|x| x.is_none()) {
            return Err(Error::Empty);
        }

        // Handle missing values based on kinds and defaults.
        for (i, value) in self.values.iter_mut().enumerate().filter(|(_, x)| x.is_none()) {
            value.replace(
                match self.list[i].kind {
                    SmargKind::Optional(default) => vec![default.to_owned()],
                    SmargKind::Flag => vec![false.to_string()],
                    SmargKind::List(0) => vec![],
                    SmargKind::List(_) | SmargKind::Required => {
                        return Err(Error::MissingRequired { expected: self.list.iter().filter(|x| Self::is_required(x)).count() });
                    },
                }
            );
        }

        // HACK: Concat items with a RARE delimiter to support parsing a List
        // from string.
        for xs in self.values.iter_mut() {
            let single_string = xs.take().unwrap().join(",");
            xs.replace(vec![single_string]);
        }


        Ts::try_from(self)
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env(self) -> Result<Ts, Error> {
        self.parse(std::env::args())
    }

    fn parse_nth<T>(&mut self, index: usize) -> Result<T, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: error::Error + 'static,
    {
        // TODO This seems unnecessarily complex...
        let mut value = self
            .values
            .get_mut(index)
            .unwrap_or_else(|| {
                panic!(
                    "Smargs.values constructed incorrectly: None in index {}",
                    index
                )
            })
            .take()
            .ok_or(Error::MissingRequired {
                expected: self
                    .list
                    .iter()
                    .filter(|x| matches!(x, Smarg { kind: SmargKind::Required, ..}))
                    .count()
            })?;

        value[0]
            .parse()
            .map_err(|e: <T as FromStr>::Err| Error::Smarg {
                printable_arg: self.list[index].to_string(),
                kind: ErrorKind::Parsing(
                    std::any::type_name::<T>(),
                    std::mem::replace(&mut value[0], "".to_string()),
                    Box::new(e)
                ),
            })
    }

    /// Initialize an empty `Smargs` struct.
    ///
    /// `description` is the general description of the program.
    pub fn new(_description: &str) -> Self {
        Self {
            list: Vec::new(),
            map: HashMap::new(),
            output: PhantomData,
            values: Vec::new(),
        }
    }

    /// Perform checks on new argument definition and add it to the collection
    /// or panic if checks fail.
    pub fn push(&mut self, smarg: Smarg) {
        Self::validate_format(&smarg.keys);

        // Save and check for duplicate keys in definition.
        for key in &smarg.keys {
            if self.map.insert(key.to_string(), self.list.len()).is_some() {
                panic!("Duplicate key defined: '{}'", key);
            }
        }

        // Add the definition.
        self.list.push(smarg);
    }

    /// Check that the keys conform to rules and panic otherwise.
    fn validate_format(keys: &[&'static str]) {
        // __Whitelist__ the allowed characters.
        const START_CHARACTERS: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const POST_START_CHARACTERS: &[u8] = b"-0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        for key in keys {
            if key.is_empty() {
                panic!("A key must not be empty");
            }
            if key.contains(' ') {
                panic!("A key must not contain spaces: '{}'", key);
            }
            if !key.is_ascii() {
                panic!("A key must only contain ASCII characters: {}", key);
            }
            
            let mut bytes = key.bytes();
            // This is OK as key is guaranteed to contain >0 bytes AND all
            // characters in key at this point are confirmed to be ASCII.
            let first_char = bytes.next().unwrap() as char;
            if !START_CHARACTERS.contains(first_char) {
                panic!(
                    "A key must begin with ASCII alphabet: {}",
                    key.replace(first_char, &format!("***{}***", first_char))
                );
            }
            for byte in bytes {
                if !POST_START_CHARACTERS.contains(&byte) {
                    let bad_char = byte as char;
                    panic!(
                        "A key must only contain ASCII alphabet, numbers or dash '-': {}",
                        key.replace(bad_char, &format!("***{}***", bad_char))
                    );
                }
            }
        }
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
    Parsing(&'static str, String, Box<dyn error::Error>),
}

/// Error type for getting and parsing the values of arguments.
#[derive(Debug)]
pub enum Error {
    Empty,
    MissingRequired { expected: usize },
    UndefinedKey(String),
    Smarg { printable_arg: String, kind: ErrorKind },
}

/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::Empty => String::from("No arguments found."),
            Self::MissingRequired { expected } => {
                // TODO What about "required _at least_ of X" in case of (future)
                // list-type arguments?
                format!("Not enough arguments (expected {}).", expected)
            }
            // TODO Suggest similar existing arguments in case of user typo.
            Self::UndefinedKey(key) => format!("Option '{}' does not exist", key),
            Self::Smarg { printable_arg, kind } => format!(
                "{} Usage: {}",
                match kind {
                    // TODO Inform how many times the argument was illegally repeated.
                    ErrorKind::Duplicate => "Too many entries of this argument.".to_owned(),
                    // TODO Elaborate on the type of value.
                    ErrorKind::MissingValue => "Option key used but missing the value.".to_owned(),
                    ErrorKind::Parsing(tname, input, e) => format!(
                        "Failed to parse the type {} from input '{}': {}.",
                        tname, input, e
                    ),
                },
                printable_arg
            ),
        };
        write!(f, "{}", msg)
    }
}

impl error::Error for Error {}

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
            SmargKind::Flag => "Negated by default".to_owned(),
            SmargKind::List(n) => format!("List of {} or more values", n),
        };

        write!(f, "{}{}", keystring, note)
    }
}

/// Describes the argument and how it is supplied.
#[derive(Debug, Clone)]
pub enum SmargKind {
    /// An argument which __needs__ to be provided by the user.
    Required,
    /// An argument with a default value that will be used if nothing is
    /// provided by the user.
    Optional(&'static str),
    /// A boolean argument defaulting to FALSE because using a flag essentially
    /// means signaling the event of or __turning on__ something, certainly not
    /// the contrary.
    // TODO Just combine this into the ArgType::False and make own method for
    // flag-arguments.
    Flag,
    /// A collection of some minimum number of arguments.
    List(usize),
}

impl<T1> TryFrom<Smargs<Self>> for (T1,)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((smargs.parse_nth(0)?,))
    }
}

impl<T1, T2> TryFrom<Smargs<Self>> for (T1, T2)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((smargs.parse_nth(0)?, smargs.parse_nth(1)?))
    }
}

impl<T1, T2, T3> TryFrom<Smargs<Self>> for (T1, T2, T3)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
        ))
    }
}

impl<T1, T2, T3, T4> TryFrom<Smargs<Self>> for (T1, T2, T3, T4)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5> TryFrom<Smargs<Self>> for (T1, T2, T3, T4, T5)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error + 'static,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5, T6> TryFrom<Smargs<Self>> for (T1, T2, T3, T4, T5, T6)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error + 'static,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error + 'static,
    T6: FromStr,
    <T6 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
            smargs.parse_nth(5)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5, T6, T7> TryFrom<Smargs<Self>> for (T1, T2, T3, T4, T5, T6, T7)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error + 'static,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error + 'static,
    T6: FromStr,
    <T6 as FromStr>::Err: error::Error + 'static,
    T7: FromStr,
    <T7 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
            smargs.parse_nth(5)?,
            smargs.parse_nth(6)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5, T6, T7, T8> TryFrom<Smargs<Self>> for (T1, T2, T3, T4, T5, T6, T7, T8)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error + 'static,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error + 'static,
    T6: FromStr,
    <T6 as FromStr>::Err: error::Error + 'static,
    T7: FromStr,
    <T7 as FromStr>::Err: error::Error + 'static,
    T8: FromStr,
    <T8 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
            smargs.parse_nth(5)?,
            smargs.parse_nth(6)?,
            smargs.parse_nth(7)?,
        ))
    }
}

impl<Ts, const N: usize> From<(&'static str, [(&'static str, Vec<&'static str>, SmargKind); N])> for Smargs<Ts>
where
    Ts: TryFrom<Smargs<Ts>, Error = Error>,
{
    fn from((desc, value): (&'static str, [(&'static str, Vec<&'static str>, SmargKind); N])) -> Self {
        let mut smargs = Smargs::new(desc);
        for (s, ks, k) in value {
            smargs.push(Smarg { desc: s, keys: ks, kind: k});
        }
        smargs
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, ErrorKind, Smargs, SmargKind, List};

    // NOTE: Use the naming scheme of target-method_scenario_expected-behavior.

    #[test]
    /// NOTE: This is testing the __implementation__ (on d76cf9288) that does
    /// multiple attempts on parsing to the required type from string following
    /// the option.
    fn parse_flag_and_positional_latter_not_interpreted_as_value_to_former() {
        let (a, b) = Smargs::<(bool, String)>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Flag),
                ("B", vec![], SmargKind::Required),
            ]))
            .parse("x -a false".split(' ').map(String::from))
            .unwrap();

        assert!(a);
        assert_eq!(b, "false".to_owned());
    }

    #[test]
    fn parse_definition_contains_optionals_and_requireds_uses_defaults_for_former() {
        let (a, b, c, d) = Smargs::<(bool, String, String, usize)>::from((
            "Test program",
            [
                ("A", vec!["Aa"], SmargKind::Flag),
                ("B", vec![], SmargKind::Required),
                ("C", vec!["c"], SmargKind::Optional("Ccc")),
                ("D", vec!["d", "Dd"], SmargKind::Required),
            ]))
            .parse("x Bbb 0".split(' ').map(String::from))
            .unwrap();

        assert!(!a);
        assert_eq!(b, "Bbb".to_owned());
        assert_eq!(c, "Ccc".to_owned());
        assert_eq!(d, 0);
    }

    #[test]
    #[should_panic]
    fn new_two_flags_have_same_keys_panics() {
        let _ = Smargs::<(bool, bool)>::from((
            "Test program",
            [
                ("A", vec!["a", "b"], SmargKind::Flag),
                ("B", vec!["a", "b"], SmargKind::Flag),
            ]
        ));
    }

    #[test]
    #[should_panic]
    fn new_two_out_of_three_flags_have_one_same_key_panics() {
        let _ = Smargs::<(bool, bool, bool)>::from((
            "Test program",
            [
                ("A", vec!["a", "c"], SmargKind::Flag),
                ("B", vec!["b"], SmargKind::Flag),
                ("C", vec!["c"], SmargKind::Flag),
            ]
        ));
    }

    #[test]
    fn parse_two_values_match_list_type_required_returns_vec() {
        let (a, ) = Smargs::<(List<usize>, )>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::List(2)),
            ]))
            .parse("x -a 0 -a 1".split(' ').map(String::from))
            .unwrap();

        assert_eq!(a.get(0), Some(&0));
        assert_eq!(a.get(1), Some(&1));
    }

    #[test]
    fn parse_two_values_match_same_single_definition_returns_duplicate_error_kind() {
        let err = Smargs::<(usize, )>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ]))
            .parse(
                "x -a 0 -a 1".split(' ').map(String::from)
            )
            .unwrap_err();

        assert!(matches!(
            match err { Error::Smarg { kind, .. } => kind, _ => panic!("expected Error::Smarg"), },
            ErrorKind::Duplicate,
        ));
    }

    #[test]
    fn parse_grouped_two_short_keys_latter_interpreted_as_key_to_following_value() {
        let (a, b) = Smargs::<(bool, usize)>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Flag),
                ("B", vec!["b"], SmargKind::Required),
            ]))
            .parse("x -ab 0".split(' ').map(String::from))
            .unwrap();

        assert!(a);
        assert_eq!(b, 0);
    }

    #[test]
    fn parse_grouped_short_keys_with_similar_long_latter_interpreted_as_single_key() {
        let (a, b, c) = Smargs::<(bool, usize, bool)>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Flag),
                ("B", vec!["b"], SmargKind::Required),
                ("C", vec!["ab"], SmargKind::Flag),
            ]))
            .parse("x -ab 0 --ab".split(' ').map(String::from))
            .unwrap();

        assert!(a);
        assert_eq!(b, 0);
        assert!(c);
    }

    #[test]
    fn parse_no_arguments_returns_empty_error() {
        let err = Smargs::<(bool, bool)>::from((
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Flag),
                ("B" , vec!["b"], SmargKind::Flag),
            ]))
            .parse(std::iter::empty())
            .unwrap_err();
        
        assert!(matches!(
            err,
            Error::Empty,
        ));
    }

    #[test]
    fn parse_required_missing_value_to_key_at_end_returns_missing_value_error_kind() {
        let err = Smargs::<(usize, )>::from((
            "Test program",
            [
                ("A", vec!["a"], SmargKind::Required),
            ]))
            .parse("x -a".split(' ').map(String::from))
            .unwrap_err();

        assert!(matches!(
            match err { Error::Smarg { kind, .. } => kind, _ => panic!("expected Error::Smarg"), },
            ErrorKind::MissingValue,
        ));
    }

    #[test]
    fn parse_missing_one_out_of_two_required_options_returns_missing_required_error() {
        let err = Smargs::<(usize, usize)>::from((
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Required),
                ("B" , vec!["b"], SmargKind::Required),
            ]))
            .parse("x -b 0".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Error::MissingRequired { expected: 2 },
        ));
    }

    #[test]
    fn parse_missing_one_out_of_two_required_positionals_returns_missing_required_error() {
        let err = Smargs::<(usize, usize)>::from((
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Required),
                ("B" , vec!["b"], SmargKind::Required),
            ]))
            .parse("x 0".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Error::MissingRequired { expected: 2 },
        ));
    }

    #[test]
    fn parse_undefined_key_found_returns_undefined_key_error() {
        let err = Smargs::<(usize, )>::from((
            "Test program",
            [
                ("A" , vec!["a"], SmargKind::Required),
            ]))
            .parse("x 0 -b".split(' ').map(String::from))
            .unwrap_err();
        
        assert!(matches!(
            err,
            Error::UndefinedKey(s) if s == "b",
        ));
    }
}
