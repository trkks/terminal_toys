use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::fmt::Display;
use std::iter;
use std::str::FromStr;

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
    NotEnough { expected: usize, count: usize },
    Smarg { argument: Smarg, kind: ErrorKind },
    // TODO Add a check and an error for non-defined arguments in args-input.
}

/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::Empty => String::from("No arguments found"),
            Self::NotEnough { expected, count } => {
                // TODO "Expected" or "required"? What about "expected _at least_"
                // in case of (future) list-type arguments?
                format!("Not enough arguments: expected {}, got {}", expected, count)
            }
            Self::Smarg { argument, kind } => format!(
                "{} - {}",
                argument,
                match kind {
                    // TODO Inform how many times the argument was illegally repeated.
                    ErrorKind::Duplicate => format!("Too many entries of this argument"),
                    // TODO Elaborate on the type of value.
                    ErrorKind::MissingValue => format!("Option found but missing a value"),
                    ErrorKind::Parsing(tname, input, e) => format!(
                        "Failed to parse the type {} from input '{}' : {}",
                        tname, input, e
                    ),
                },
            ),
        };
        write!(f, "{}", msg)
    }
}

impl error::Error for Error {}

/// Normalize/preprocess the CLI-syntax (most notably do "-bar" => "-b -a -r").
///
/// Return `Option<(bool, String)>` in order to deal with argument positions
/// later. The bool represents if the argument is an option, which needs to be
/// added to the dict.
fn normalize(args: impl Iterator<Item = String>) -> Vec<Option<(bool, String)>> {
    args
        // Ignore the executable. TODO Allow saving exe with a .exe() -method?
        .skip(1)
        // Remove the cli-syntax off of keys and normalize the
        // multi-character groups.
        .fold(Vec::new(), |mut acc, s| {
            let n = key_prefix_len(&s);
            if n == 1 {
                // Multi-character group.
                acc.extend(s.chars().skip(1).map(|c| Some((true, c.to_string()))));
            } else {
                // Also remove any other length prefixes starting with '-'.
                acc.push(Some((n > 0, s.chars().skip(n).collect())));
            }
            acc
        })
}

/// Return the amount of preceding '-'-characters or 0 if the first character of
/// the rest of the string is a number.
fn key_prefix_len(s: &str) -> usize {
    // TODO Why take(2)?
    // TODO Error if typo "--2" when meant "-2" (negative 2)?
    let prefix_len = s.chars().take(2).take_while(|c| *c == '-').count();
    if let Some(fst_char_of_key) = s.chars().nth(prefix_len) {
        if !fst_char_of_key.is_ascii_digit() {
            return prefix_len;
        }
    }
    0
}

/// Search list of args (which might be values denoted by `false`) for the first
/// match of the given key. Return the index of found match.
fn find_matching_idx(args: &mut [Option<(bool, String)>], key: &'static str) -> Option<usize> {
    args.iter_mut().enumerate().find_map(|(i, opt)| {
        if let Some((true, arg)) = opt {
            if arg == key {
                return Some(i);
            }
        }
        None
    })
}

#[derive(Debug, Clone)]
pub struct Smarg {
    keys: Vec<&'static str>,
    kind: SmargKind,
}

impl Display for Smarg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keystring: String = {
            let mut xs = self.keys.clone();
            // Sort by alphabet + length as normal (shortest first).
            xs.sort();
            // Sort in reverse-length second.
            xs.sort_by(|x, y| x.len().cmp(&y.len()).reverse());
            xs.iter().map(|x| format!("{}{} ", if x.len() == 1 { "-" } else { "--" }, x)).collect()
        };

        let (is_valued, note) = match &self.kind {
            SmargKind::Required => (true, "Required argument".to_owned()),
            SmargKind::Optional(default) => (true, format!("Defaults to '{}'", default)),
            SmargKind::Flag => (false, "Negated by default".to_owned()),
        };

        write!(f, "{}{} ( {} )", keystring, if is_valued { "<value>"} else { "" }, note)
    }
}

#[derive(Debug, Clone)]
pub enum SmargKind {
    Required,
    Optional(String),
    // TODO Just combine this into the ArgType::False and make own method for
    // flag-arguments.
    Flag,
}

/// Specifies if an argument is a flag.
/// TODO Would just plain ol' Optional be adequate?
pub enum ArgType<'a> {
    False,
    Other(&'a str),
}

/// SiMpler thAn wRiting it once aGain Surely :)
///
/// # Examples:
/// Program arguments will be defined using the builder:
/// ```
/// use terminal_toys::{Smargs, ArgType};
///
/// let builder = Smargs::builder("Register for service")
///     .optional(["no-newsletter"], "Opt-out from receiving newsletter", ArgType::False)
///     .required([],                "Your full name")
///     .optional(["d"],             "Email address domain", ArgType::Other("getspam"))
///     .required(["a", "age"],      "Your age");
/// ```
/// The different arguments will be recognized from the command line syntax and
/// parsed into usable types:
/// ```
/// # fn main() -> Result<(), String> {
/// # use terminal_toys::{Smargs, ArgType};
/// # let builder = Smargs::builder("Register for service")
/// #    .optional(["no-newsletter"], "Opt-out from receiving newsletter", ArgType::False)
/// #    .required([],                "Your full name")
/// #    .optional(["d"],             "Email address domain", ArgType::Other("getspam"))
/// #    .required(["a", "age"],      "Your age");
/// # let mut newsletter_subscribers = vec![];
/// let args = vec!["register.exe", "--no-newsletter", "-a", "26", "-d", "hatch", "Matt Myman"].into_iter().map(String::from);
///
/// let (no_news, name, domain, age)
///     : (bool, String, String, usize)
///     = builder.parse(args).map_err(|e| format!("Argument failure: {}", e))?;
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
/// # use terminal_toys::{Smargs, ArgType};
/// # let builder = Smargs::builder("Register for service")
/// #    .optional(["no-newsletter"], "Opt-out from receiving newsletter", ArgType::False)
/// #    .required([],                "Your full name")
/// #    .optional(["d"],             "Email address domain", ArgType::Other("getspam"))
/// #    .required(["a", "age"],      "Your age");
/// let args = vec!["register.exe", "Matt Myman", "26"].into_iter().map(String::from);
///
/// let (no_news, name, domain, age) : (bool, String, String, usize) = builder.parse(args).unwrap();
///
/// assert!(!no_news);
/// assert_eq!(name, "Matt Myman".to_string());
/// assert_eq!(domain, "getspam".to_string());
/// assert_eq!(age, 26);
/// ```
#[derive(Debug, Clone)]
pub struct Smargs {
    defins: Vec<Smarg>,
    values: Vec<Option<String>>,
}

impl Smargs {
    /// Start a builder defining the order, keys and description of a program
    /// and its arguments.
    ///
    /// `description` is the general description of the program.
    pub fn builder(_description: &str) -> Self {
        Self {
            defins: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Define next an argument which __needs__ to be provided by the user.
    pub fn required<const N: usize>(mut self, keys: [&'static str; N], description: &str) -> Self {
        self.push_arg(keys, description, SmargKind::Required);
        self
    }

    /// Define next an argument with a default value that will be used if
    /// nothing is provided by the user.
    ///
    /// A boolean argument defaults to FALSE because using a flag essentially
    /// means signaling the event of or __turning on__ something, certainly not
    /// the contrary.
    pub fn optional<const N: usize>(
        mut self,
        keys: [&'static str; N],
        description: &str,
        default: ArgType,
    ) -> Self {
        let kind = match default {
            ArgType::False => SmargKind::Flag,
            ArgType::Other(s) => SmargKind::Optional(s.to_owned()),
        };
        self.push_arg(keys, description, kind);
        self
    }

    /// Parse the argument strings into the type `T` according to the
    /// definition of `self` which may include default values for some.
    pub fn parse<T>(mut self, args: impl Iterator<Item = String>) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error = Error>,
    {
        let mut args = normalize(args);

        if args.is_empty() {
            return Err(Error::Empty);
        }

        // Fill in matching values based on keys.
        self.resolve_kv_pairs(&mut args)?;

        // Replace all the rest in order after the options (and optionals) are
        // filtered out.
        for (x, y) in iter::zip(
            self.values.iter_mut().filter(|x| x.is_none()),
            args.iter_mut().filter(|x| x.is_some()),
        ) {
            x.replace(y.take().unwrap().1);
        }

        // TODO Instead of parsing into the values here, maybe return some
        // abstraction like "IntermediateElemT_i" or "FakeT_i" (or perhaps
        // `std::any::Any`?) that could be used to identify the boolean at
        // runtime(?) (and thus get rid of ArgType::False).
        T::try_from(self)
    }

    /// Select the values for arguments based on identified keys.
    ///
    /// Key-value pairs are roughly based on the rough syntax:
    /// > Key := -Alph Value | --Alph Value
    ///
    /// Value is a superset of Alph, which means is not always clear when a string
    /// is a key or a value. This means, that some strings meant as values for
    /// example "--my-username--" will be presented as being keys. However for
    /// example "-42" is strictly considered a value.
    fn resolve_kv_pairs(&mut self, args: &mut Vec<Option<(bool, String)>>) -> Result<(), Error> {
        self.values = Vec::with_capacity(self.defins.len());

        for smarg @ Smarg { keys, kind } in &self.defins {
            let opt = keys.iter().find_map(|x| find_matching_idx(args, x));

            // TODO Somehow despookify this if?
            let item = if let Some(key_idx) = opt {
                // Remove the now unneeded key.
                args[key_idx] = None;
                Some(if let SmargKind::Flag = kind {
                    true.to_string()
                } else {
                    // Check existence of and take the subsequent, key-matching,
                    // value.
                    args.get_mut(key_idx + 1)
                        .ok_or(Error::Smarg {
                            argument: smarg.clone(),
                            kind: ErrorKind::MissingValue
                        })?
                        .take()
                        .unwrap()
                        .1
                })
            } else {
                // Handle the case when a match is not found for the key.
                match kind {
                    // Flag defaults to false here.
                    SmargKind::Flag => Some(false.to_string()),
                    // Optional is replaced by its specified default.
                    SmargKind::Optional(default) => Some(default.clone()),
                    // Required will need to be found based on its position.
                    SmargKind::Required => None,
                }
            };

            self.values.push(item);
        }
        Ok(())
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env<T>(self) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error = Error>,
    {
        self.parse(std::env::args())
    }

    /// Perform common operations for defining an argument in order
    /// and TODO: generate a user-friendly description for it.
    fn push_arg<const N: usize>(&mut self, keys: [&'static str; N], description: &str, kind: SmargKind) {
        // Check for duplicates keys in user definition TODO This could
        // theoretically be done at compile time...or probably a lot cleaner...
        if let Some((def, duplicate_key)) = self.defins.iter().find_map(|def| {
            def.keys.iter().find_map(|x| {
                keys.iter()
                    .position(|y| y == x)
                    .and_then(|i| Some((def, keys[i])))
            })
        }) {
            panic!(
                "Duplicate key '{}' found in arguments' definition: {:?}",
                duplicate_key, def
            )
        } else {
            self.defins.push(Smarg { keys: keys.to_vec(), kind });
        }
    }

    fn parse_nth<T>(&mut self, index: usize) -> Result<T, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: error::Error + 'static,
    {
        // TODO This seems unnecessarily complex...
        let value = self
            .values
            .get_mut(index)
            .unwrap_or_else(|| {
                panic!(
                    "Smargs.values constructed incorrectly: None in index {}",
                    index
                )
            })
            .take()
            .ok_or_else(|| {
                let required_count = self
                    .defins
                    .iter()
                    .filter(|x| {
                        if let SmargKind::Required = x.kind {
                            true
                        } else {
                            false
                        }
                    })
                    .count();
                Error::NotEnough {
                    expected: required_count,
                    count: index - required_count,
                }
            })?;

        value
            .parse()
            .map_err(|e: <T as FromStr>::Err| Error::Smarg {
                argument: self.defins[index].clone(),
                kind: ErrorKind::Parsing(std::any::type_name::<T>(), value, Box::new(e)),
            })
    }
}

impl<T1, T2> TryFrom<Smargs> for (T1, T2)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
        Ok((smargs.parse_nth(0)?, smargs.parse_nth(1)?))
    }
}

impl<T1, T2, T3> TryFrom<Smargs> for (T1, T2, T3)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error + 'static,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error + 'static,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error + 'static,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
        ))
    }
}

impl<T1, T2, T3, T4> TryFrom<Smargs> for (T1, T2, T3, T4)
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
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5> TryFrom<Smargs> for (T1, T2, T3, T4, T5)
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
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5, T6> TryFrom<Smargs> for (T1, T2, T3, T4, T5, T6)
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
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
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

impl<T1, T2, T3, T4, T5, T6, T7> TryFrom<Smargs> for (T1, T2, T3, T4, T5, T6, T7)
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
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
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

impl<T1, T2, T3, T4, T5, T6, T7, T8> TryFrom<Smargs> for (T1, T2, T3, T4, T5, T6, T7, T8)
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
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
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

#[cfg(test)]
mod tests {
    use super::{ArgType, Error, Smargs, ErrorKind};

    #[test]
    fn general_use_case() {
        use std::path::PathBuf;

        let (a1, a2, a3, a4, a5): (PathBuf, u32, u32, bool, PathBuf) =
            Smargs::builder("A program to scale an image")
                .required([], "Path to the image")
                .required(["w", "width"], "The width to scale into")
                .required(["h", "height"], "The height to scale into")
                .optional(
                    ["v", "verbose"],
                    "Print realtime status of operations",
                    ArgType::False,
                )
                .optional(["o", "output"], "Output path", ArgType::Other("a"))
                .parse(
                    "scale_img.exe -v ./img.png -w 1366 -h 768 --output scaled.png"
                        .split(" ")
                        .map(String::from),
                )
                .unwrap();

        assert_eq!(a1, "./img.png".parse::<PathBuf>().unwrap());
        assert_eq!(a2, 1366);
        assert_eq!(a3, 768);
        assert!(a4);
        assert_eq!(a5, "scaled.png".parse::<PathBuf>().unwrap());
    }

    #[test]
    /// NOTE: This is testing the __implementation__ (on d76cf9288) that does
    /// multiple attempts on parsing to the required type from string following
    /// the option.
    fn confused_flag_option() {
        let (a1, a2): (bool, String) =
            Smargs::builder("Compute P AND NOT Q from a bool and a string")
                .optional(["b", "bool"], "A bool", ArgType::False)
                .required([], "A string representing another bool")
                .parse("a -b false".split(" ").map(String::from))
                .unwrap();

        // True AND NOT False
        let computation = a1 && !a2.parse::<bool>().unwrap();

        assert!(computation);
    }

    #[test]
    fn mixed_positions() {
        let builder = Smargs::builder("Test program")
            .optional(["foo"], "Foo", ArgType::False)
            .required([], "Bar")
            .optional(["b"], "Baz", ArgType::Other("Lorem"))
            .required(["q", "qux"], "Qux");
        let args = vec!["a", "Bar Bar", "42"].into_iter().map(String::from);

        let (foo, bar, baz, qux): (bool, String, String, usize) = builder.parse(args).unwrap();

        assert!(!foo);
        assert_eq!(bar, "Bar Bar".to_string());
        assert_eq!(baz, "Lorem".to_string());
        assert_eq!(qux, 42);
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_flag() {
        Smargs::builder("Test program")
            .optional(["f"], "Foo", ArgType::False)
            .optional(["f"], "Bar", ArgType::False);
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_flag2() {
        Smargs::builder("Test program")
            .optional(["f", "b"], "Foo", ArgType::False)
            .optional(["a"], "Bar", ArgType::False)
            .optional(["b", "f"], "Baz", ArgType::False);
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_word() {
        Smargs::builder("Test program")
            .optional(["foo"], "Foo", ArgType::False)
            .optional(["foo"], "Bar", ArgType::False);
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_word2() {
        Smargs::builder("Test program")
            .optional(["foo"], "Foo", ArgType::False)
            .optional(["bar"], "Bar", ArgType::False)
            .optional(["baz", "foo"], "Baz", ArgType::False);
    }

    /// Catch the __first__ duplicate that appears from left to right TODO __if__ the
    /// expected type is not a list.
    /*
    #[test]
    fn error_arg_duplicates() {

        let err_duplicate = Smargs::builder("Test program")
            .optional(["f"], "Foo", ArgType::False)
            .optional(["b"], "Bar", ArgType::False)
            .parse::<(bool, bool)>("a -fbfb".split(" ").map(String::from))
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("f".to_owned())
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(["foo"], "Foo", ArgType::False)
            .optional(["bar"], "Bar", ArgType::False)
            .parse::<(bool, bool)>(
                "a --foo --foo --bar --bar".split(" ").map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("foo".to_owned()),
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(["f"], "Foo", ArgType::False)
            .optional(["b"], "Bar", ArgType::False)
            .optional(["baz"], "Baz", ArgType::False)
            .parse::<(bool, bool, bool)>(
                "a -fb --baz -bf --baz".split(" ").map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("b".to_owned()),
        );
    }
    */

    #[test]
    fn multi_character_option() {
        let (b, a, r, bar): (bool, bool, String, bool) = Smargs::builder("Test program")
            .optional(["b"], "Bee", ArgType::False)
            .optional(["a"], "Ay", ArgType::False)
            .optional(["r"], "Are", ArgType::Other("some-default"))
            .optional(["bar"], "Bar", ArgType::False)
            .parse("a -bar r-arg-value --bar".split(" ").map(String::from))
            .unwrap();
        assert!(b);
        assert!(a);
        assert_eq!(r, "r-arg-value");
        assert!(bar);

        let (b, a, r, verbose, f): (bool, bool, bool, bool, f32) = Smargs::builder("Test program")
            .optional(["b"], "Bee", ArgType::False)
            .optional(["a"], "Ay", ArgType::False)
            .optional(["r"], "Are", ArgType::False)
            .optional(["verbose"], "Verbose", ArgType::False)
            .optional(["f"], "Foo", ArgType::Other("666"))
            .parse("a -bar --verbose -f 4.2".split(" ").map(String::from))
            .unwrap();
        assert!(a);
        assert!(b);
        assert!(r);
        assert!(verbose);
        assert_eq!(f, 4.2);
    }

    #[test]
    fn multiple_char_keys_different_types() {
        let (bar, foo, baz): (usize, f32, String) = Smargs::builder("Test program")
            .optional(["f", "o", "bar"], "Bar", ArgType::Other("42"))
            .optional(["b", "a", "r", "foo"], "Foo", ArgType::Other("3.14"))
            .required([], "Baz")
            .parse("a BazArg --bar 666".split(" ").map(String::from))
            .unwrap();
        assert_eq!(bar, 666);
        assert!(3.1 < foo && foo < 3.2);
        assert_eq!(baz, "BazArg".to_owned());
    }

    #[test]
    fn multiple_char_keys_same_types() {
        let (bar, foo, baz): (bool, bool, bool) = Smargs::builder("Test program")
            .optional(["f", "o", "bar"], "Bar", ArgType::False)
            .optional(["b", "a", "r", "foo"], "Foo", ArgType::False)
            .optional(["z", "baz"], "Baz", ArgType::False)
            .parse("a --foo -f".split(" ").map(String::from))
            .unwrap();
        assert!(bar);
        assert!(foo);
        assert!(!baz);

        let (bar, foo, baz): (usize, usize, usize) = Smargs::builder("Test program")
            .optional(["f", "o", "bar"], "Bar", ArgType::Other("42"))
            .optional(["b", "a", "r", "foo"], "Foo", ArgType::Other("3"))
            .required([], "Baz")
            .parse("a 123 --bar 666".split(" ").map(String::from))
            .unwrap();
        assert_eq!(bar, 666);
        assert_eq!(foo, 3);
        assert_eq!(baz, 123);
    }

    #[test]
    fn error_on_empty() {
        match Smargs::builder("Test program")
            .optional(["f"], "Foo", ArgType::False)
            .optional(["b"], "Bar", ArgType::False)
            .parse::<(bool, bool)>(std::iter::empty())
            .unwrap_err()
        {
            Error::Empty => {},
            e => panic!("Expected {:?} got {:?}", Error::Empty, e),
        }
    }

    #[test]
    fn missing_value_at_end() {
        match Smargs::builder("Test program")
            .required([], "Foo")
            .required(["d"], "Bar")
            .required(["a"], "Baz")
            .parse::<(String, usize, usize)>("a \"moth man\" -a 41 -d".split(" ").map(String::from))
            .unwrap_err()
        {
            Error::Smarg { argument: _, kind: ErrorKind::MissingValue } => {},
            e => panic!("Expected {:?} got {:?}", ErrorKind::MissingValue, e),
        }
    }
}
