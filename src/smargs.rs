use std::any;
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::fmt::Display;
use std::iter;
use std::marker::PhantomData;
use std::str::FromStr;


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
#[derive(Debug)]
pub struct Smargs<Ts> {
    defins: Vec<Smarg>,
    values: Vec<Option<String>>,
    /// Made-up field required for storing the output type `Ts`.
    output: PhantomData<Ts>
}

impl<Ts: TryFrom<Self, Error = Error>> Smargs<Ts> {
    /// Parse the argument strings into the type `T` according to the
    /// definition of `self` which may include default values for some.
    pub fn parse(mut self, mut args: impl Iterator<Item = String>) -> Result<Ts, Error>
    {
        // Ignore the executable. TODO Allow saving exe with a .exe() -method?
        // TODO Save it anyway for error/help messages?
        args.next();

        let mut args = {
            // Check that the args can satisfy all definitions.

            let all_keys: Vec<&&'static str> = self
                .defins
                .iter()
                .flat_map(|x| x.keys.iter())
                .collect();

            let mut xs = Vec::<Option<(Arg, String)>>::new();
            for arg in args {
                xs.extend(
                    // Wrap elements in Option for memory trickery.
                    normalize(&all_keys, arg)?.into_iter().map(|x| Some(x))
                );
            }
            xs
        };

        // Fill in matching values based on keys.
        self.resolve_kv_pairs(&mut args)?;

        if args.is_empty() {
            return Err(Error::Empty);
        }


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
        Ts::try_from(self)
    }
    /// Validate the keys based on definition and select the values for
    /// arguments based on identified keys.
    ///
    /// Key-value pairs are roughly based on the rough syntax:
    /// > Key := -Alph Value | --Alph Value
    ///
    /// Value is a superset of Alph, which means is not always clear when a string
    /// is a key or a value. This means, that some strings meant as values for
    /// example "--my-username--" will be presented as being keys. However for
    /// example "-42" is strictly considered a value.
    fn resolve_kv_pairs(&mut self, args: &mut Vec<Option<(Arg, String)>>) -> Result<(), Error> {
        self.values = Vec::with_capacity(self.defins.len());

        for smarg @ Smarg { desc, keys, kind } in &self.defins {
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
                            printable_arg: smarg.to_string(),
                            kind: ErrorKind::MissingValue,
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
                    SmargKind::Optional(default) => Some(default.to_string()),
                    // Required will need to be found based on its position.
                    SmargKind::Required => None,
                }
            };

            self.values.push(item);
        }
        Ok(())
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env(self) -> Result<Ts, Error> {
        self.parse(std::env::args())
    }

    /// Perform common operations for defining an argument in order
    /// and TODO: generate a user-friendly description for it.
    fn push_arg<const N: usize>(
        &mut self,
        keys: [&'static str; N],
        description: &'static str,
        kind: SmargKind,
    ) {
        // Check for duplicates keys in user definition TODO This could
        // theoretically be done at compile time...or probably a lot cleaner...
        if let Some((def, duplicate_key)) = self.defins.iter().find_map(|def| {
            def.keys.iter().find_map(|x| {
                keys.iter()
                    .position(|y| y == x).map(|i| (def, keys[i]))
            })
        }) {
            panic!(
                "Duplicate key '{}' found in arguments' definition: {:?}",
                duplicate_key, def
            )
        } else {
            self.defins.push(Smarg {
                desc: description,
                keys: keys.to_vec(),
                kind,
            });
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
            .ok_or(Error::MissingRequired {
                expected: self
                    .defins
                    .iter()
                    .filter(|x| matches!(x, Smarg { kind: SmargKind::Required, ..}))
                    .count()
            })?;

        value
            .parse()
            .map_err(|e: <T as FromStr>::Err| Error::Smarg {
                printable_arg: self.defins[index].to_string(),
                kind: ErrorKind::Parsing(std::any::type_name::<T>(), value, Box::new(e)),
            })
    }

    /// Initialize an empty `Smargs` struct.
    ///
    /// `description` is the general description of the program.
    pub fn new(_description: &str) -> Self {
        Self {
            defins: Vec::new(),
            values: Vec::new(),
            output: PhantomData,
        }
    }

    pub fn push(&mut self, smarg: Smarg) {
        Self::validate_format(&smarg.keys);

        let earlier_keys: Vec<&&'static str> = self
            .defins
            .iter()
            .flat_map(|x| x.keys.iter())
            .collect();
        for key in earlier_keys {
            if smarg.keys.contains(key) {
                panic!("Duplicate key defined '{}'", key);
            }
        }

        self.defins.push(smarg);
    }

    fn validate_format(keys: &[&'static str]) {
        for key in keys {
            if key.contains(' ') {
                panic!("A key must not contain spaces: '{}'", key);
            }
            // TODO: Check prefix.
            // TODO: Check characters used after prefix.
        }
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

enum Arg {
    Value,
    Option,
}

/// Prevent non-defined but option-seeming strings like '--kebab--' or negative
/// numbers like '-42' from being interpreted as options and normalize the
/// CLI-syntax (most notably do "-bar" => "-b -a -r", which is why this returns
/// `Vec`).
/// TODO Holy references :o
/// TODO Why not utilize the definition at this point???
/// TODOTODO Why not enforce these rules at definition-time???
fn normalize(key_set: &[&&'static str], arg: String) -> Result<Vec<(Arg, String)>, Error> {
    // Assume initially, that if the arg begins with '-' it is a key.
    let normalized = {
        // Remove the cli-syntax off of keys and normalize the
        // multi-character groups.
        let n = key_prefix_len(&arg);
            if n == 1 {
                // Multi-character group.
            let keys = arg.chars().skip(1);
            keys.map(|c| (1, c.to_string())).collect()
            } else {
                // Also remove any other length prefixes starting with '-'.
            let s = arg.chars().skip(n).collect();
            vec![(n, s)]
        }
    };

    let defined = |key: &str| key_set.contains(&&key);

    // Check that the assumed key(s) is defined and if not, it must be a value.
    // FIXME multiples of a key need to be checked e.g. if 'x' is a
    // key expecting value but input is "-x -x" this becomes
    // [Option("x"), Option("x")] instead of [Option("x"), Value("x")]
    // Handle by "popping" the keys as they are checkd?
    match &normalized[..] {
        // TODO Could probably be possible without the cloning(?) of string.
        [(0, value)] => Ok(vec![(Arg::Value, value.to_owned())]),
        [(n, key)] if *n > 1 => {
            if defined(key) {
                Ok(vec![(Arg::Option, key.to_owned())])
            } else {
                Err(Error::UndefinedKey(key.to_owned()))
            }
        },
        multi_key => {
            // Keep track of any keys being valid; if none of the keys in the
            // group are defined, the group could actually be a value e.g. a
            // stylized username "-myuser-" and is then interpreted as such.
            let (none_defined, result) = {
                let mut none_defined = true;
                let mut result = Ok(Vec::<(Arg, String)>::new());
                for (_, key) in multi_key {
                    // Everything, right here, all at once.
                    // The Result is the return value or first error found.
                    if defined(key) {
                        if let Ok(keys) = result.as_mut() {
                            keys.push((Arg::Option, key.to_owned()));
                            none_defined = false;
                        }
                    } else {
                        result = Err(Error::UndefinedKey(key.to_owned()));
                    }
                }
                (none_defined, result)
            };

            if none_defined {
                // Return the value as is.
                Ok(vec![(Arg::Value, arg)])
            } else {
                result
            }
        },
    }
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
fn find_matching_idx(args: &mut [Option<(Arg, String)>], key: &'static str) -> Option<usize> {
    args.iter_mut().enumerate().find_map(|(i, opt)| {
        if let Some((Arg::Option, arg)) = opt {
            if arg == key {
                return Some(i);
            }
        }
        None
    })
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
            SmargKind::Flag => "Negated by default".to_owned(),
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
}

/// Specifies if an argument is a flag.
/// TODO Would just plain ol' Optional be adequate?
#[derive(Debug)]
pub enum ArgType {
    False,
    Other(String),
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

#[cfg(test)]
mod tests {
    use crate::smargs::{Smarg, SmargKind};

    use super::{ArgType, Error, ErrorKind, Smargs};

    #[test]
    fn general_use_case() {
        use std::path::PathBuf;

        let (a1, a2, a3, a4, a5): (PathBuf, u32, u32, bool, PathBuf) = {
                let mut x = Smargs::<(PathBuf, u32, u32, bool, PathBuf)>::new("A program to scale an image");
                for (desc, keys, kind) in [
                    ("Path to the image", vec![], SmargKind::Required),
                    ("The width to scale into", vec!["w", "width"], SmargKind::Required),
                    ("The height to scale into", vec!["h", "height"], SmargKind::Required),
                    ("Print realtime status of operations", vec!["v", "verbose"], SmargKind::Flag),
                    ("Output path", vec!["o", "output"], SmargKind::Optional("a")),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse(
            "scale_img.exe -v ./img.png -w 1366 -h 768 --output scaled.png"
                    .split(' ')
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
        let (a1, a2): (bool, String) = {
                let mut x = Smargs::<(bool, String)>::new("Compute P AND NOT Q from a bool and a string");
                for (desc, keys, kind) in [
                    ("A bool", vec!["b", "bool"], SmargKind::Flag),
                    ("A string representing another bool", vec![], SmargKind::Required),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a -b false".split(' ').map(String::from))
            .unwrap();

        // True AND NOT False
        let computation = a1 && !a2.parse::<bool>().unwrap();

        assert!(computation);
    }

    #[test]
    fn mixed_positions() {
        let builder = {
            let mut x = Smargs::<(bool, String, String, usize)>::new("Test program");
            for (desc, keys, kind) in [
                ("Foo", vec!["foo"], SmargKind::Flag),
                ("Bar", vec![], SmargKind::Required),
                ("Baz", vec!["b"], SmargKind::Optional("Lorem")),
                ("Qux", vec!["q", "qux"], SmargKind::Required),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };
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
        let mut x = Smargs::<(bool, bool, bool)>::new("Test program");
        for (desc, keys, kind) in [
            ("Foo", vec!["f"], SmargKind::Flag),
            ("Bar", vec!["f"], SmargKind::Flag),
        ]
        {
            x.push(Smarg { desc, keys, kind });
        }
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_flag2() {
        let mut x = Smargs::<(bool, bool, bool)>::new("Test program");
        for (desc, keys, kind) in [
            ("Foo", vec!["f", "b"], SmargKind::Flag),
            ("Bar", vec!["a"], SmargKind::Flag),
            ("Baz", vec!["b", "f"], SmargKind::Flag),
        ]
        {
            x.push(Smarg { desc, keys, kind });
        }
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_word() {
        let mut x = Smargs::<(bool, bool, bool)>::new("Test program");
        for (desc, keys, kind) in [
            ("Foo", vec!["foo"], SmargKind::Flag),
            ("Bar", vec!["foo"], SmargKind::Flag),
        ]
        {
            x.push(Smarg { desc, keys, kind });
        }
    }

    #[test]
    #[should_panic]
    fn error_definition_duplicates_word2() {
        let mut x = Smargs::<(bool, bool, bool)>::new("Test program");
        for (desc, keys, kind) in [
            ("Foo", vec!["foo"], SmargKind::Flag),
            ("Bar", vec!["bar"], SmargKind::Flag),
            ("Baz", vec!["baz", "foo"], SmargKind::Flag),
        ]
        {
            x.push(Smarg { desc, keys, kind });
        }
    }

    /// Catch the __first__ duplicate that appears from left to right TODO __if__ the
    /// expected type is not a list.
    /*
    #[test]
    fn error_arg_duplicates() {

        let err_duplicate = Smargs::<(bool, bool, bool)>::builder("Test program")
            ("Foo", vec!["f"], SmargKind::Flag),
            ("Bar", vec!["b"], SmargKind::Flag),
            .parse("a -fbfb".split(" ").map(String::from))
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("f".to_owned())
        );

        let err_duplicate = Smargs::<(bool, bool, bool)>::builder("Test program")
            ("Foo", vec!["foo"], SmargKind::Flag),
            ("Bar", vec!["bar"], SmargKind::Flag),
            .parse(
                "a --foo --foo --bar --bar".split(" ").map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("foo".to_owned()),
        );

        let err_duplicate = Smargs::<(bool, bool, bool)>::builder("Test program")
            ("Foo", vec!["f"], SmargKind::Flag),
            ("Bar", vec!["b"], SmargKind::Flag),
            ("Baz", vec!["baz"], SmargKind::Flag),
            .parse(
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
        let (b, a, r, bar): (bool, bool, String, bool) = {
                let mut x = Smargs::<(bool, bool, String, bool)>::new("Test program");
                for (desc, keys, kind) in [
                    ("Bee", vec!["b"], SmargKind::Flag),
                    ("Ay",  vec!["a"], SmargKind::Flag),
                    ("Are", vec!["r"], SmargKind::Optional("some-default")),
                    ("Bar", vec!["bar"], SmargKind::Flag),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a -bar r-arg-value --bar".split(' ').map(String::from))
            .unwrap();
        assert!(b);
        assert!(a);
        assert_eq!(r, "r-arg-value");
        assert!(bar);

        let (b, a, r, verbose, f): (bool, bool, bool, bool, f32) = {
                let mut x = Smargs::<(bool, bool, bool, bool, f32)>::new("Test program");
                for (desc, keys, kind) in [
                    ("Bee", vec!["b"], SmargKind::Flag),
                    ("Ay",  vec!["a"], SmargKind::Flag),
                    ("Are", vec!["r"], SmargKind::Flag),
                    ("Verbose", vec!["verbose"], SmargKind::Flag),
                    ("Foo", vec!["f"], SmargKind::Optional("666")),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a -bar --verbose -f 4.2".split(' ').map(String::from))
            .unwrap();
        assert!(a);
        assert!(b);
        assert!(r);
        assert!(verbose);
        assert_eq!(f, 4.2);
    }

    #[test]
    fn multiple_char_keys_different_types() {
        let (bar, foo, baz): (usize, f32, String) = {
                let mut x = Smargs::<(usize, f32, String)>::new("Test program");
                for (desc, keys, kind) in [
                    ("Bar" , vec!["f", "o", "bar"], SmargKind::Optional("42")),
                    ("Foo" , vec!["b", "a", "r", "foo"], SmargKind::Optional("3.14")),
                    ("Baz" , vec![], SmargKind::Required),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a BazArg --bar 666".split(' ').map(String::from))
            .unwrap();
        assert_eq!(bar, 666);
        assert!(3.1 < foo && foo < 3.2);
        assert_eq!(baz, "BazArg".to_owned());
    }

    #[test]
    fn multiple_char_keys_same_types() {
        let (bar, foo, baz): (bool, bool, bool) = {
                let mut x = Smargs::<(bool, bool, bool)>::new("Test program");
                for (desc, keys, kind) in [
                    ("Bar" , vec!["f", "o", "bar"], SmargKind::Flag),
                    ("Foo" , vec!["b", "a", "r", "foo"], SmargKind::Flag),
                    ("Baz" , vec!["z", "baz"], SmargKind::Flag),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a --foo -f".split(' ').map(String::from))
            .unwrap();
        assert!(bar);
        assert!(foo);
        assert!(!baz);

        let (bar, foo, baz): (usize, usize, usize) = {
                let mut x = Smargs::<(usize, usize, usize)>::new("Test program");
                for (desc, keys, kind) in [
                    ("Bar" , vec!["f", "o", "bar"], SmargKind::Optional("42")),
                    ("Foo" , vec!["b", "a", "r", "foo"], SmargKind::Optional("3")),
                    ("Baz" , vec![], SmargKind::Required),
                ]
                {
                    x.push(Smarg { desc, keys, kind });
                }
                x
            }
            .parse("a 123 --bar 666".split(' ').map(String::from))
            .unwrap();
        assert_eq!(bar, 666);
        assert_eq!(foo, 3);
        assert_eq!(baz, 123);
    }

    #[test]
    fn error_on_empty() {
        let x = {
            let mut x = Smargs::<(bool, bool)>::new("Test program");
            for (desc, keys, kind) in [
                ("Foo" , vec!["f"], SmargKind::Flag),
                ("Bar" , vec!["b"], SmargKind::Flag),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };
        match x
            .parse(std::iter::empty())
            .unwrap_err()
        {
            Error::Empty => {}
            e => panic!("Expected {:?} got {:?}", Error::Empty, e),
        }
    }

    #[test]
    fn missing_value_at_end() {
        let x = {
            let mut x = Smargs::<(String, usize, usize)>::new("Test program");
            for (desc, keys, kind) in [
                ("Foo" , vec![], SmargKind::Required),
                ("Bar" , vec!["d"], SmargKind::Required),
                ("Baz" , vec!["a"], SmargKind::Required),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };

        match x
            .parse("a \"moth man\" -a 41 -d".split(' ').map(String::from))
            .unwrap_err()
        {
            Error::Smarg {
                printable_arg: _,
                kind: ErrorKind::MissingValue,
            } => {}
            e => panic!("Expected {:?} got {:?}", ErrorKind::MissingValue, e),
        }
    }

    #[test]
    fn not_enough_required_args_option() {
        let x = {
            let mut x = Smargs::<(bool, String, String, usize)>::new("Test program");
            for (desc, keys, kind) in [
                ("Foo" , vec!["foo"], SmargKind::Flag),
                ("A required arg" , vec![], SmargKind::Required),
                ("Bar" , vec!["b"], SmargKind::Optional("Barbar")),
                ("Baz" , vec!["z", "baz"], SmargKind::Required),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };
        match x
            .parse("a --baz 42".split(' ').map(String::from))
            .unwrap_err()
        {
            Error::MissingRequired { expected: 2 } => {}
            e => panic!(
                "Expected {:?} got {:?}",
                Error::MissingRequired { expected: 2 },
                e
            ),
        }
    }

    #[test]
    fn not_enough_required_args_position() {
        let x = {
            let mut x = Smargs::<(bool, String, String, usize)>::new("Test program");

            for (desc, keys, kind) in [
                ("Foo", vec!["foo"], SmargKind::Flag),
                ("A required arg", vec![], SmargKind::Required),
                ("Bar", vec!["b"], SmargKind::Optional("Barbar")),
                ("Baz", vec!["z", "baz"], SmargKind::Required),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };
        match x
            .parse("a Required".split(' ').map(String::from))
            .unwrap_err()
        {
            Error::MissingRequired { expected: 2 } => {}
            e => panic!(
                "Expected {:?} got {:?}",
                Error::MissingRequired { expected: 2 },
                e
            ),
        }
    }

    #[test]
    fn undefined_key_in_input() {
        let x = {
            let mut x = Smargs::<(bool, bool)>::new("Test program");
            for (desc, keys, kind) in [
                ("Foo" , vec!["foo"], SmargKind::Flag),
                ("Bar" , vec!["bar"], SmargKind::Flag),
            ]
            {
                x.push(Smarg { desc, keys, kind });
            }
            x
        };
        match x
            .parse("a --baz".split(' ').map(String::from))
            .unwrap_err()
        {
            Error::UndefinedKey(s) if s == "baz" => {}
            e => panic!(
                "Expected {:?} got {:?}",
                Error::UndefinedKey("baz".to_owned()),
                e
            ),
        }
    }
}
