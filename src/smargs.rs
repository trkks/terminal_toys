use std::collections::HashMap;
use std::error;
use std::fmt;
use std::iter;
use std::str::FromStr;
use std::convert::TryFrom;


/// Error type for getting and parsing the values of arguments.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Empty,
    Duplicate(String),
    Parsing(String),
    Position(usize),
    Required(usize, Vec<String>),
}

/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::Empty => String::from("No arguments found"),
            // TODO impl Display for Token
            Self::Duplicate(s) => format!("Duplicate entry of '{}'", s),
            Self::Parsing(s) => format!("Failed to parse: {}", s),
            Self::Position(i) => format!("Argument index {} out of bounds for required type", i),
            Self::Required(i, keys) => format!("This argument is required: position {}, keys {:?}", i, keys),
        };
        write!(f, "{}", msg)
    }
}

impl error::Error for Error {}

/// A mapping from keys to indices to strings:
/// > ArgMap[Key] == Index -> ArgMap[Index] == String
/// Key-value pairs are roughly based on the rough syntax:
/// > Key := -Alph Value | --Alph Value
/// Value is a superset of Alph, which means is not always clear when a string
/// is a key or a value. This means, that some strings meant as values for
/// example "--my-username--" will be presented as being keys. However for
/// example "-42" is strictly considered a value.
struct ArgMap {
    list: Vec<Option<String>>,
    dict: HashMap<String, usize>,
}

impl ArgMap {
    /// Collect the strings in `args` into a list and map ones that __might__
    /// be keys to __their__ corresponding index in said list.
    fn new(
        args: impl Iterator<Item = String>,
    ) -> Result<ArgMap, Error> {
        // "Normalized" representation of the original arguments.
        // The bool represents if the argument is an option, which needs to be
        // added to the dict.
        let list: Vec<(bool, String)> = args
            // Ignore the executable.
            .skip(1)
            // Remove the cli-syntax off of keys and normalize the
            // multi-character groups.
            .fold(Vec::new(), |mut acc, s| {
                let n = Self::key_prefix_len(&s);
                if n == 1 {
                    // Multi-character group.
                    acc.extend(
                        s.chars().skip(1).map(|c| (true, c.to_string()))
                    );
                } else {
                    acc.push((n > 0, s.chars().skip(n).collect()));
                }
                acc
            });

        if list.is_empty() { return Err(Error::Empty) }

        // TODO This could be snappier as a `Result.collect()`, but couldn't
        // figure it out.
        // Save handles to the list's indices for all options.
        let mut dict = HashMap::with_capacity(list.len());
        for (key, value)
            in list.iter()
                .enumerate()
                .filter_map(|(i, (is_option, s))| is_option.then_some((s, i)))
        {
            // Insert into dict and Err if key was already found.
            if let Some(_) = dict.insert(key.clone(), value) {
                // TODO Earlier, a clone wasn't needed here...
                return Err(Error::Duplicate(key.clone()))
            }
        }

        Ok(ArgMap {
            list: list.into_iter().map(|(_, s)| Some(s)).collect(),
            dict
        })
    }

    fn key_prefix_len(s: &str) -> usize {
        let prefix_len = s.chars().take(2).take_while(|c| *c == '-').count();
        if let Some(fst_char_of_key) = s.chars().skip(prefix_len).next() {
            if !fst_char_of_key.is_ascii_digit() {
                return prefix_len
            }
        }
        0
    }

    /// Find, return and replace with `None` the __first__ matching "token"
    /// based on some keys.
    fn pop(&mut self, keys: &[String]) -> Option<(usize, String)> {
        match keys.iter().find_map(|key| self.dict.get(key)) {
            Some(&i) if i < self.list.len() => {
                let token = self.list[i].take().unwrap();
                Some((i, token))
            },
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Smarg {
    keys: Vec<String>,
    kind: SmargKind,
}

#[derive(Debug)]
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
/// Here the execution of a program is guided by command-line arguments in
/// order to create the string `(foo bar, foo bar, foo bar)`.
/// ```
/// # fn main() -> Result<(), String> {
/// use terminal_toys::{Smargs, ArgType};
/// let (n, s, verbose) : (usize, String, bool) =
///     Smargs::builder("Tupletize!")
///         .required(Some((&[], &["amount"])), "Amount of items in the tuple")
///         .required(None, "The string to repeat")
///         .optional(Some((&['v'], &[])), "Print information about the result", ArgType::False)
///         .parse(
///             vec!["tupletize.exe", "-v", "--amount", "3", "foo bar"]
///                 .into_iter().map(String::from)
///         )
///         .map_err(|e| format!("Argument failure: {}", e))?;
///
/// let result = format!("({})", vec![s.clone(); n].join(", "));
///
/// if verbose {
///     println!("Character count: {}", result.len()); // Character count: 27
/// }
///
/// assert_eq!(result, "(foo bar, foo bar, foo bar)".to_owned());
/// # Ok(()) }
/// ```
/// Or with just ordered arguments and the verbose flag defaulted to `true`:
/// ```
/// use terminal_toys::{Smargs, ArgType};
/// let (n, s, verbose) : (usize, String, bool) =
///     Smargs::builder("Tupletize!")
///         .required(Some((&[], &["amount"])), "Amount of items in the tuple")
///         .required(None, "The string to repeat")
///         .optional(Some((&['v'], &[])), "Print information about the result", ArgType::False)
///         .parse(
///             vec!["tupletize.exe", "3", "foo bar"].into_iter().map(String::from)
///         )
///         .unwrap();
/// assert_eq!(n, 3);
/// assert_eq!(s, "foo bar");
/// assert!(!verbose);
/// ```
#[derive(Debug)]
pub struct Smargs {
    defins: Vec<Smarg>,
    values: Vec<Option<String>>,
}

impl Smargs {
    /// Start a builder defining the order, keys and description of a program
    /// and its arguments.
    ///
    /// `description` is the general description of the program.
    pub fn builder(description: &str) -> Self {
        Self { defins: Vec::new(), values: Vec::new() }
    }

    /// Define next an argument which __needs__ to be provided by the user.
    pub fn required(
        mut self,
        keys: Option<(&[char], &[&str])>,
        description: &str,
    ) -> Self {
        self.push_arg(keys, description, SmargKind::Required);
        self
    }

    /// Define next an argument with a default value that will be used if
    /// nothing is provided by the user.
    ///
    /// A boolean argument defaults to FALSE because using a flag essentially
    /// means signaling the event of or __turning on__ something, certainly not
    /// the contrary.
    pub fn optional(
        mut self,
        keys: Option<(&[char], &[&str])>,
        description: &str,
        default: ArgType,
    ) -> Self {
        let kind = match default {
            ArgType::False    => SmargKind::Flag,
            ArgType::Other(s) => SmargKind::Optional(s.to_owned()),
        };
        self.push_arg(keys, description, kind);
        self
    }

    /// Parse the argument strings into the type `T` according to the
    /// definition of `self` which may include default values for some.
    pub fn parse<T>(
        mut self,
        args: impl Iterator<Item=String>,
    ) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error=Error>,
   {
        let mut am = ArgMap::new(args)?;

        // First, fill correct indices based on keys.
        self.resolve_kv_pairs(&mut am);

        // Replace all the rest in order after the options are filtered out.
        for (x, y) in iter::zip(
            self.values.iter_mut().filter(|x| x.is_none()),
            am  .list  .iter_mut().filter(|x| x.is_some()),
        ) {
            x.replace(y.take().unwrap());
        }

        // TODO Instead of parsing into the values here, maybe return some
        // abstraction like "IntermediateElemT_i" or "FakeT_i" (or perhaps
        // `std::any::Any`?) that could be used to identify the boolean at
        // runtime(?) (and thus get rid of ArgType::False).
        T::try_from(self)
    }

    fn resolve_kv_pairs(&mut self, am: &mut ArgMap) {
        self.values = self.defins.iter()
            .map(|Smarg { keys, kind }|
                // TODO Somehow despookify this if?
                // TODO This sort of indexing makes it feel like ArgMap is
                // useless: how much better can the dict be compared to
                // linearly searching for the key-string?
                if let Some((key_idx, _)) = am.pop(keys) {
                    if let SmargKind::Flag = kind {
                        Some(true.to_string())
                    } else {
                        // Take the following value.
                        Some(am.list[key_idx + 1].take().unwrap())
                    }
                } else {
                    // Flags default to false here if a match is not found.
                    if let SmargKind::Flag = kind {
                        Some(false.to_string())
                    } else {
                        None
                    }
                }
            )
            .collect();
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env<T>(self) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error=Error>,
    {
        self.parse(std::env::args())
    }

    /// Perform common operations for defining an argument in order
    /// and TODO: generate a user-friendly description for it.
    fn push_arg(
        &mut self,
        keys: Option<(&[char], &[&str])>,
        description: &str,
        kind: SmargKind,
    ) {
        let keys = if let Some((cs, ss)) = keys {
            iter::once(cs.iter().collect::<String>())
                .chain(ss.iter().map(|y| y.to_string()))
                .collect()
        } else {
            Vec::new()
        };

        self.defins.push(Smarg { keys, kind });
    }

    fn parse_nth<T>(&mut self, index: usize) -> Result<T, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: error::Error,
    {
        self.values.get_mut(index)
            .expect(&format!("Smargs.values constructed incorrectly: None in index {}", index))
            .take()
            .ok_or(Error::Position(index))?
            .parse()
            .map_err(
                |e: <T as FromStr>::Err| Error::Parsing(
                    format!("#{} {}", index, e.to_string())
                )
            )
    }
}

impl<T1, T2> TryFrom<Smargs> for (T1, T2)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
{
    type Error = Error;
    fn try_from(mut smargs: Smargs) -> Result<Self, Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
        ))
    }
}

impl<T1, T2, T3> TryFrom<Smargs> for (T1, T2, T3)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error,
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
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error,
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
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error,
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

impl<T1, T2, T3, T4, T5, T6, T7, T8> TryFrom<Smargs> for (T1, T2, T3, T4, T5, T6, T7, T8)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error,
    T4: FromStr,
    <T4 as FromStr>::Err: error::Error,
    T5: FromStr,
    <T5 as FromStr>::Err: error::Error,
    T6: FromStr,
    <T6 as FromStr>::Err: error::Error,
    T7: FromStr,
    <T7 as FromStr>::Err: error::Error,
    T8: FromStr,
    <T8 as FromStr>::Err: error::Error,
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
    use super::{Smargs, ArgMap, Error, ArgType};

    #[test]
    fn argmap_use_case() {
        let am = ArgMap::new(
            "scale_img.exe ./img.png -v -w 1366 -h -768 --output scaled.png"
                .split(' ')
                .map(String::from)
            )
            .unwrap();

        assert_eq!(am.dict.len(), 4);
        assert_eq!(am.dict["v"], 1);
        assert_eq!(am.dict["w"], 2);
        assert_eq!(am.dict["h"], 4);
        assert_eq!(am.dict["output"], 6);
    }

    #[test]
    fn general_use_case() {
        use std::path::PathBuf;

        let (a1, a2, a3, a4, a5) :
            (PathBuf, u32, u32, bool, PathBuf) =
            Smargs::builder("A program to scale an image")
            .required(None, "Path to the image")
            .required(Some((&['w'], &["width"])), "The width to scale into")
            .required(Some((&['h'], &["height"])), "The height to scale into")
            .optional(
                Some((&['v'], &["verbose"])),
                "Print realtime status of operations",
                ArgType::False,
            )
            .optional(Some((&['o'], &["output"])), "Output path", ArgType::Other("a"))
            .parse(
                "scale_img.exe -v ./img.png -w 1366 -h 768 --output scaled.png"
                .split(' ').map(String::from)
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
        let (a1, a2) : (bool, String) =
            Smargs::builder("Compute P AND NOT Q from a bool and a string")
                .optional(Some((&['b'], &["bool"])), "A bool", ArgType::False)
                .required(None, "A string representing another bool")
                .parse("a -b false".split(' ').map(String::from))
                .unwrap();

        // True AND NOT False
        let computation = a1 && !a2.parse::<bool>().unwrap();

        assert!(computation);
    }

    #[test]
    fn error_on_duplicates() {
        // Catch the __first__ duplicate that appears from left to right.

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&['f'], &[])), "Foo", ArgType::False)
            .optional(Some((&['b'], &[])), "Bar", ArgType::False)
            .parse::<(bool, bool)>("a -fbfb".split(' ').map(String::from))
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("f".to_owned())
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&[], &["foo"])), "Foo", ArgType::False)
            .optional(Some((&[], &["bar"])), "Bar", ArgType::False)
            .parse::<(bool, bool)>(
                "a --foo --foo --bar --bar".split(' ').map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("foo".to_owned()),
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&['f'], &[])), "Foo", ArgType::False)
            .optional(Some((&['b'], &[])), "Bar", ArgType::False)
            .optional(Some((&[], &["baz"])), "Baz", ArgType::False)
            .parse::<(bool, bool, bool)>(
                "a -fb --baz -bf --baz".split(' ').map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("b".to_owned()),
        );
    }

    #[test]
    fn multi_character_option() {
        let (b, a, r, bar) :
            (bool, bool, String, bool) =
            Smargs::builder("Test program")
            .optional(Some((&['b'], &[])), "Bee", ArgType::False)
            .optional(Some((&['a'], &[])), "Ay", ArgType::False)
            .optional(Some((&['r'], &[])), "Are", ArgType::Other("some-default"))
            .optional(Some((&[], &["bar"])), "Bar", ArgType::False)
            .parse("a -bar r-arg-value --bar".split(' ').map(String::from))
            .unwrap();
        assert!(b);
        assert!(a);
        assert_eq!(r, "r-arg-value");
        assert!(bar);

        let (b, a, r, verbose, f) :
            (bool, bool, bool, bool, f32) =
            Smargs::builder("Test program")
            .optional(Some((&['b'], &[])), "Bee", ArgType::False)
            .optional(Some((&['a'], &[])), "Ay", ArgType::False)
            .optional(Some((&['r'], &[])), "Are", ArgType::False)
            .optional(Some((&[], &["verbose"])), "Verbose", ArgType::False)
            .optional(Some((&['f'], &[])), "Foo", ArgType::Other("666"))
            .parse("a -bar --verbose -f 4.2".split(' ').map(String::from))
            .unwrap();
        assert!(a);
        assert!(b);
        assert!(r);
        assert!(verbose);
        assert_eq!(f, 4.2);
    }


    #[test]
    fn error_on_empty() {
        let err_empty = Smargs::builder("Test program")
            .optional(Some((&['f'], &[])), "Foo", ArgType::False)
            .optional(Some((&['b'], &[])), "Bar", ArgType::False)
            .parse::<(bool, bool)>(std::iter::empty())
            .unwrap_err();
        assert_eq!(err_empty, Error::Empty);
    }
}
