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
    list: Vec<String>,
    dict: HashMap<String, usize>,
}

impl ArgMap {
    /// Collect the strings in `args` into a list and map ones that __might__
    /// be keys to their corresponding value's index in said list.
    fn new(
        args: impl Iterator<Item = String>,
    ) -> Result<ArgMap, Error> {
        // Contains the original arguments as is.
        let list: Vec<String> = args.collect();
        if list.is_empty() { return Err(Error::Empty) }

        // Get all the (possible) key-value pairs of the argument list.
        // TODO This could be snappier as an `iterator.collect()`, but couldn't
        // figure it out.
        let mut dict = HashMap::with_capacity(list.len());
        for (key, value) in list.iter()
            // Enumerate to save a handle to original list index.
            .enumerate()
            // Skip the executable. The 0-index is special.
            .skip(1)
            // Remove now unneeded values from inbetween and calculate the
            // correct index handle (out of bounds wraps to 0).
            .filter_map(|(i, s)| match Self::key_prefix_len(s) {
                0 => None,
                n => Some(((i + 1) % list.len(), s, n)),
            })
            // Remove the cli-syntax off of keys and handle the possibility of
            // multi-character groups.
            .fold(Vec::with_capacity(list.len()), |mut acc, (i, s, n)| {
                if n == 1 {
                    // Handle the possibility of multi-character group.
                    acc.extend(
                        s.chars()
                            .skip(1)
                            .map(|c| (c.to_string(), i))
                    );
                } else {
                    acc.push((s.chars().skip(n).collect(), i));
                }
                acc
            })
        {
            // Insert into dict and Err if key was already found.
            if let Some(_) = dict.insert(key.clone(), value) {
                return Err(Error::Duplicate(key))
            }
        }

        Ok(ArgMap { list, dict })
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

    /// Return the first matching "token" based on some keys.
    fn get(&self, keys: &[String]) -> Option<&String> {
        keys.iter()
            .find_map(|key|
                self.dict
                    .get(key)
                    .map(|&i| self.list.get(i))
                    .flatten()
            )
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
}

#[derive(Debug)]
pub struct StringVec(Vec<String>);

// TODO Parse options from some parameters eg. [Bool("-v", "--verbose", "Print
// detailed information"), OsPath("-p", "--path", "Path to source file"), ...]
// smargs = Smargs::new(options_list, env::args())
/// SiMpler thAn wRiting it once aGain Surely :)
/// PlaceS strings received froM std::env::ARGS into Suitable structures for
/// straightforward operation of flags, ordered and naMed ARGumentS.
///
/// # Example:
/// ```
/// use terminal_toys::smargs::{Smargs, SmargError as Se};
/// use std::error;
///
/// fn get_args(
///     smargs: &Smargs,
/// ) -> Result<(String, usize), Box<dyn error::Error>> {
///     Ok((smargs.last()?, smargs.gets(&["amount", "a"])?))
/// }
///
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe -v --amount 3 foo".split(' ').map(String::from)
/// ).unwrap();
///
/// let (target, n) = match get_args(&smargs) {
///     Err(e) => panic!("Argument failure: {}", e),
///     Ok(x)  => x,
/// };
///
/// let mut result = String::from("()");
/// if n > 0 {
///     result = format!("({})", vec![target.clone(); n].join(", "));
///
///     if smargs.has("v") {
///         // Prints: "tupletize.exe: Result is 15 characters"
///         println!(
///             "{}: Result is {} characters",
///             smargs.exe(), result.len()
///         );
///     }
/// }
///
/// assert_eq!(result, "(foo, foo, foo)");
/// ```
/// Or with just ordered arguments:
/// ```
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe 3 foo -v".split(' ').map(String::from)
/// ).unwrap();
/// match &smargs[..2] {
///     []  => { /* Print instructions */ },
///     [n] => { /* ... */},
///     [n, target, ..] => {
///         assert_eq!(n, "3");
///         assert_eq!(target, "foo");
///         // ...
///     },
/// }
/// ```
#[derive(Debug)]
pub struct Smargs {
    defins: Vec<Smarg>,
    values: StringVec,
}

impl Smargs {
    /// TODO
    pub fn builder(description: &str) -> Self {
        Self { defins: Vec::new(), values: StringVec(Vec::new()) }
    }

    /// TODO
    pub fn required(
        mut self,
        keys: Option<(&[char], &[&str])>,
        description: &str,
    ) -> Self {
        let keys = if let Some((cs, ss)) = keys {
            iter::once(cs.iter().collect::<String>())
                .chain(ss.iter().map(|y| y.to_string()))
                .collect()
        } else {
            Vec::new()
        };

        self.defins.push(Smarg { keys, kind: SmargKind::Required });

        self
    }

    /// TODO
    pub fn optional(
        mut self,
        keys: Option<(&[char], &[&str])>,
        description: &str,
        default: &str,
    ) -> Self {
        let keys = if let Some((cs, ss)) = keys {
            iter::once(cs.iter().collect::<String>())
                .chain(ss.iter().map(|y| y.to_string()))
                .collect()
        } else {
            Vec::new()
        };

        self.defins.push(Smarg { keys, kind: SmargKind::Optional(default.to_owned()) });

        self
    }

    /// Parse the argument strings into the type `T` according to the
    /// definition of `self`.
    pub fn parse<T>(
        mut self,
        args: impl Iterator<Item=String>,
    ) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error=Error>,
    {
        let am = ArgMap::new(args)?;

        for (i, Smarg { keys, kind }) in self.defins.iter().enumerate() {
            // Try to find a matching value from args.
            self.values.0.push(
                if let Some(value) = am.get(keys).or(am.list.get(i + 1)) {
                    value.clone()
                } else {
                    match kind {
                        SmargKind::Required => return Err(
                            Error::Required(i, keys.clone())
                        ),
                        SmargKind::Optional(default) => default.clone(),
                    }
                }
            );
        }

        T::try_from(self)
    }

    /// Creates `T` based on a call to `std::env::args`.
    pub fn from_env<T>(self) -> Result<T, Error>
    where
        T: TryFrom<Smargs, Error=Error>,
    {
        self.parse(std::env::args())
    }

    fn parse_nth<T>(&self, index: usize) -> Result<T, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: error::Error,
    {
        self.values.0
            .get(index)
            .ok_or(Error::Position(index))?
            .parse()
            .or_else(|first_err: <T as FromStr>::Err|
                // Assume that T is bool because the earlier argument mapping
                // was and is unable to differentiate between key-value and
                // flag -options.
                true.to_string()
                    .parse()
                    // Guessing the type was wrong so return the initial error.
                    .map_err(|_| Error::Parsing(first_err.to_string()))
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
    fn try_from(smargs: Smargs) -> Result<Self, Error> {
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
    fn try_from(smargs: Smargs) -> Result<Self, Error> {
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
    fn try_from(smargs: Smargs) -> Result<Self, Error> {
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
    fn try_from(smargs: Smargs) -> Result<Self, Error> {
        Ok((
            smargs.parse_nth(0)?,
            smargs.parse_nth(1)?,
            smargs.parse_nth(2)?,
            smargs.parse_nth(3)?,
            smargs.parse_nth(4)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::{Smargs, ArgMap, Error};

    #[test]
    fn argmap_use_case() {
        let am = ArgMap::new(
            "scale_img.exe ./img.png -v -w 1366 -h -768 --output scaled.png"
                .split(' ')
                .map(String::from)
            )
            .unwrap();

        assert_eq!(am.dict.len(), 4);
        assert_eq!(am.dict["v"], 3);
        assert_eq!(am.dict["w"], 4);
        assert_eq!(am.dict["h"], 6);
        assert_eq!(am.dict["output"], 8);
    }

    #[test]
    fn general_use_case() {
        use std::path::PathBuf;

        let (a1, a2, a3, a4, a5) :
            (PathBuf, u32, u32, PathBuf, bool) =
            Smargs::builder("A program to scale an image")
            .required(None, "Path to the image")
            .required(Some((&['w'], &["width"])), "The width to scale into")
            .required(Some((&['h'], &["height"])), "The height to scale into")
            .optional(Some((&['o'], &["output"])), "Output path", "a")
            .optional(
                Some((&['v'], &["verbose"])),
                "Print realtime status of operations",
                &true.to_string()
            )
            .parse(
                "scale_img.exe ./img.png -v -w 1366 -h 768 --output scaled.png"
                .split(' ').map(String::from)
            )
            .unwrap();

        assert_eq!(a1, "./img.png".parse::<PathBuf>().unwrap());
        assert_eq!(a2, 1366);
        assert_eq!(a3, 768);
        assert_eq!(a4, "scaled.png".parse::<PathBuf>().unwrap());
        assert!(a5);
    }

    #[test]
    fn error_on_duplicates() {
        // Catch the __first__ duplicate that appears from left to right.

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&['f'], &[])), "Foo", &false.to_string())
            .optional(Some((&['b'], &[])), "Bar", &true.to_string())
            .parse::<(bool, bool)>("a -fbfb".split(' ').map(String::from))
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("f".to_owned())
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&[], &["foo"])), "Foo", &false.to_string())
            .optional(Some((&[], &["bar"])), "Bar", &true.to_string())
            .parse::<(bool, bool)>(
                "a --foo --foo --bar --bar".split(' ').map(String::from)
            )
            .unwrap_err();
        assert_eq!(
            err_duplicate,
            Error::Duplicate("foo".to_owned()),
        );

        let err_duplicate = Smargs::builder("Test program")
            .optional(Some((&['f'], &[])), "Foo", &false.to_string())
            .optional(Some((&['b'], &[])), "Bar", &true.to_string())
            .optional(Some((&[], &["baz"])), "Baz", &true.to_string())
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
            .optional(Some((&['b'], &[])), "Bee", &false.to_string())
            .optional(Some((&['a'], &[])), "Ay", &false.to_string())
            .optional(Some((&['r'], &[])), "Are", "some-default")
            .optional(Some((&[], &["bar"])), "Bar", &false.to_string())
            .parse("a -bar r-arg-value --bar".split(' ').map(String::from))
            .unwrap();
        assert!(b);
        assert!(a);
        assert_eq!(r, "r-arg-value");
        assert!(bar);

        let (b, a, r, verbose, f) :
            (bool, bool, bool, bool, f32) =
            Smargs::builder("Test program")
            .optional(Some((&['b'], &[])), "Bee", &false.to_string())
            .optional(Some((&['a'], &[])), "Ay", &false.to_string())
            .optional(Some((&['r'], &[])), "Are", &false.to_string())
            .optional(Some((&[], &["verbose"])), "Verbose", &false.to_string())
            .optional(Some((&['f'], &[])), "Foo", "666")
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
            .optional(Some((&['f'], &[])), "Foo", &false.to_string())
            .optional(Some((&['b'], &[])), "Bar", &true.to_string())
            .parse::<(bool, bool)>(std::iter::empty())
            .unwrap_err();
        assert_eq!(err_empty, Error::Empty);
    }
}
