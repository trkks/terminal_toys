use std::collections::HashMap;
use std::iter;
use std::ops;
use std::str;
use std::fmt;


/// Error type for `Smargs`'s constructors.
///
/// `SmargsError::Duplicate` can be used to tell the caller which argument was
/// a duplicate and its token-type.
#[derive(Debug, PartialEq)]
pub enum SmargsError {
    Empty,
    Duplicate(Token),
}


/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for SmargsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::Empty => String::from("No arguments found"),
            // TODO impl Display for Token
            Self::Duplicate(t) => format!("Duplicate entry of {:?}", t),
        };
        write!(f, "{}", msg)
    }
}


/// Error type for getting and parsing the values of arguments.
pub enum CollectError<T>
where
    T: str::FromStr,
    <T as str::FromStr>::Err: fmt::Debug,
{
    NotFound { flags: Vec<char>, words: Vec<String> },
    ParseError(<T as str::FromStr>::Err),
}
impl<T> CollectError<T>
where
    T: str::FromStr,
    <T as str::FromStr>::Err: fmt::Debug,
{
    /// Create the NotFound-variant based on the argument keys passed in.
    /// `CollectError` uses this function in creating a better error message.
    ///
    /// Example:
    /// ```
    /// use terminal_toys::smargs::{Smargs, CollectError as Ce};
    /// let smargs = Smargs::new(
    ///         "foo.exe -bar --baz".split(' ').map(String::from)
    ///     ).unwrap();
    /// let notfound_err_msg = smargs.gets::<i32>(&["output", "out", "o"])
    ///     .unwrap_err()
    ///     .to_string();
    /// assert!(notfound_err_msg.contains("output"));
    /// assert!(notfound_err_msg.contains("out"));
    /// assert!(notfound_err_msg.contains("o"));
    /// // TODO Position of the argument (in the order of the gets-query?).
    /// ```
    fn not_found(keys: &[&str]) -> Self {
        let mut words = Vec::new();
        let mut flags = Vec::new();
        // TODO Could allocations be reduced by passing keys intelligentler?
        for key in keys {
            if key.len() == 1 {
                flags.push(key.chars().next().unwrap());
            } else if key.len() > 1 {
                words.push(String::from(*key));
            }
        }
        Self::NotFound { words, flags }
    }
}



/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl<T> fmt::Display for CollectError<T>
where
    T: str::FromStr,
    <T as str::FromStr>::Err: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::NotFound { flags, words } => format!(
                    "Option not found {}{}",
                    flags.iter()
                        .map(|c| format!(" -{}", c))
                        .collect::<String>(),
                    words.iter()
                        .map(|s| format!(" --{}", s))
                        .collect::<String>(),
                ),
            Self::ParseError(err) => format!("Bad format: {:?}", err),
        };
        write!(f, "{}", msg)
    }
}


/// Makes handling the args -strings a bit clearer
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Value(String),
    Flag(char),
    Word(String),
}


// TODO Parse options from some parameters eg. [Bool("-v", "--verbose", "Print
// detailed information"), OsPath("-p", "--path", "Path to source file"), ...]
// smargs = Smargs::new(options_list, env::args())
/// SiMpler thAn wRiting it once aGain Surely :)
/// PlaceS strings received froM std::env::ARGS into Suitable structures for
/// straightforward operation of flags, ordered and naMed ARGumentS.
///
/// # Example:
/// ```
/// use terminal_toys::smargs::{Smargs, CollectError as Ce};
///
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe -v --amount 3 foo".split(' ').map(String::from)
/// ).unwrap();
///
/// let target = smargs.last().expect("Specify target as the last argument");
/// let n: usize = match smargs.gets(&["amount", "a"]) {
///     Err(Ce::NotFound { .. }) => panic!("Missing argument"),
///     Err(Ce::ParseError(e))   => panic!("Failed to parse: {:?}", e),
///     Ok(m) => m,
/// };
/// let mut result = String::from("()");
/// if n > 0 {
///     result = format!("({})", vec![String::from(target); n].join(", "));
///
///     if smargs.has("v") {
///         // Prints: "tupletize.exe: Result is 15 characters"
///         println!("{}: Result is {} characters", smargs.exe(), result.len());
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
#[derive(Debug, PartialEq, Eq)]
pub struct Smargs {
    exe: String,
    list: Vec<String>,
    dict: HashMap<String, usize>,
}
impl Smargs {
    pub fn new(
        mut args: impl Iterator<Item = String>,
    ) -> Result<Self, SmargsError> {
        let exe = args.next().ok_or(SmargsError::Empty)?;

        // Contains the original arguments without empty ones
        // TODO parse into typed enums
        let list: Vec<String> =
            args.filter_map(|x| {
                    let xx = String::from(x.trim());
                    if xx.is_empty() { None } else { Some(xx) }
                })
                // Hide a "boolean" to last index
                .chain(iter::once(true.to_string()))
                .collect();

        // Tokenize and enumerate with original indices (ie. flag groups like
        // "-bar" count as one index)
        // NOTE that the added boolean in last index is also tokenized so that
        // the next dict-loop wraps up nicely
        let mut tokens = Vec::with_capacity(list.len());
        for (i, s) in list.iter().enumerate() {
            if s.starts_with("--") {
                tokens.push(
                    (i, Token::Word(s.chars().skip(2).collect()))
                );
            } else if s.starts_with("-") {
                // Possible flag group
                tokens.extend(
                    s.chars()
                        .skip(1)
                        .map(|c| (i, Token::Flag(c)))
                );
            } else {
                tokens.push(
                    (i, Token::Value(String::from(s)))
                );
            }
        }

        let mut dict = HashMap::with_capacity(tokens.len());
        // Emulate old school for-loop because Rust is so expressive /s
        let mut i = 0;
        while i < tokens.len().saturating_sub(1) {
            let current_token = &tokens[i].1;
            let (k, next_token) = &tokens[i + 1];

            // Check if left side of pair is a key
            let kv_opt = match current_token {
                Token::Flag(chr) => Some(chr.to_string()),
                Token::Word(s)   => Some(s.clone()),
                _ => None,
            }
            // If it was, it will map to a value in resulting dict
            .zip(Some(
                if let Token::Value(_) = next_token {
                    // Do not check if this Value is a key next iteration
                    // This is literally the only reason for not using for-loop
                    i += 1;
                    // Point at the following Value in the original list
                    *k
                } else {
                    // Key without following value points to the boolean
                    list.len() - 1
                }
            ));

            // Insert into dict and Err if key was already found
            if let Some((key, value)) = kv_opt {
                if let Some(_value) = dict.insert(key, value) {
                    return Err(
                        SmargsError::Duplicate(current_token.clone())
                    )
                }
            }

            i += 1;
        }

        Ok(Smargs { list, dict, exe })
    }

    /// Creates `Smargs` from a call to `std::env::args`.
    pub fn from_env() -> Result<Self, SmargsError> {
        Self::new(std::env::args())
    }

    pub fn exe(&self) -> &String {
        &self.exe
    }

    pub fn len(&self) -> usize {
        // Do not include the "boolean" at the end
        &self.list.len() - 1
    }

    pub fn first(&self) -> Option<&String> {
        // Do not include the "boolean" at the end
        self.list[..self.list.len() - 1].first()
    }

    pub fn last(&self) -> Option<&String> {
        // Do not include the "boolean" at the end
        self.list[..self.list.len() - 1].last()
    }

    /// Return the matching value based on a list of keys.
    // TODO Also keep a record of the order of calls to this (see
    // GetsError::not_found) -> which would need the values to be removed from
    // the smargs-instance.
    pub fn gets<T>(&self, keys: &[&str]) -> Result<T, CollectError<T>>
    where
        T: str::FromStr,
        <T as str::FromStr>::Err: fmt::Debug,
    {
        for &key in keys {
            if let Some(s)
                = self.dict.get(key)
                    .map(|&i| self.list.get(i))
                    .flatten()
            {
                return s.parse::<T>().map_err(|e| CollectError::ParseError(e))
            }
        }
        return Err(CollectError::not_found(keys))
    }

    pub fn has(&self, key: &str) -> bool {
        self.dict.contains_key(key)
    }
}

impl ops::Index<&str> for Smargs {
    type Output = String;
    fn index(&self, key: &str) -> &Self::Output {
        &self.list[self.dict[key]]
    }
}

/// NOTE Indexes excluding the executable path; use `Smargs::exe` if it's needed
impl ops::Index<usize> for Smargs {
    type Output = String;
    fn index(&self, user_index: usize) -> &Self::Output {
        // Do not index the "boolean" at the end
        &self.list[0..self.list.len() - 1][user_index]
    }
}

/// NOTE Indexes excluding the executable path; use `Smargs::exe` if it's needed
impl ops::Index<ops::Range<usize>> for Smargs {
    type Output = [String];
    fn index(&self, user_range: ops::Range<usize>) -> &Self::Output {
        // Do not index the "boolean" at the end
        &self.list[0..self.list.len() - 1][user_range]
    }
}

impl ops::Index<ops::RangeFull> for Smargs {
    type Output = [String];
    fn index(&self, _: ops::RangeFull) -> &Self::Output {
        &self[0..self.list.len() - 1]
    }
}

impl ops::Index<ops::RangeFrom<usize>> for Smargs {
    type Output = [String];
    fn index(&self, user_range: ops::RangeFrom<usize>) -> &Self::Output {
        &self[user_range.start..self.list.len() - 1]
    }
}

impl ops::Index<ops::RangeTo<usize>> for Smargs {
    type Output = [String];
    fn index(&self, user_range: ops::RangeTo<usize>) -> &Self::Output {
        &self[0..user_range.end]
    }
}


#[cfg(test)]
mod tests {
    use super::{Smargs, SmargsError, Token};
    #[test]
    fn test_smargs_use_case() {
        let smargs = Smargs::new(
            "scale_img.exe nn --verbose   -w 300 -h 300  --output scaled.png"
                .split(' ').map(String::from)
        ).unwrap();

        let indexable_args = vec![
            "nn", "--verbose", "-w", "300",
            "-h", "300", "--output", "scaled.png",
        ];

        assert_eq!(smargs[0], indexable_args[0]);
        assert_eq!(smargs[1], indexable_args[1]);
        assert_eq!(smargs[2], indexable_args[2]);
        assert_eq!(smargs[3], indexable_args[3]);
        assert_eq!(smargs[4], indexable_args[4]);
        assert_eq!(smargs[5], indexable_args[5]);
        assert_eq!(smargs[6], indexable_args[6]);
        assert_eq!(smargs[7], indexable_args[7]);

        // TODO Is this functionality even useful?
        // Is supporting the original arg-list necessary?
        assert_eq!(smargs[..], smargs[0..]);
        assert_eq!(smargs[0..], smargs[..8]);
        assert_eq!(smargs[..8], smargs[0..8]);
        assert_eq!(smargs[0..8], indexable_args[0..8]);

        assert_eq!(smargs[2..6], indexable_args[2..6]);
        assert_eq!(smargs[3..3], indexable_args[3..3]);

        assert_eq!(smargs["h"], "300");
        assert_eq!(smargs["w"], "300");
        assert_eq!(smargs["output"], "scaled.png");
        assert_eq!(smargs["verbose"], "true");
        assert!(smargs.has("verbose"));
        assert!(!smargs.has("v"));
        assert_eq!(smargs.first(), Some(&smargs[0]));
        assert_eq!(smargs.first(), Some(&String::from("nn")));
        assert_eq!(smargs.last(), Some(&String::from("scaled.png")));
    }

    #[test]
    fn test_smargs_first_last() {
        let args = "foo.exe bar".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        assert_eq!(smargs.first(), Some(&String::from("bar")));
        assert_eq!(smargs.last(), Some(&String::from("bar")));
    }

    #[test]
    fn test_smargs_exe() {
        let args = "foo.exe".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        assert_eq!(smargs.first(), None);
        assert_eq!(smargs.last(), None);
        assert_eq!(smargs.exe(), &String::from("foo.exe"));
    }

    #[test]
    fn test_smargs_duplicates() {
        let args = "some.exe -fofo".split(' ').map(String::from);
        let double_flag = Smargs::new(args);
        // Catch the first duplicate that appears from left to right
        assert_eq!(
            double_flag,
            Err(SmargsError::Duplicate(Token::Flag('f')))
        );

        let args = "some.exe --foo --foo --bar --bar".split(' ')
            .map(String::from);
        let double_word = Smargs::new(args);
        assert_eq!(
            double_word,
            Err(SmargsError::Duplicate(Token::Word(String::from("foo"))))
        );

        let args = "some.exe -fo -of --bar --bar".split(' ')
            .map(String::from);
        let double_flag = Smargs::new(args);
        assert_eq!(
            double_flag,
            Err(SmargsError::Duplicate(Token::Flag('o')))
        );
    }

    #[test]
    fn test_combined_key_value() {
        let args = "some.exe -bar r-arg-value --bar"
            .split(' ')
            .map(String::from);
        let diff_types = Smargs::new(args).unwrap();
        assert_eq!(diff_types["b"].parse::<bool>().unwrap(), true);
        assert_eq!(diff_types["a"].parse::<bool>().unwrap(), true);
        assert_eq!(diff_types["r"], "r-arg-value");
        assert_eq!(diff_types["bar"].parse::<bool>().unwrap(), true);

        let args = "some.exe -bar --verbose -f 4.2"
            .split(' ')
            .map(String::from);
        let multiple = Smargs::new(args).unwrap();
        assert_eq!(multiple["b"].parse::<bool>().unwrap(), true);
        assert_eq!(multiple["a"].parse::<bool>().unwrap(), true);
        assert_eq!(multiple["r"].parse::<bool>().unwrap(), true);
        assert_eq!(multiple["verbose"].parse::<bool>().unwrap(), true);
        assert_eq!(multiple["f"].parse::<f32>().unwrap(), 4.2);
    }


    #[test]
    fn test_smargs_empty() {
        let smargs = Smargs::new(std::iter::empty());
        assert_eq!(smargs, Err(SmargsError::Empty));
    }

    #[test]
    #[should_panic]
    fn test_smargs_empty_key() {
        let args = "some.exe foo".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        let _ = smargs[""];
    }

    #[test]
    #[should_panic]
    fn test_smargs_not_a_key() {
        let args = "some.exe foo bar".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        let _ = smargs["foo"];
    }

    #[test]
    #[should_panic]
    fn test_smargs_index_out_of_bounds() {
        let args = "some.exe foo bar".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        let _ = smargs[2];
    }

    #[test]
    #[should_panic]
    fn test_smargs_range_out_of_bounds() {
        let args = "some.exe foo bar".split(' ').map(String::from);
        let smargs = Smargs::new(args).unwrap();
        let _ = smargs[0..3];
    }
}
