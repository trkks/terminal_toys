use std::collections::HashMap;
use std::iter;
use std::ops;


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
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe -v --amount 3 foo".split(' ').map(String::from)
/// ).unwrap();
///
/// let target = smargs.last().expect("Specify target as the last argument");
/// let n: usize = smargs["amount"].parse().expect("Amount not an integer");
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

        // Tokenize
        let mut tokens = Vec::with_capacity(list.len());
        for s in list.iter().take(list.len() - 1) {
            if s.starts_with("--") {
                tokens.push(Token::Word(s.chars().skip(2).collect()));
            } else if s.starts_with("-") {
                tokens.extend(
                    s.chars()
                        .skip(1)
                        .map(|c| Token::Flag(c))
                );
            } else {
                tokens.push(Token::Value(String::from(s)));
            }
        }
        // Check that no duplicates were added
        for i in 0..tokens.len() {
            // `Value`s can be duplicates
            if let Token::Value(_) = tokens[i] {
                continue;
            }
            for j in i + 1.. tokens.len() {
                if tokens[i] == tokens[j] {
                    return Err(
                        SmargsError::Duplicate(tokens[i].clone())
                    );
                }
            }
        }

        // NOTE HACK to have windows(2) handle every actual arg as "key"
        tokens.push(Token::Flag(0 as char));

        // Enumerate but with original indices ie. combined flags as one item
        // When parsing a pattern like
        //   "exe -bar baz"
        // the offsets refer to the first flag ie.
        // bar+1 == b+0+1 == a+1+1 == r+2+1 == baz)
        let enumeration = tokens.iter()
            .scan((false, 0), |(prev_was_flag, i), x| {
                // Eww c):
                if let Token::Flag(_) = x {
                    if !*prev_was_flag {
                        *prev_was_flag = true;
                        *i += 1;
                    }
                } else {
                    *prev_was_flag = false;
                    *i += 1;
                }
                Some(*i - 1)
            });

        // Figure out the key-value -pairs; Flags and Words without following
        // values point to the true-string (ie. they map to a boolean)
        // TODO Use scan(Some) to remember previous arg and not use windows(2)?
        let dict = enumeration.zip(tokens.windows(2))
            .filter_map(|(i, pair)|
                match &pair[0] {
                    Token::Flag(chr) => Some(chr.to_string()),
                    Token::Word(s)   => Some(s.clone()),
                    _ => None,
                }
                .zip(Some(if let Token::Value(_) = pair[1] {
                    // Point at the following arg, which is the pair's value
                    i + 1
                } else {
                    // Point at the true-string
                    list.len() - 1
                }))
            )
            .inspect(|x| println!("{:?}", x))
            .collect();

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

    pub fn get(&self, key: &str) -> Option<&String> {
        self.dict.get(key).map(|&i| self.list.get(i)).flatten()
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


/// `SmargsError::Duplicate` can be used to tell the caller which argument was
/// a duplicate and its token-type.
#[derive(Debug, PartialEq)]
pub enum SmargsError {
    Empty,
    Duplicate(Token),
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
        // Catch the first duplicate that appeared from left to right
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
