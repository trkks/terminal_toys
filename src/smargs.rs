use std::collections::HashMap;
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::iter;
use std::str::FromStr;


/////////////////////////////////////////////////////////////////////////////
// Constants
/////////////////////////////////////////////////////////////////////////////

const HELP_FLAG: &str = "h";
const HELP_WORD: &str = "help";

/////////////////////////////////////////////////////////////////////////////
// SmargError
/////////////////////////////////////////////////////////////////////////////

#[derive(Debug, PartialEq, Clone)]
pub struct Keys(Vec<char>, Vec<String>);


/// Error type for getting and parsing the values of arguments.
#[derive(Debug, PartialEq)]
pub enum SmargError {
    BadKeys(Keys),
    BadPosition(usize),
    BadFormat(String),
    Unrecognized(Token),
    Ambiguous(Token),
}


/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for SmargError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::BadKeys(Keys(flags, words)) => format!(
                    "option not found {}{}",
                    flags.iter()
                        .map(|c| format!(" -{}", c))
                        .collect::<String>(),
                    words.iter()
                        .map(|s| format!(" --{}", s))
                        .collect::<String>(),
                ),
            Self::BadPosition(i) => format!("position not in bounds: {}", i),
            Self::BadFormat(s) => format!("parsing error: {}", s),
            Self::Unrecognized(t) => format!("unrecognized option: {}", t),
            Self::Ambiguous(t) => format!("ambiguous option: {}", t),
        };
        write!(f, "{}", msg)
    }
}


/// Implement `Error` to ease the use in error-handling.
impl error::Error for SmargError {}


/////////////////////////////////////////////////////////////////////////////
// SmargsParserError
/////////////////////////////////////////////////////////////////////////////

/// Error type for `Smargs`'s constructors.
///
/// `SmargsParserError::Duplicate` can be used to tell the caller which argument
/// was a duplicate and its token-type.
#[derive(Debug, PartialEq)]
pub enum SmargsParserError {
    Empty,
    Duplicate(Token),
    // TODO This sort of layering feels dumb.
    Smarg(SmargError)
}


/// Offer nicer error-messages to user.
/// Implementing `Display` is also needed for `std::error::Error`.
impl fmt::Display for SmargsParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let msg = match self {
            Self::Empty => String::from("No arguments found"),
            // TODO impl Display for Token
            Self::Duplicate(t) => format!("Duplicate entry of {:?}", t),
            Self::Smarg(e) => e.to_string(),
        };
        write!(f, "{}", msg)
    }
}

impl error::Error for SmargsParserError {}

/////////////////////////////////////////////////////////////////////////////
// Token
/////////////////////////////////////////////////////////////////////////////

/// Makes handling the args -strings a bit clearer
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Value(String),
    Flag(char),
    Word(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", match self {
            Self::Value(s) => format!("Value '{}'", s),
            Self::Flag(c)  => format!("Flag '-{}'", c),
            Self::Word(s)  => format!("Word '--{}'", s),
        })
    }
}

/////////////////////////////////////////////////////////////////////////////
// SmargsParser
/////////////////////////////////////////////////////////////////////////////

/// Places strings received from std::env::args into suitable structures for
/// straightforward operation of flags, ordered and named arguments.
#[derive(Debug, PartialEq, Eq)]
pub struct SmargsParser {
    exe: String,
    list: Vec<String>,
    dict: HashMap<String, usize>,
}

impl SmargsParser {
    pub fn new(
        mut args: impl Iterator<Item = String>,
    ) -> Result<Self, SmargsParserError> {
        let exe = args.next().ok_or(SmargsParserError::Empty)?;

        // Contains the original arguments without empty ones.
        let list: Vec<String> =
            args.filter_map(|x| {
                    let xx = String::from(x.trim());
                    if xx.is_empty() { None } else { Some(xx) }
                })
                // Hide a "boolean" to last index
                .chain(iter::once(true.to_string()))
                .collect();

        // Tokenize and enumerate with original indices (ie. flag groups like
        // "-bar" count as one index).
        // NOTE that the added boolean in last index is also tokenized so that
        // the next dict-loop wraps up nicely.
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
        // Emulate old school for-loop because Rust is so expressive /s.
        let mut i = 0;
        while i < tokens.len().saturating_sub(1) {
            let current_token = &tokens[i].1;
            let (k, next_token) = &tokens[i + 1];

            // Check if left side of pair is a key.
            let kv_opt = match current_token {
                Token::Flag(chr) => Some(chr.to_string()),
                Token::Word(s)   => Some(s.clone()),
                _ => None,
            }
            // If it was, it will map to a value in resulting dict.
            .zip(Some(
                if let Token::Value(_) = next_token {
                    // Do not check if this Value is a key next iteration.
                    // This is literally the only reason for not using
                    // for-loop.
                    i += 1;
                    // Point at the following Value in the original list.
                    *k
                } else {
                    // Key without following value points to the boolean.
                    list.len() - 1
                }
            ));

            // Insert into dict and Err if key was already found.
            if let Some((key, value)) = kv_opt {
                if let Some(_value) = dict.insert(key, value) {
                    return Err(
                        SmargsParserError::Duplicate(current_token.clone())
                    )
                }
            }

            i += 1;
        }

        Ok(SmargsParser { list, dict, exe })
    }

    pub fn exe(&self) -> &String {
        &self.exe
    }

    pub fn len(&self) -> usize {
        // Do not include the "boolean" at the end
        &self.list.len() - 1
    }

    /// Return the string-value found in position.
    pub fn get_pos(&self, pos: usize) -> Result<String, SmargError> {
        if pos < self.len() {
            // Do not index the "boolean" at the end
            Ok(self.list[0..self.list.len() - 1][pos].clone())
        } else {
            Err(SmargError::BadPosition(pos))
        }
    }

    /// Return the matching string-value based on a list of keys.
    pub fn get_keys(
        &self,
        keys @ Keys(flags, words): &Keys,
    ) -> Result<String, SmargError> {
        match words.iter()
            .cloned()
            .chain(flags.iter().map(|&c| c.to_string()))
            .find_map(
                |k| self.dict.get(&k).map(|&i| self.list.get(i)).flatten()
        ) {
            Some(s) => Ok(String::from(s)),
            None    => Err(SmargError::BadKeys(keys.clone())),
        }
    }

    pub fn has(&self, key: &str) -> bool {
        self.dict.contains_key(key)
    }
}

/////////////////////////////////////////////////////////////////////////////
// SmargsParser tests
/////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod smarg_parser_tests {
    use super::{SmargsParser, SmargsParserError, SmargError, Token, Keys};
    /// Helper to construct `Keys` without cluttering the test-code.
    fn keys(flags: &[char], words: &[&str]) -> Keys {
        Keys(flags.to_vec(), words.iter().map(|&s| s.to_owned()).collect())
    }

    #[test]
    fn test_use_case() {
        let sp = SmargsParser::new(
            "scale_img.exe nn --verbose   -w 300 -h 300  --output scaled.png"
                .split(' ').map(String::from)
        ).unwrap();

        let indexable_args = vec![
            "nn", "--verbose", "-w", "300",
            "-h", "300", "--output", "scaled.png",
        ];

        assert_eq!(sp.get_pos(0), Ok(indexable_args[0].to_owned()));
        assert_eq!(sp.get_pos(1), Ok(indexable_args[1].to_owned()));
        assert_eq!(sp.get_pos(2), Ok(indexable_args[2].to_owned()));
        assert_eq!(sp.get_pos(3), Ok(indexable_args[3].to_owned()));
        assert_eq!(sp.get_pos(4), Ok(indexable_args[4].to_owned()));
        assert_eq!(sp.get_pos(5), Ok(indexable_args[5].to_owned()));
        assert_eq!(sp.get_pos(6), Ok(indexable_args[6].to_owned()));
        assert_eq!(sp.get_pos(7), Ok(indexable_args[7].to_owned()));

        assert_eq!(
			sp.get_keys(&keys(&['h'], &[])),
			Ok("300".to_owned()),
		);
        assert_eq!(
			sp.get_keys(&keys(&['w'], &[])),
			Ok("300".to_owned()),
		);
        assert_eq!(
			sp.get_keys(&keys(&[], &["output"])),
			Ok("scaled.png".to_owned()),
		);
        assert_eq!(
			sp.get_keys(&keys(&[], &["verbose"])),
			Ok("true".to_owned()),
		);
        assert!(sp.has("verbose"));
        assert!(!sp.has("v"));
        assert_eq!(sp.get_pos(0), Ok("nn".to_owned()));
        assert_eq!(sp.get_pos(7), Ok("scaled.png".to_owned()));
    }

    #[test]
    fn test_exe() {
        let args = "foo.exe".split(' ').map(String::from);
        let sp = SmargsParser::new(args).unwrap();
        assert!(match sp.get_pos(0).unwrap_err() {
            SmargError::BadPosition(0) => true,
            _ => false,
        });
        assert!(match sp.get_pos(usize::MAX).unwrap_err() {
            SmargError::BadPosition(usize::MAX) => true,
            _ => false,
        });
        assert_eq!(sp.exe(), &String::from("foo.exe"));
    }

    #[test]
    fn test_duplicates() {
        let args = "some.exe -fofo".split(' ').map(String::from);
        let double_flag = SmargsParser::new(args);
        // Catch the first duplicate that appears from left to right
        assert_eq!(
            double_flag,
            Err(SmargsParserError::Duplicate(Token::Flag('f')))
        );

        let args = "some.exe --foo --foo --bar --bar".split(' ')
            .map(String::from);
        let double_word = SmargsParser::new(args);
        assert_eq!(
            double_word,
            Err(SmargsParserError::Duplicate(Token::Word(String::from("foo"))))
        );

        let args = "some.exe -fo -of --bar --bar".split(' ')
            .map(String::from);
        let double_flag = SmargsParser::new(args);
        assert_eq!(
            double_flag,
            Err(SmargsParserError::Duplicate(Token::Flag('o')))
        );
    }

    #[test]
    fn test_combined_key_value() {
        let args = "some.exe -bar r-arg-value --bar"
            .split(' ')
            .map(String::from);
        let diff_types = SmargsParser::new(args).unwrap();
        assert_eq!(
            diff_types.get_keys(&keys(&['b'], &[]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            diff_types.get_keys(&keys(&['a'], &[]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            diff_types.get_keys(&keys(&['r'], &[])).unwrap(),
            "r-arg-value"
        );
        assert_eq!(
            diff_types.get_keys(&keys(&[], &["bar"]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );

        let args = "some.exe -bar --verbose -f 4.2"
            .split(' ')
            .map(String::from);
        let multiple = SmargsParser::new(args).unwrap();
        assert_eq!(
            multiple.get_keys(&keys(&['b'], &[]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            multiple.get_keys(&keys(&['a'], &[]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            multiple.get_keys(&keys(&['r'], &[]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            multiple.get_keys(&keys(&[], &["verbose"]))
                .unwrap()
                .parse::<bool>().unwrap(),
            true
        );
        assert_eq!(
            multiple.get_keys(&keys(&['f'], &[]))
                .unwrap()
                .parse::<f32>().unwrap(),
            4.2
        );
    }


    #[test]
    fn test_empty() {
        let sp = SmargsParser::new(std::iter::empty());
        assert_eq!(sp, Err(SmargsParserError::Empty));
    }

    #[test]
    #[should_panic]
    fn test_empty_key() {
        let args = "some.exe foo".split(' ').map(String::from);
        let sp = SmargsParser::new(args).unwrap();
        let _ = sp.get_keys(&keys(&[], &[""])).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_not_a_key() {
        let args = "some.exe foo bar".split(' ').map(String::from);
        if let Ok(sp) = SmargsParser::new(args) {
            let _ = sp.get_keys(&keys(&[], &["foo"])).unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn test_index_out_of_bounds() {
        let args = "some.exe foo bar".split(' ').map(String::from);
        if let Ok(sp) = SmargsParser::new(args) {
            let _ = sp.get_pos(2).unwrap();
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// Smarg
/////////////////////////////////////////////////////////////////////////////

/// Struct to attach the string-argument (`value`) to its explanation.
struct Smarg {
    value: Option<String>,
    description: String,
    keys: Keys,
}

/////////////////////////////////////////////////////////////////////////////
// CliDefinition
/////////////////////////////////////////////////////////////////////////////

/// A builder for ordering, mapping, generating instructions for and parsing
/// CLI-arguments.
///
/// NOTE: The ordering is defined by the order in which the option-defining
/// -methods like `required` or `optional` are called. The executable name
/// (often the first argument) is not included.
pub struct CliDefinition {
    instruction: String,
    list: Vec<Smarg>,
}

impl CliDefinition {
    /// Perform common operations for finding and adding the argument in order
    /// and generate its description including the position and options to use.
    ///
    /// Return the index of the added `Smarg`.
    fn push_arg(
        &mut self,
        words: &[&str],
        flags: &[char],
        description: &str,
    ) -> usize {
        // Always enumerate, even if finding argument fails.
        self.list.push(Smarg {
            value: None,
            description: format!(
                "{}) {}{}:: {}.",
                self.list.len(),
                flags.iter().
                    map(|x| format!("-{} ", x)).collect::<String>(),
                words.iter()
                    .map(|x| format!("--{} ", x)).collect::<String>(),
                description,
            ),
            keys: Keys(
                flags.to_vec(),
                words.iter().map(|&x| x.to_owned()).collect()
            ),
        });
        self.list.len() - 1
    }

    /// Private constructor to start the builder.
    fn new(description: &str) -> Self {
        Self {
            instruction: description.to_owned(),
            list: Vec::new(),
        }
    }

    // TODO Implement this as the TryFrom-trait.
    /// Parses CLI-arguments (into the constrained type `T`) from strings.
    pub fn parse<I, T>(mut self, args: I) -> Result<T, SmargsParserError>
    where
        I: IntoIterator<Item = String>,
        T: TryFrom<Self, Error = SmargError>,
    {
        // TODO A common error-type?
        let sp = SmargsParser::new(args.into_iter())?;

        for i in 0..self.list.len() {
            // Use the possible ways that arguments can be identified to get
            // them.
            let by_keys = sp.get_keys(&self.list[i].keys);
            let by_pos = sp.get_pos(i);

            // Prioritize using options (by_keys) as they are explicit.
            self.list[i].value.replace(
                by_keys.or(by_pos).map_err(|e| SmargsParserError::Smarg(e))?
            );
        }

        // TODO Should error on the whole thing and not on individual parts
        // (individually).
        <T as TryFrom<Self>>::try_from(self)
            .map_err(|e| SmargsParserError::Smarg(e))
    }

    /// Parses CLI-arguments from a call to `std::env::args`.
    pub fn parse_env<T>(self) -> Result<T, SmargsParserError>
    // TODO A common error-type?
    where
        T: TryFrom<CliDefinition, Error = SmargError>,
    {
        self.parse(std::env::args())
    }

    /// Set a `description` of the program and automatically generated
    /// instructions (a "help"-message) to be returned with the `--help` and
    /// `-h` -options.
    pub fn instruct(mut self, description: &str) -> Self {
        // Mark the instructions to be build after all args are collected.
        self.instruction = description.to_owned();
        self
    }

    /// Define a required argument i.e. input that is required from the user to
    /// use the program.
    pub fn required(
        mut self,
        words: &[&str],
        flags: &[char],
        description: &str,
    ) -> Self {
        self.push_arg(words, flags, description);
        // Add to the description the notion, that this argument is
        // required.
        self.instruction.push_str(" This argument is required.");
        self
    }

    /// Define an optional argument i.e. input that has a default value in case
    /// the user does not specify any.
    pub fn optional(
        mut self,
        words: &[&str],
        flags: &[char],
        description: &str,
        default: &str,
    ) -> Self {
        let i = self.push_arg(words, flags, description);
        // Add to the description the default value of this argument.
        // TODO Implement using the default.
        self.list[i].description.push_str(
            &format!(" Defaults to '{}'.", default)
        );
        self
    }

    /// Define an optional argument that can be generated at runtime for
    /// example based on the other arguments.
    pub fn generate(
        mut self,
        words: &[&str],
        flags: &[char],
        description: &str,
        generator: &dyn Fn(&[&str]) -> String,
    ) -> Self {
        let i = self.push_arg(words, flags, description);
        // Add to the description that this argument can be generated if
        // not given as input.
        // TODO Implement using the generator.
        self.list[i].description.push_str(
            " Will be attempted to be generated if not given."
        );
        self
    }

    /// Parse the argument in position `pos` and return the result.
    fn parse_nth<T>(&self, pos: usize) -> Result<T, SmargError>
    where
        T: FromStr,
        <T as FromStr>::Err: error::Error,
    {
        self.list[pos].value.as_ref()
            .unwrap()
            .parse::<T>()
            .map_err(|e| SmargError::BadFormat(e.to_string()))
    }
}

/////////////////////////////////////////////////////////////////////////////
// CliDefinition tests
/////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod cli_definition_tests {
    use super::{
        CliDefinition,
        SmargsParserError,
        SmargError,
        Token,
        HELP_FLAG,
        HELP_WORD,
    };
    type MINIMUM_PARSE_TYPE = (usize, u32);

    /// Helper for building and asserting help with a minimum argument-list.
    fn assert_help_string(args: impl IntoIterator<Item=String>) {
        let help_str = "make something with a width";
        assert!(
            CliDefinition::new("Testing")
                .instruct(help_str)
                .required(&["width"], &['w'], "Width of the something")
                .optional(&[], &[], "", "0")
                .parse::<_, MINIMUM_PARSE_TYPE>(args)
                .unwrap_err()
                .to_string().to_lowercase().contains(help_str)
        );
    }

    #[test]
    fn test_position_only() {
        let args = "foo.exe 42".split(' ').map(String::from);
        let (value, _): MINIMUM_PARSE_TYPE = CliDefinition::new("Testing 1")
            .required(&[], &[], "Forty two")
            //TODO These _empty_ "extras" might be dumb.
            .optional(&[], &[], "", "0")
            .parse(args)
            .unwrap();

        assert_eq!(value, 42_usize);

        let args = "foo.exe 42 bar baz".split(' ').map(String::from);
        let (meaning_of_life, bar, baz): (usize, String, String) =
            CliDefinition::new("Testing 2")
                .required(&[], &[], "Forty two")
                .required(&[], &[], "BaR")
                .required(&[], &[], "BaZ")
                .parse(args)
                .unwrap();

        assert_eq!(meaning_of_life, 42);
        assert_eq!(bar, String::from("bar"));
        assert_eq!(baz, String::from("baz"));
    }

    #[test]
    fn test_options_only() {
        let args = "foo.exe --meaning 42".split(' ').map(String::from);
        let (value, _): MINIMUM_PARSE_TYPE = CliDefinition::new("Testing")
            .required(&["meaning"], &['m'], "Forty two")
            .optional(&[], &[], "", "0")
            .parse(args)
            .unwrap();

        assert_eq!(value, 42_usize);

        let args = "foo.exe -m 42 --b bar -z baz".split(' ').map(String::from);
        let (meaning_of_life, bar, baz): (usize, String, String) =
            CliDefinition::new("Testing")
                .required(&[],      &['m'], "Forty two")
                .required(&["b"],   &[],    "BaR")
                .required(&["baz"], &['z'], "BaZ")
                .parse(args)
                .unwrap();

        assert_eq!(meaning_of_life, 42);
        assert_eq!(bar, String::from("bar"));
        assert_eq!(baz, String::from("baz"));
    }

    #[test]
    fn test_mixed() {
        let args = "foo.exe --do-thing -bar -z bazzy".split(' ')
            .map(String::from);
        let (baz, qux, do_thing, b, r, a):
            (String, u32, bool, bool, bool, bool) =
            CliDefinition::new("Testing")
                .required(&[],           &['z'], "BaZ")
                .optional(&["qux"],      &['q'], "Qux",             "666")
                .required(&["do-thing"], &[],    "The thing to do")
                .required(&[],           &['b'], "A b")
                .optional(&[],           &['r'], "A r",             "true")
                .optional(&[],           &['a'], "A a",             "false")
                .parse(args)
                .unwrap();

        assert_eq!(baz, "bazzy".to_owned());
        assert_eq!(qux, 666_u32);
        assert!(do_thing);
        assert!(b);
        assert!(r);
        assert!(a);
    }

    #[test]
    fn test_unrecognized_arg() {
        let args = "foo.exe --baz".split(' ').map(String::from);
        let err = CliDefinition::new("Testing")
                .required(&["bar"], &['b'], "Bar")
                .parse::<_, (u32, u32)>(args)
                .unwrap_err();
        assert_eq!(
            err,
            SmargsParserError::Smarg(
                SmargError::Unrecognized(Token::Word("baz".to_string()))
            )
        );
        // TODO Implement these messages.
        //assert!(err.to_string().to_lowercase().contains("did you mean"));
        //assert!(err.to_string().to_lowercase().contains("-b"));
        //assert!(err.to_string().to_lowercase().contains("--bar"));
    }

    #[test]
    fn test_optionals_only() {
        let args = "foo.exe".split(' ').map(String::from);
        let (value, _): (usize, u32) = CliDefinition::new("Testing")
            .optional(&["meaning"], &['m'], "Forty two", "42")
            .optional(&[], &[], "", "0")
            .parse(args)
            .unwrap();

        assert_eq!(value, 42_usize);

        let args = "foo.exe".split(' ').map(String::from);
        let (meaning_of_life, bar, baz): (usize, String, String) =
            CliDefinition::new("Testing")
                .optional(&[],      &['m'], "Forty two", "42")
                .optional(&["b"],   &[],    "BaR",       "bar")
                .optional(&["baz"], &['z'], "BaZ",       "baz")
                .parse(args)
                .unwrap();

        assert_eq!(meaning_of_life, 42);
        assert_eq!(bar, String::from("bar"));
        assert_eq!(baz, String::from("baz"));
    }

    #[test]
    fn test_instruct_no_args() {
        let args = "foo.exe"
            .split(' ')
            .map(String::from)
            .collect::<Vec<String>>();
        assert_help_string(args);
    } 
    
    #[test]
    fn test_instruct_flag() {
        let args_flag = format!("foo.exe -{}", HELP_FLAG)
            .split(' ')
            .map(String::from)
            .collect::<Vec<String>>();
        assert_help_string(args_flag);
    }

    #[test]
    fn test_instruct_word() {
        let args_word = format!("foo.exe --{}", HELP_WORD)
            .split(' ')
            .map(String::from)
            .collect::<Vec<String>>();
        assert_help_string(args_word);
    }

    #[test]
    fn test_instruct_mixed() {
        // NOTE Help overrides other options.
        let args_mixed = format!("foo.exe -w 42 -{}", HELP_FLAG)
            .split(' ')
            .map(String::from)
            .collect::<Vec<String>>();
        assert_help_string(args_mixed);
    }

    #[test]
    fn test_instruct_order() {
        let help_str = "make something with a width";
        let args = "foo.exe".split(' ').map(String::from);
        let err = CliDefinition::new("Testing")
            .instruct(help_str)
            .required(&["width"], &['w'], "Width of the something")
            .parse::<_, MINIMUM_PARSE_TYPE>(args)
            .unwrap_err();

        assert!(err.to_string().to_lowercase().contains(help_str));

        let help_str = "make something with a width";
        let args = "foo.exe".split(' ').map(String::from);
        let err = CliDefinition::new("Testing")
            .required(&["width"], &['w'], "Width of the something")
            .instruct(help_str)
            .parse::<_, MINIMUM_PARSE_TYPE>(args)
            .unwrap_err();

        assert!(err.to_string().to_lowercase().contains(help_str));

        let help_str = "make something with a width";
        let args = "foo.exe".split(' ').map(String::from);
        let err = CliDefinition::new("Testing")
            .required(&["width"], &['w'], "Width of the something")
            .instruct(help_str)
            .required(&["depth"], &['d'], "Depth of the something")
            .parse::<_, MINIMUM_PARSE_TYPE>(args)
            .unwrap_err();

        assert!(err.to_string().to_lowercase().contains(help_str));
    }

    #[test]
    fn test_instruct_option_taken() {
        let args = "foo.exe -h 42".split(' ').map(String::from);
        let (height, _): MINIMUM_PARSE_TYPE = CliDefinition::new("Testing")
            .required(&["height"], &['h'], "Height of something")
            .parse(args)
            .unwrap();

        assert_eq!(height, 42);
    }

    #[test]
    fn test_instruct_option_overridden() {
        let help_str = "make something with a height";
        let args = "foo.exe -h 42".split(' ').map(String::from);
        let err = CliDefinition::new("Testing")
            .instruct(help_str)
            .required(&["height"], &['h'], "Height of something")
            .parse::<_, MINIMUM_PARSE_TYPE>(args)
            .unwrap_err();

        assert_eq!(
            err,
            SmargsParserError::Smarg(SmargError::Ambiguous(Token::Flag('h')))
        );
    }

    #[test]
    #[should_panic]
    fn test_instruct_replaced() {
        let args = "foo.exe -w 42".split(' ').map(String::from);
        let (_, _): MINIMUM_PARSE_TYPE = CliDefinition::new("Testing")
            .instruct("Does something with width")
            .instruct("Uses width to do something")
            .parse(args)
            .unwrap();
    }
}

/////////////////////////////////////////////////////////////////////////////
// Smargs
/////////////////////////////////////////////////////////////////////////////

/// SiMpler thAn wRiting it once aGain Surely :)
///
/// Parses command line arguments based on order, options/switches, default
/// values and automatically generates help-strings for them.
///
/// # Example
/// Parsing and describing arguments for some raytracer:
/// ```
/// use std::path::PathBuf;
/// use std::ffi::OsStr;
///
/// // TODO Return --help if errors? Or just the required -error-msgs
/// // Get all the possible program arguments.
/// let (
///     source_path: PathBuf,
///     width: usize,
///     height: usize,
///     threads: usize,
///     out: PathBuf,
/// ) = Smargs::define("Render a scene using raytracing")
///     // TODO Autogenerate --help -message
///     // Set description and --help -h -options to print args.
///     .instruct() // Equivalent to required(&["help"], &['h'], <Help msg>)
///     .required(&["source"],  &['s'], "Scene file")
///     // TODO Have default as non-string.
///     .optional(&["width"],   &['w'], "Width of image",    "128")
///     .optional(&["height"],  &['h'], "Height of image",   "128")
///     .optional(&["threads"], &['t'], "Amount of threads", "4")
///     // Use the parsed values in generating the default value for this arg.
///     // TODO Have generated result as non-string.
///     .generate(&["out"],     &['o'], "Output path",
///         |arr| {
///             let res = format!(
///                 "./my_dir/{}_{}x{}.png",
///                 arr.nth(0)?, arr.nth(1)?, arr.nth(2)?,
///             );
///             Ok(res)
///         }
///     )
///     // Finish the builder and parse the args from this list.
///     .parse(["tracer", "./scenes/foo", "-h", "42", "-w", "666"].iter())?;
///
/// assert_eq!(source_path.file_stem(), OsStr::new("foo"));
/// assert_eq!(width, 666);
/// assert_eq!(height, 42);
/// assert_eq!(threads, 4);
/// assert_eq!(out, OsStr::new("foo_666x42.png"));
/// ```
///
/// If something goes wrong, for example an argument is not found or has bad
/// type, an error with a fitting message is returned:
/// ```
/// let foo = Smargs::define("Does foo.")
///     .required(&["foo"], &['f'], "Flag for doing foo.")
///     .parse(["foo.exe"].iter())
///     .unwrap_err();
/// //TODO This might be better to return the error-type (enum).
/// assert!(foo.to_string().to_lowercase().contains("not found"));
///
/// let bar = Smargs::define("Does bar.")
///     .required(&["bar"], &['b'], "Amount of bars.")
///     .parse::<usize>(["bar.exe", "--bar", "forty two"].iter())
///     .unwrap_err();
/// //TODO This might be better to return the error-type (enum).
/// assert!(bar.to_string().to_lowercase().contains("wrong type"));
/// ```
pub struct Smargs(Vec<Smarg>);
impl Smargs {
    /// Set the description of the program and start builder for arguments.
    pub fn define(description: &str) -> CliDefinition {
        CliDefinition::new(description)
    }
}

/////////////////////////////////////////////////////////////////////////////
// Implementations for the user to utilize `Smargs`
/////////////////////////////////////////////////////////////////////////////

/* TODO Are these necessary or possible to implement?
impl TryFrom<CliDefinition> for () {
    type Error = SmargError;
    fn try_from(_: CliDefinition) -> Result<Self, Self::Error> {
        Ok(())
    }
}


impl<T> TryFrom<CliDefinition> for (T,)
where
    (T,): FromStr,
    <(T,) as FromStr>::Err: error::Error,
{
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok(cd.parse_nth(0)?)
    }
}
*/


impl<T1, T2> TryFrom<CliDefinition> for (T1, T2)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
{
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok((
            cd.parse_nth(0)?,
            cd.parse_nth(1)?,
        ))
    }
}

impl<T1, T2, T3> TryFrom<CliDefinition> for (T1, T2, T3)
where
    T1: FromStr,
    <T1 as FromStr>::Err: error::Error,
    T2: FromStr,
    <T2 as FromStr>::Err: error::Error,
    T3: FromStr,
    <T3 as FromStr>::Err: error::Error,
{
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok((
            cd.parse_nth(0)?,
            cd.parse_nth(1)?,
            cd.parse_nth(2)?,
        ))
    }
}

impl<T1, T2, T3, T4> TryFrom<CliDefinition> for (T1, T2, T3, T4)
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
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok((
            cd.parse_nth(0)?,
            cd.parse_nth(1)?,
            cd.parse_nth(2)?,
            cd.parse_nth(3)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5> TryFrom<CliDefinition>
    for (T1, T2, T3, T4, T5)
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
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok((
            cd.parse_nth(0)?,
            cd.parse_nth(1)?,
            cd.parse_nth(2)?,
            cd.parse_nth(3)?,
            cd.parse_nth(4)?,
        ))
    }
}

impl<T1, T2, T3, T4, T5, T6> TryFrom<CliDefinition>
    for (T1, T2, T3, T4, T5, T6)
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
{
    type Error = SmargError;
    fn try_from(cd: CliDefinition) -> Result<Self, Self::Error> {
        Ok((
            cd.parse_nth(0)?,
            cd.parse_nth(1)?,
            cd.parse_nth(2)?,
            cd.parse_nth(3)?,
            cd.parse_nth(4)?,
            cd.parse_nth(5)?,
        ))
    }
}
// TODO Implemented more of the above if needed.
