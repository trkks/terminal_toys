use std::collections::HashMap;

/// SiMpler thAn wRiting it once aGain Surely :)
/// PlaceS strings received froM std::env::ARGS into Suitable structures for
/// straightforward operation of flags, ordered and naMed ARGumentS.
///
/// # Example:
/// ```
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe -v --amount 3 foo".split(' ').map(String::from)
/// );
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
/// assert_eq!(result, String::from("(foo, foo, foo)"));
/// ```
pub struct Smargs {
    dict: HashMap<String, usize>,
    list: Vec<String>,
}
impl Smargs {
    pub fn new(args: impl Iterator<Item = String>) -> Self {
        let list: Vec<String> = args.collect();
        let mut dict = HashMap::with_capacity(list.len());

        for (i, arg) in list.iter().enumerate() {
            if arg.starts_with('-') {
                let option = arg.trim_start_matches('-').to_string();
                match list.get(i + 1) {
                    Some(val) if !val.starts_with('-') =>
                        // Option with value
                        dict.insert(option, i + 1),
                    _ =>
                        // Is a flag
                        dict.insert(option, 0),
                };
            }
        }

        Smargs { dict, list }
    }

    pub fn exe(&self) -> &String {
        &self.list[0]
    }

    pub fn first(&self) -> Option<&String> {
        self.list[1..].first()
    }

    pub fn last(&self) -> Option<&String> {
        self.list[1..].last()
    }

    pub fn has(&self, key: &str) -> bool {
        self.dict.contains_key(key)
    }
}

impl std::ops::Index<&str> for Smargs {
    type Output = String;
    fn index(&self, key: &str) -> &Self::Output {
        &self.list[self.dict[key]]
    }
}

/// NOTE Indexes excluding the executable path; use `Smargs::exe` if it's needed
impl std::ops::Index<usize> for Smargs {
    type Output = String;
    fn index(&self, index: usize) -> &Self::Output {
        &self.list[index + 1]
    }
}

#[cfg(test)]
mod tests {
    use super::Smargs;
    #[test]
    fn test_smargs() {
        let smargs = Smargs::new(
            "scale_img.exe nn --verbose -w 300 -h 95 --output scaled.png"
                .split(' ').map(String::from)
        );

        assert_eq!(smargs[0], String::from("nn"));
        assert_eq!(smargs[1], String::from("--verbose"));
        assert_eq!(smargs[2], String::from("-w"));
        assert_eq!(smargs[3], String::from("300"));
        assert_eq!(smargs[4], String::from("-h"));
        assert_eq!(smargs[5], String::from("95"));
        assert_eq!(smargs[6], String::from("--output"));
        assert_eq!(smargs[7], String::from("scaled.png"));

        assert_eq!(smargs["h"], "95");
        assert_eq!(smargs["w"], "300");
        assert_eq!(smargs["output"], "scaled.png");
        assert_eq!(smargs["verbose"], "scale_img.exe");
        assert!(smargs.has("verbose"));
        assert!(!smargs.has("v"));
        assert_eq!(smargs.first(), Some(&smargs[0]));
        assert_eq!(smargs.first(), Some(&String::from("nn")));
        assert_eq!(smargs.last(), Some(&String::from("scaled.png")));

        let smargs = Smargs::new("foo.exe".split(' ').map(String::from));
        assert_eq!(smargs.first(), None);
        assert_eq!(smargs.last(), None);

        let smargs = Smargs::new("foo.exe bar".split(' ').map(String::from));
        assert_eq!(smargs.first(), Some(&String::from("bar")));
        assert_eq!(smargs.last(), Some(&String::from("bar")));
    }

    #[test]
    #[should_panic]
    fn test_smargs_empty_key() {
        let smargs = Smargs::new("some.exe foo".split(' ').map(String::from));
        let _ = smargs[""];
    }

    #[test]
    #[should_panic]
    fn test_smargs_not_a_key() {
        let smargs = Smargs::new("some.exe foo bar".split(' ').map(String::from));
        let _ = smargs["foo"];
    }

    #[test]
    #[should_panic]
    fn test_smargs_not_an_index() {
        let smargs = Smargs::new("some.exe foo bar".split(' ').map(String::from));
        let _ = smargs[2];
    }
}
