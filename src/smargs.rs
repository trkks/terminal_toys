use std::collections::HashMap;
use std::iter;
use std::ops;

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
/// assert_eq!(result, "(foo, foo, foo)");
/// ```
/// Or with just ordered arguments:
/// ```
/// let smargs = terminal_toys::Smargs::new(
///     "tupletize.exe 3 foo -v".split(' ').map(String::from)
/// );
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
pub struct Smargs {
    exe: String,
    list: Vec<String>,
    dict: HashMap<String, usize>,
}
impl Smargs {
    pub fn new(mut args: impl Iterator<Item = String>) -> Self {
        let exe = args.next().unwrap();
        let list: Vec<String> =
            // Hide a "boolean" to last index
            args.chain(iter::once(true.to_string())).collect();
        let dict = list.windows(2)
            .enumerate()
            .filter_map(|(i, x)|
                // Windows (always) has n elements per slice so indexing is ok
                x[0].starts_with('-').then(|| (
                    x[0].trim_start_matches('-').to_string(),
                    // Options point at next index, flags at "boolean" in last
                    if x[1].starts_with('-') { list.len() - 1 } else { i + 1 }
                ))
            )
            .collect();

        Smargs { list, dict, exe }
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

#[cfg(test)]
mod tests {
    use super::Smargs;
    #[test]
    fn test_smargs() {
        let smargs = Smargs::new(
            "scale_img.exe nn --verbose -w 300 -h 95 --output scaled.png"
                .split(' ').map(String::from)
        );

        let indexable_args = vec![
            "nn", "--verbose", "-w", "300",
            "-h", "95", "--output", "scaled.png",
        ];

        assert_eq!(smargs[0], indexable_args[0]);
        assert_eq!(smargs[1], indexable_args[1]);
        assert_eq!(smargs[2], indexable_args[2]);
        assert_eq!(smargs[3], indexable_args[3]);
        assert_eq!(smargs[4], indexable_args[4]);
        assert_eq!(smargs[5], indexable_args[5]);
        assert_eq!(smargs[6], indexable_args[6]);
        assert_eq!(smargs[7], indexable_args[7]);

        assert_eq!(smargs[..], smargs[0..]);
        assert_eq!(smargs[0..], smargs[..8]);
        assert_eq!(smargs[..8], smargs[0..8]);
        assert_eq!(smargs[0..8], indexable_args[0..8]);

        assert_eq!(smargs[2..6], indexable_args[2..6]);
        assert_eq!(smargs[3..3], indexable_args[3..3]);

        assert_eq!(smargs["h"], "95");
        assert_eq!(smargs["w"], "300");
        assert_eq!(smargs["output"], "scaled.png");
        assert_eq!(smargs["verbose"], "true");
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
    fn test_smargs_index_out_of_bounds() {
        let smargs = Smargs::new("some.exe foo bar".split(' ').map(String::from));
        let _ = smargs[2];
    }

    #[test]
    #[should_panic]
    fn test_smargs_range_out_of_bounds() {
        let smargs = Smargs::new("some.exe foo bar".split(' ').map(String::from));
        let _ = smargs[0..3];
    }
}