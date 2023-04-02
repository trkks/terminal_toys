use terminal_toys::{smargs, SmargsBreak, SmargsResult, SmargsError};
use std::{str::FromStr, fmt::Display};


#[derive(Debug)]
struct NonEmptyString(String);

#[derive(Debug)]
struct StringIsEmptyError;
impl Display for StringIsEmptyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "empty string")
    }
}
impl std::error::Error for StringIsEmptyError { }

impl FromStr for NonEmptyString {
    type Err = StringIsEmptyError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() > 0 {
            Ok(Self(<String as FromStr>::from_str(s).unwrap()))
        } else {
            Err(StringIsEmptyError)
        }
    }
}

impl Display for NonEmptyString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug)]
struct RegistrationInfo(String, usize, SmargsResult<NonEmptyString>, String, bool);

fn parse(args: impl Iterator<Item=String>) -> Result<RegistrationInfo, SmargsBreak> {
    smargs!(
        "Register for a service",
        SmargKind::Help,
        RegistrationInfo(
            ("Your full name",                    [],                SmargKind::Required),
            ("Your age",                          ["a", "age"],      SmargKind::Required),
            (
                "Email address without domain e.g. if address is 'foo@bar.baz' provide the 'foo' part",
                ["e"],
                SmargKind::Maybe
            ),
            ("Email address domain",              ["d"],             SmargKind::Optional("coolnewz")),
            ("Opt-out from receiving newsletter", ["no-newsletter"], SmargKind::Flag),
        ),
        args
    )
}

fn use_example_args() -> bool {
    eprint!("You did not pass enough arguments. Proceed with example ones [Y/n]?");
    let mut buf = String::new();
    std::io::stdin().read_line(&mut buf).expect("failed reading stdin");
    let s = buf.trim().to_lowercase();
    let n = s.len();
    s.is_empty() || n <= 3 && "yes"[..n] == s[..n]
}

/// The same registration application example as seen in the documentation. TODO: Update documentation
fn main() {
    let mut newsletter_subscribers = vec![];

    let example_args = vec![
        "register",
        "--no-newsletter",
        "-a",
        "26",
        "-d",
        "hatch",
        "Matt Myman",
    ]
    .into_iter()
    .map(String::from);

    let RegistrationInfo(name, age, local_part, domain, no_subscribe) = {
        // Catch this error in order to make demonstration of actual parsing easier.
        match match parse(std::env::args()) {
            missing_args@Err(SmargsBreak { err: SmargsError::MissingRequired { .. }, .. }) => {
                if use_example_args() {
                    parse(example_args)
                } else {
                    // Let the error continue on.
                    missing_args
                }
            }
            result_of_parsing => result_of_parsing,
        } {
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1);
            },
            Ok(x) => {
                println!("You passed {:?}", x);
                x
            }
        }
    };

    if age < 18 {
        let ys = 18 - age;
        let putdown = format!(
            "come back in {}",
            if ys == 1 {
                "a year".to_owned()
            } else {
                format!("{} years", ys)
            }
        );
        eprintln!("Failed to register: {}", putdown);
        std::process::exit(1);
    }

    let user_email = {
        let mut split = domain.rsplitn(1, '.');
        let (domain, tld) = match (split.next(), split.next()) {
            (Some(l), Some(r)) if l.len() > 0 && r.len() > 0 => (l, r),
            (Some(l), None) if l.len() > 0 => (l, "com"),
            _ => panic!("malformed domain: '{}'", domain),
        };

        let local_part = match local_part.0 {
            Ok(s) => Some(s),
            Err(err@SmargsError::MissingRequired { .. }) => {
                eprintln!("{}", err);
                None
            },
            Err(err) => panic!("{}", err),
        }.unwrap_or_else(|| {
            eprintln!("Constructing default local part");
            NonEmptyString(format!("{}.{}", name, age))
        });

        format!("{}@{}.{}", local_part, domain, tld)
            .replace(' ', ".")
            .to_lowercase()
    };

    let subscriber_count = newsletter_subscribers.len();
    if !no_subscribe {
        newsletter_subscribers.push(&user_email);
    }

    println!(
        "You have been registered as '{}' and {} to our newsletter",
        user_email,
        if subscriber_count < newsletter_subscribers.len() {
            "subscribed"
        } else {
            "did not subscribe"
        }
    );
}
