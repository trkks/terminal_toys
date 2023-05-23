use terminal_toys::{smärgs, smargs};
use std::{str::FromStr, fmt::Display};


/// A custom type to parse from an argument.
#[derive(Debug)]
struct NonEmptyString(String);

/// A custom error to return when parsing fails.
#[derive(Debug)]
struct StringIsEmptyError;
impl Display for StringIsEmptyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "empty string")
    }
}
/// The `Err` variant in `SmargsResult` requires implementing
/// `std::error::Error` for using custom types.
impl std::error::Error for StringIsEmptyError { }

/// Bringing the two, custom type and parsing error together.
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

/// Type for a simple error message.
#[derive(Debug)]
struct TextErrorMessage(String);
impl Display for TextErrorMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for TextErrorMessage { }


/// Custom output type.
type RegistrationInfo = (String, usize, smargs::Result<NonEmptyString>, String, bool);

fn parse(args: impl DoubleEndedIterator<Item=String>) -> Result<RegistrationInfo, smargs::Break> {
    smärgs!(
        "Register for a service",
        (
            ("Your full name",                    [],                Kind::Required),
            ("Your age",                          ["a", "age"],      Kind::Required),
            (
                "Email address without domain e.g. if address is 'foo@bar.baz' provide the 'foo' part",
                ["e"],
                Kind::Maybe
            ),
            ("Email address domain",              ["d"],             Kind::Optional("coolnewz.com")),
            ("Opt-out from receiving newsletter", ["no-newsletter"], Kind::Flag),
        ),
    )
    .help_default()
    .parse(args)
}

fn use_example_args() -> bool {
    eprint!("You did not pass enough arguments. Proceed with example ones [Y/n]?");
    let mut buf = String::new();
    std::io::stdin().read_line(&mut buf).expect("failed reading stdin");
    let s = buf.trim().to_lowercase();
    let n = s.len();
    s.is_empty() || n <= 3 && "yes"[..n] == s[..n]
}

/// Demonstrate how `smargs::Error` can be handled e.g., using the `?` operator.
fn construct_email(name: String, age: usize, local_part: smargs::Result<NonEmptyString>, domain: String) -> Result<String, smargs::Error> {
    let split = domain.rsplit_once('.');
    let (domain, tld) = match split {
        Some((l, r)) if l.len() > 0 && r.len() > 0 => Ok((l, r)),
        Some((l, _)) if l.len() > 0 => Ok((l, "com")),
        _ => Err(smargs::Error::Dummy(Box::new(
            TextErrorMessage(format!("malformed domain: '{}'", domain))
        ))),
    }?;

    let local_part = local_part.0.or_else(|e|
        if let smargs::Error::MissingRequired { .. } | smargs::Error::Dummy(_) = e {
            eprintln!("Constructing default local part for email");
            Ok(NonEmptyString(format!("{}.{}", name, age)))
        } else {
            Err(e)
        }
    )?;

    Ok(
        format!("{}@{}.{}", local_part.0, domain, tld)
        .replace(' ', ".")
        .to_lowercase()
    )
}

/// Similar registration example as seen in the documentation.
fn main() {
    let mut newsletter_subscribers = vec![];

    let example_args = vec![
        "register",
        "--no-newsletter",
        "-a",
        "26",
        "-d",
        "hatch.com",
        "Matt Myman",
    ]
    .into_iter()
    .map(String::from);

    let (name, age, local_part, domain, no_subscribe) = {
        // Catch this error in order to make demonstration of actual parsing easier.
        let x = match parse(std::env::args()) {
            Err(smargs::Break { err: smargs::Error::MissingRequired { .. }, .. }) if use_example_args() => {
                // Use some hard-coded args for demonstration.
                parse(example_args).expect("bad example args")
            },
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1)
            },
            Ok(x) => x,
        };

        println!("You passed {:?}", x);

        x
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

    let user_email = match construct_email(name, age, local_part, domain) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        },
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
