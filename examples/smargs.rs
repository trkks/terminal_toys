use terminal_toys::*;


#[derive(Debug)]
struct Input {
    _name: String,
    _age: usize,
    _domain: String,
    _wants_to_subscribe: bool,
}

impl From<(bool, String, String, usize)> for Input {
    // TODO Trying to match the fields this way is error-prone...automate?
    fn from(value: (bool, String, String, usize)) -> Self {
        Self {
            _name: value.1,
            _age: value.3,
            _domain: value.2,
            _wants_to_subscribe: !value.0, // Note negation as flags default to False.
        }
    }
}

/// The same registration application example as seen in the documentation.
fn main() {
    let builder = || smargs!(
        "Register for service",
        ("Opt-out from receiving newsletter", vec!["no-newsletter"], bool),
        ("Your full name", vec![], String),
        ("Email address domain", vec!["d"], String, "getspam"),
        // FIXME: Setting a default here like "42" overrides concrete argument.
        ("Your age", vec!["a", "age"], usize)
    ).help_default();

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

    let (no_news, name, domain, age): (bool, String, String, usize) = {
        // Catch this error in order to make demonstration of actual parsing easier.
        match match builder().parse(std::env::args()) {
            missing_args@Err(Break { err: SmargsError::MissingRequired { .. }, .. }) => {
                eprint!("You did not pass enough arguments. Proceed with example ones [Y/n]?");
                let mut buf = String::new();
                std::io::stdin().read_line(&mut buf).expect("failed reading stdin");
                let s = buf.trim().to_lowercase();
                let n = s.len();
                if s.is_empty() || n <= 3 && "yes"[..n] == s[..n] {
                    builder().parse(example_args)
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
            Ok(x) => x,
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

    let user_email = format!("{}.{}@{}.com", name, age, domain)
        .replace(' ', ".")
        .to_lowercase();

    let subscriber_count = newsletter_subscribers.len();
    if !no_news {
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
