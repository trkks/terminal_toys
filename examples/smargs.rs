use terminal_toys::{smargs, ArgType, Smargs};

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
fn main() -> Result<(), String> {
    let builder = Smargs::builder("Register for service")
        .optional(
            ["no-newsletter"],
            "Opt-out from receiving newsletter",
            ArgType::False,
        )
        .required([], "Your full name")
        .optional(["d"], "Email address domain", ArgType::Other("getspam"))
        .required(["a", "age"], "Your age");

    let mut newsletter_subscribers = vec![];

    let example_args = vec![
        "register.exe",
        "--no-newsletter",
        "-a",
        "26",
        "-d",
        "hatch",
        "Matt Myman",
    ]
    .into_iter()
    .map(String::from);

    let (no_news, name, domain, age): (bool, String, String, usize) =
        match builder.clone().parse(std::env::args()) {
            empty_error @ Err(smargs::Error::Empty) => {
                eprint!("You did not pass any arguments. Proceed with example ones [Y/n]?");
                let mut buf = String::new();
                match std::io::stdin().read_line(&mut buf) {
                    Ok(_) => {
                        let s = buf.trim().to_lowercase();
                        let n = s.len();
                        if s.is_empty() || n <= 3 && "yes"[..n] == s[..n] {
                            builder.parse(example_args)
                        } else {
                            empty_error
                        }
                    }
                    _ => empty_error,
                }
            }
            x => x,
        }
        .map_err(|e| format!("Argument failure: {}", e))
        .map(|x: (bool, String, String, usize)| {
            println!("{:?}", Into::<Input>::into(x.clone()));
            x
        })?;

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
    Ok(())
}
