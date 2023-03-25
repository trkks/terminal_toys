use terminal_toys::{log, color_log, textcolor::{BRIGHT_RED, GREEN, RESET, BLACK, RED}};

const TTOYSLOG_COLOR: &str = BRIGHT_RED;

fn main() {
    println!(
        "If you have not set the environment variable according to the `log` \
        macro, this example will not show any log messages."
    );
    log!("Log message");
    color_log!("Colored log message");

    // Highlight errors and successes.
    println!("{}{} - Bad request: {}{}", RED, 400, RESET, "foo",);
    match Some(42) { Some(n) => println!("{}OK {}", GREEN, n), _ => { } }

    // Print a 8x7 heart ❤️.
    println!("  {}████{}    {}████{}",       BLACK, RESET, BLACK, RESET);
    println!("{}██{}████{}████{}████{}██{}", BLACK,   RED, BLACK,   RED, BLACK, RESET);
    println!("{}██{}████████████{}██{}",     BLACK,   RED, BLACK, RESET);
    println!("{}██{}████████████{}██{}",     BLACK,   RED, BLACK, RESET);
    println!("  {}██{}████████{}██{}",       BLACK,   RED, BLACK, RESET);
    println!("    {}██{}████{}██{}",         BLACK,   RED, BLACK, RESET);
    println!("      {}████{}",               BLACK, RESET);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn log() {
        assert_eq!(
            env!("TTOYSLOG"), module_path!(),
            "please set environment variable `TTOYSLOG` to {}", module_path!()
        );
        log!("Foo");
    }

    #[test]
    fn color_log() {
        assert_eq!(
            env!("TTOYSLOG"), module_path!(),
            "please set environment variable `TTOYSLOG` to {}", module_path!()
        );
        color_log!("Foo");
    }
}
