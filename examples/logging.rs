use terminal_toys::{log, color_log, Color};

const TTOYSLOG_COLOR: Color = Color::BrightRed;

fn main() {
    println!(
        "If you have not set the environment variable according to the `log` \
        macro, this example will not show any log messages."
    );
    log!("Log message");
    color_log!("Log message colored '{:?}'", TTOYSLOG_COLOR);
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
