# terminal_toys
Command-line thingamajigs helpful or otherwise.

## Smargs
Command line argument parser into types that implement `std::str::FromStr`.

### Example:
```rust
use std::io::Write;
use std::path::PathBuf;

use terminal_toys::smargs;

let program_args = vec![
    "echon",
    "--verbose",
    "--amount",
    "3",
    "-f",
    "baz.txt",
    "-f",
    "qux.txt",
    "foo bar",
]
.into_iter()
.map(String::from);

let (string, repeats, verbose, copies): (String, usize, bool, Vec<PathBuf>) =
    smargs::arguments!(
        "Echo strings N times",
        ("The string to echo", vec![], smargs::Argument::Required),
        (
            "Amount of echoes",
            vec!["amount"],
            smargs::Argument::Optional("1")
        ),
        (
            "Print more information",
            vec!["v", "verbose"],
            smargs::Argument::Flag
        ),
        (
            "Files to copy the output into",
            vec!["f", "file"],
            smargs::Argument::OptionalList(vec![])
        ),
    )
    .parse(program_args)
    .map_err(|e| e.to_string())?;

assert_eq!(repeats, 3);
assert_eq!(string, "foo bar");
assert!(verbose);
assert_eq!(copies.len(), 2);
assert_eq!(copies[0], PathBuf::from("baz.txt"));
assert_eq!(copies[1], PathBuf::from("qux.txt"));

let message = std::iter::repeat_with(|| string.clone())
    .take(repeats)
    .collect::<String>();

for f in copies {
    std::fs::File::create(&f)
        .and_then(|mut f| write!(f, "{}", message))
        .map_err(|_| "Echo copying failed".to_string())?;

    if verbose {
        eprintln!("Wrote the message to {}", f.display());
    }
}

print!("{}", message);

# return Ok::<(), String>(())
```

## ProgressBar
Example of eight threads with a progress bar each:
```ignore
Thread #1  95% [===================.]
Thread #2 100% [====================] Done!
Thread #3  95% [===================.]
Thread #4  95% [===================.]
Thread #5  95% [===================.]
Thread #6  95% [===================.]
Thread #7 100% [====================] Done!
Thread #8  90% [==================..]
```
## spinner
Animation of the basic spinner `(|) > (/) > (-) > (\)` while waiting for a function to finish:
```rust
use terminal_toys::spinner;
fn my_long_process() -> u32 { 42 }
let result = spinner::start_spinner(|| my_long_process());
```

## Color
Color manipulation codes saved into constants:
```rust
use terminal_toys::textcolor::{GREEN, RESET};
println!("{}The color of envy{}", GREEN, RESET);
```

## snake
Snake on the command-line. Control with `WASD`.

```ignore
######################
#............SSSSSS..#
#............S....S..#
#............S....S..#
#............S....S..#
#............S....S..#
#.......HSSSSS....S..#
#................SS..#
#....................#
#..............A.....#
#....................#
######################
```
