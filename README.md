# terminal_toys
Command-line thingamajigs helpful or otherwise.

## Smargs
Command line argument parser into types that implement `std::str::FromStr`.

### Example:
```rust
use terminal_toys::{smärgs, smargs};

struct MyInput { repeats: usize, string: String, verbose: bool };
let program_args = vec!["echon", "-v", "--amount", "3", "foo bar"];

let MyInput { repeats, string, verbose } = terminal_toys::smärgs!(
  "Echo a string N times",
  MyInput {
    repeats:("Amount of echoes",       vec!["amount"],       smargs::Kind::Required),
    string: ("The string to echo",     vec![],               smargs::Kind::Required),
    verbose:("Print more information", vec!["v", "verbose"], smargs::Kind::Flag)
  },
)
.parse(program_args.into_iter().map(String::from))?;

assert_eq!(repeats, 3);
assert_eq!(string, "foo bar");
assert!(verbose);

for i in 0..repeats {
  print!("{}", string);
  if verbose { eprintln!("{} repeats left", repeats - (i + 1)); }
}

# return Ok::<(), Box<smargs::Break>>(())
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
