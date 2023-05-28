# terminal_toys
Thingamajigs to make command-line programs more user- and developer-friendly.

## Smargs
- Parse program arguments into required types based on your definition.
- Show generated help messages in fitting situations:
  - An argument could not be parsed correctly
  - Not enough or too many arguments received
  - Duplicates of or undefined option keys used
  - Help is requested with the `-h/--help` options

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
Programs that take a long time processing will benefit from displaying their real-time status also on the command-line.

Example scenario of eight threads running simultaneously with each having their own progress bar:
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
The `start_spinner` -function animates the basic spinner (`(|) > (/) > (-) >
(\)`) while waiting on your function-call to finish:
```rust
use terminal_toys::spinner;
fn my_long_process() -> u32 { 42 }
let result = spinner::start_spinner(|| my_long_process());
```

## Color
Print colors on the command-line by setting current color with constants:
```rust
use terminal_toys::textcolor::{GREEN, RESET};
println!("{}The color of envy{}", GREEN, RESET);
```

## snake
Play snake on the command-line with:
```ignore
cargo run --bin snake
```
Use `WASD` to __stage__ an input to a direction and hit `Enter` to apply it.

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
