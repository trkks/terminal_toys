# terminal_toys
Thingamajigs to make command-line programs more user- and developer-friendly.

## Smargs
- Easily parse program arguments based on your definition into required types.
- Return automatically generated help messages when for example:
  - Argument could not be parsed correctly
  - Not enough or too many arguments are given
  - Duplicate or undefined option keys are used
  - Help is requested with the `--help` option

### Example:
```rust
struct MyInput { repeats: usize, string: String, verbose: bool };
let program_args = vec!["repeat.exe", "-v", "--amount", "3", "foo bar"];

let MyInput { repeats, string, verbose } = terminal_toys::smargs!(
      "Repeat!",
      MyInput {
        repeats:("Amount of repeats",      vec!["amount"],       usize),
        string: ("The string to repeat",   vec![],               String),
        verbose:("Print more information", vec!["v", "verbose"], bool)
      }
    )
    .parse(program_args.into_iter().map(String::from))?;

assert_eq!(repeats, 3);
assert_eq!(string, "foo bar");
assert!(verbose);
# return Ok::<(), terminal_toys::SmargsBreak>(())
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
