# terminal_toys
Thingamajigs to make command-line programs more user- and developer-friendly.

## Smargs
- Program argument options you define will be automatically parsed from strings
  to the needed types.
- Return fitting help messages when:
  - Arguments could not be parsed correctly,
  - Duplicates of an option were found (TODO Allow lists when so required e.g. `grep -f file1 -f file2 ...`),
  - There were no arguments at all,
  - The `--help` option is used.

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
# return Ok::<(), terminal_toys::SmargsError>(())
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
# use terminal_toys::spinner;
# fn my_long_process() -> u32 { 42 }
let result = spinner::start_spinner(|| my_long_process());
```

## Color
Print colors on the command-line with the two `color_print*`-macros:
```rust
# use terminal_toys::{color_print, Color};
color_print!(Color::Green, "The color of envy");
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
