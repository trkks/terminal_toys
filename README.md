# terminal_toys
Thingamajigs to make command-line programs more user- and developer-friendly.

## Smargs
- Program argument options you define (e.g. the path in `--file ./my/file/path.txt` or 42 in `-n 42`) will be automatically parsed from strings to the needed types. 
- Return fitting help messages when:
  - Arguments could not be parsed correctly,
  - Duplicates of an option were found (TODO Allow lists when so required e.g. `grep -f file1 -f file2 ...`),
  - There were no arguments at all,
  - The `--help` option is used.

### Example: 
```rs
// Program arguments: 'repeat.exe -v --amount 3 "foo bar"'
let (n, s, verbose) : (usize, String, bool) =
  Smargs::builder("Repeat!")
    .required(Some((&[], &["amount"])), "Amount of repeats")
    .required(None, "The string to repeat")
    .optional(Some((&['v'], &["verbose"])), "Print information about the result", ArgType::False)
    .from_env()?;
```

## ProgressBar
Programs that take a long time processing will benefit from displaying their real-time status also on the command-line.

Example scenario of eight threads running simultaneously with each having their own progress bar:
```
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
The `start_spinner` -function animates the basic spinner (`(|) > (/) > (-) > (\)`) while waiting on your function-call to finish:
```rs
let result = spinner::start_spinner(|| my_long_process());
```

## Color
Print colors on the command-line with the two `color_print*`-macros:
```rs
color_print!(Color::Green, "The color of envy");
```

## snake
Play snake on the command-line with: 
```
cargo run --bin snake
```
Use `WASD` to __stage__ an input to a direction and hit `Enter` to apply it (very intuitive, I know).

Example scenario:
```
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
