# terminal_toys
Thingamajigs to make command-line programs more user (and developer) -friendly.

## Smargs
Stands for *smarter arguments* but calling it *smart* may be a bit of a stretch.
Simply maps a list of strings into command-line options and values by recognizing `--` and `-` from their beginning.

For example suppose you had a program for manipulating a row in a text file. This might need a filepath on 
the operating system `file` and an integer `row` as input.
For a small program like this you would probably define some fixed order for the user of your program to 
use (e.g. file 1st and row as 2nd) and then parse the strings to the needed types according to this.

With `Smargs` you can more easily provide the user with options like `--file ./my/file/path.txt` and `-r 42` that'll
be automatically parsed to the types your program requires. `Smargs` can also return fitting error-messages for cases where
the user's input could not be parsed correctly, they input the `row`-option twice or that there were no arguments at all.

All you need to do is come up with the type and options of the arguments and call `Smargs::gets` to pick them out for you from the argument list:
```rs
// Initialize Smargs from the cli-args.
let smargs = Smargs::from_env()?;
// Use --file or -f for the file...
let file: std::path::Path = smargs.gets(&["file", "f"])?;
// ...and --row or -r for the row.
let row: usize = smargs.gets(&["row", "r"])?;
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
