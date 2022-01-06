use terminal_toys::start_spinner;

/// Do some work and animate a spinner during it
fn main() {
    print!("A spinner rotates while work is being done ");
    let ones_in_94967295 =
        || std::iter::repeat(1).take(94967295).collect::<Vec<u32>>();
    let ones = start_spinner(ones_in_94967295);

    print!("Such animation tells the user that the program has not halted ");
    let compute_42 = || (u32::MAX - ones.iter().sum::<u32>()) / 10_0000_000;

    let result = start_spinner(compute_42);
    println!("The finished program can return a value normally: {}", result);
}
