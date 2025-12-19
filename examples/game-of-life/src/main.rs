use game_of_life::{blinker, glider};

fn main() {
    println!("=== Blinker (period 2) ===\n");
    let mut b = blinker();
    for i in 0..=4 {
        println!("Step {i}:");
        println!("{b}");
        b = b.step();
    }

    println!("=== Glider (translates after 4 steps) ===\n");
    let mut g = glider();
    for i in 0..=4 {
        println!("Step {i}:");
        println!("{g}");
        g = g.step();
    }
}
