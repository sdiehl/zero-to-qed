#!/bin/bash
set -e
lake exe fizzbuzz 20
lake exe wordfreq "the spice must flow the spice extends life"
lake exe collatz 27
lake exe dnd 42
lake exe units
lake exe mtg
lake exe spells
lake exe atm
lake exe vending
lake exe nqueens
lake exe parsers
lake exe stack
lake exe life

# Rust examples with Lean-generated test vectors
cd examples && cargo test --package circuit-breaker
