/// Stack machine operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Push(i64),
    Pop,
    Add,
    Mul,
    Dup,
    Swap,
}

/// Execution state: stack contents and validity flag
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub stack: Vec<i64>,
    pub valid: bool,
}

impl State {
    pub fn new() -> Self {
        State {
            stack: Vec::new(),
            valid: true,
        }
    }

    pub fn from_stack(stack: Vec<i64>) -> Self {
        State { stack, valid: true }
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

/// Execute a single operation, returning the new state.
/// This is the functional core we verify.
pub fn step(state: &State, op: Op) -> State {
    if !state.valid {
        return State {
            stack: state.stack.clone(),
            valid: false,
        };
    }

    match op {
        Op::Push(n) => {
            let mut stack = state.stack.clone();
            stack.push(n);
            State { stack, valid: true }
        }
        Op::Pop => {
            if state.stack.is_empty() {
                State {
                    stack: state.stack.clone(),
                    valid: false,
                }
            } else {
                let mut stack = state.stack.clone();
                stack.pop();
                State { stack, valid: true }
            }
        }
        Op::Add => {
            if state.stack.len() < 2 {
                State {
                    stack: state.stack.clone(),
                    valid: false,
                }
            } else {
                let mut stack = state.stack.clone();
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a + b);
                State { stack, valid: true }
            }
        }
        Op::Mul => {
            if state.stack.len() < 2 {
                State {
                    stack: state.stack.clone(),
                    valid: false,
                }
            } else {
                let mut stack = state.stack.clone();
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a * b);
                State { stack, valid: true }
            }
        }
        Op::Dup => {
            if state.stack.is_empty() {
                State {
                    stack: state.stack.clone(),
                    valid: false,
                }
            } else {
                let mut stack = state.stack.clone();
                let top = *stack.last().unwrap();
                stack.push(top);
                State { stack, valid: true }
            }
        }
        Op::Swap => {
            if state.stack.len() < 2 {
                State {
                    stack: state.stack.clone(),
                    valid: false,
                }
            } else {
                let mut stack = state.stack.clone();
                let len = stack.len();
                stack.swap(len - 1, len - 2);
                State { stack, valid: true }
            }
        }
    }
}

/// Execute a program, returning the final state
pub fn run(program: &[Op]) -> State {
    let mut state = State::new();
    for &op in program {
        state = step(&state, op);
    }
    state
}

/// Execute a program, returning a trace of all states
pub fn trace(program: &[Op]) -> Vec<State> {
    let mut states = Vec::with_capacity(program.len() + 1);
    let mut state = State::new();
    states.push(state.clone());
    for &op in program {
        state = step(&state, op);
        states.push(state.clone());
    }
    states
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_add() {
        let prog = [Op::Push(3), Op::Push(4), Op::Add];
        let result = run(&prog);
        assert_eq!(result.stack, vec![7]);
        assert!(result.valid);
    }

    #[test]
    fn push_mul() {
        let prog = [Op::Push(3), Op::Push(4), Op::Mul];
        let result = run(&prog);
        assert_eq!(result.stack, vec![12]);
        assert!(result.valid);
    }

    #[test]
    fn dup_add() {
        let prog = [Op::Push(5), Op::Dup, Op::Add];
        let result = run(&prog);
        assert_eq!(result.stack, vec![10]);
        assert!(result.valid);
    }

    #[test]
    fn swap_sub_pattern() {
        let prog = [Op::Push(10), Op::Push(3), Op::Swap];
        let result = run(&prog);
        assert_eq!(result.stack, vec![3, 10]);
        assert!(result.valid);
    }

    #[test]
    fn underflow_pop() {
        let prog = [Op::Pop];
        let result = run(&prog);
        assert!(!result.valid);
    }

    #[test]
    fn underflow_add() {
        let prog = [Op::Push(1), Op::Add];
        let result = run(&prog);
        assert!(!result.valid);
    }

    #[test]
    fn underflow_propagates() {
        let prog = [Op::Pop, Op::Push(1), Op::Push(2), Op::Add];
        let result = run(&prog);
        assert!(!result.valid);
    }

    #[test]
    fn trace_records_all_states() {
        let prog = [Op::Push(1), Op::Push(2), Op::Add];
        let states = trace(&prog);
        assert_eq!(states.len(), 4);
        assert_eq!(states[0].stack, vec![]);
        assert_eq!(states[1].stack, vec![1]);
        assert_eq!(states[2].stack, vec![1, 2]);
        assert_eq!(states[3].stack, vec![3]);
    }

    #[test]
    fn complex_program() {
        // (3 + 4) * 2 = 14
        let prog = [Op::Push(3), Op::Push(4), Op::Add, Op::Push(2), Op::Mul];
        let result = run(&prog);
        assert_eq!(result.stack, vec![14]);
        assert!(result.valid);
    }
}
