//! Circuit Breaker: Verified State Machine
//!
//! A formally verified circuit breaker implementation. The Rust `step` function
//! is verified against Lean via bounded model checking with 83,300 exhaustive
//! test cases. The typestate API is built on top of `step`, ensuring compile-time
//! state transition safety backed by formal verification.

use serde::de::{self, Deserializer, MapAccess, Visitor};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

// ============================================================================
// Core Types (verified via bounded model checking)
// ============================================================================

/// State representation for verification. Matches Lean's `State` type exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum State {
    Closed(u64),
    Open(u64),
    HalfOpen,
}

/// Custom deserializer for Lean's mixed JSON format:
/// - `{"Closed": n}` and `{"Open": n}` for variants with data
/// - `"HalfOpen"` as a plain string for unit variant
impl<'de> Deserialize<'de> for State {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = State;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str(r#"{"Closed": n}, {"Open": n}, or "HalfOpen""#)
            }

            fn visit_str<E: de::Error>(self, v: &str) -> Result<State, E> {
                if v == "HalfOpen" {
                    Ok(State::HalfOpen)
                } else {
                    Err(E::custom(format!("unknown state variant: {v}")))
                }
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<State, M::Error> {
                let key: String = map
                    .next_key()?
                    .ok_or_else(|| de::Error::custom("empty map"))?;
                match key.as_str() {
                    "Closed" => Ok(State::Closed(map.next_value()?)),
                    "Open" => Ok(State::Open(map.next_value()?)),
                    _ => Err(de::Error::custom(format!("unknown key: {key}"))),
                }
            }
        }

        deserializer.deserialize_any(StateVisitor)
    }
}

/// Events that trigger state transitions. Matches Lean's `Event` type exactly.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Event {
    Success,
    Failure(u64),
    Tick(u64),
    ProbeSuccess(u64),
    ProbeFailure(u64),
}

// ============================================================================
// Verified Core: The `step` function
// ============================================================================

/// The canonical state transition function.
///
/// This function is verified against Lean via bounded model checking with 83,300
/// exhaustive test cases covering all (state, event, config) combinations within
/// bounds. The uniformity theorem (proven in Lean) guarantees that bounded
/// verification implies unbounded correctness: transition behavior depends only
/// on comparison results (threshold reached, timeout elapsed), not on the
/// magnitude of numeric values.
#[allow(clippy::match_same_arms)] // Arms are semantically distinct transitions
pub fn step(threshold: u64, timeout: u64, state: State, event: &Event) -> State {
    match (state, event) {
        // Closed state transitions
        (State::Closed(_), Event::Success) => State::Closed(0),
        (State::Closed(failures), Event::Failure(time)) => {
            if failures + 1 >= threshold {
                State::Open(*time)
            } else {
                State::Closed(failures + 1)
            }
        }
        // Open state transitions
        (State::Open(opened_at), Event::Tick(time)) => {
            if time.saturating_sub(opened_at) >= timeout {
                State::HalfOpen
            } else {
                State::Open(opened_at)
            }
        }
        // HalfOpen state transitions
        (State::HalfOpen, Event::ProbeSuccess(_)) => State::Closed(0),
        (State::HalfOpen, Event::ProbeFailure(time)) => State::Open(*time),
        // Ignored events: no state change
        (s, _) => s,
    }
}

// ============================================================================
// Typestate API (built on verified `step`)
// ============================================================================

/// Marker types for compile-time state tracking
pub mod states {
    pub struct Closed;
    pub struct Open;
    pub struct HalfOpen;
}

use states::{Closed, HalfOpen, Open};

/// Type-safe circuit breaker with compile-time state transitions.
///
/// The typestate pattern ensures that only valid transitions are possible:
/// - `CircuitBreaker<Closed>` can only call `record_success` or `record_failure`
/// - `CircuitBreaker<Open>` can only call `check_timeout`
/// - `CircuitBreaker<HalfOpen>` can only call `probe`
///
/// All transitions use the verified `step` function internally.
pub struct CircuitBreaker<S> {
    threshold: u64,
    timeout: u64,
    state: State,
    _marker: PhantomData<S>,
}

impl<S> fmt::Debug for CircuitBreaker<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CircuitBreaker")
            .field("threshold", &self.threshold)
            .field("timeout", &self.timeout)
            .field("state", &self.state)
            .finish()
    }
}

impl CircuitBreaker<Closed> {
    /// Create a new circuit breaker in the closed state.
    pub fn new(threshold: u64, timeout: u64) -> Self {
        Self {
            threshold,
            timeout,
            state: State::Closed(0),
            _marker: PhantomData,
        }
    }

    /// Record a successful operation. Resets the failure counter.
    pub fn record_success(self) -> Self {
        let new_state = step(self.threshold, self.timeout, self.state, &Event::Success);
        Self {
            state: new_state,
            ..self
        }
    }

    /// Record a failed operation. May trip the circuit open.
    pub fn record_failure(self, now: u64) -> Result<Self, CircuitBreaker<Open>> {
        let new_state = step(
            self.threshold,
            self.timeout,
            self.state,
            &Event::Failure(now),
        );
        match new_state {
            State::Closed(_) => Ok(Self {
                state: new_state,
                ..self
            }),
            State::Open(_) => Err(CircuitBreaker {
                threshold: self.threshold,
                timeout: self.timeout,
                state: new_state,
                _marker: PhantomData,
            }),
            State::HalfOpen => unreachable!("step cannot transition Closed to HalfOpen"),
        }
    }

    /// Get the current failure count.
    pub fn failures(&self) -> u64 {
        match self.state {
            State::Closed(f) => f,
            _ => unreachable!("CircuitBreaker<Closed> must have Closed state"),
        }
    }

    /// Convert to state representation.
    pub fn to_state(&self) -> State {
        self.state
    }
}

impl CircuitBreaker<Open> {
    /// Check if the timeout has elapsed. May transition to half-open.
    pub fn check_timeout(self, now: u64) -> Result<Self, CircuitBreaker<HalfOpen>> {
        let new_state = step(self.threshold, self.timeout, self.state, &Event::Tick(now));
        match new_state {
            State::Open(_) => Ok(Self {
                state: new_state,
                ..self
            }),
            State::HalfOpen => Err(CircuitBreaker {
                threshold: self.threshold,
                timeout: self.timeout,
                state: new_state,
                _marker: PhantomData,
            }),
            State::Closed(_) => unreachable!("step cannot transition Open to Closed"),
        }
    }

    /// Get the time when the circuit opened.
    pub fn opened_at(&self) -> u64 {
        match self.state {
            State::Open(t) => t,
            _ => unreachable!("CircuitBreaker<Open> must have Open state"),
        }
    }

    /// Convert to state representation.
    pub fn to_state(&self) -> State {
        self.state
    }
}

impl CircuitBreaker<HalfOpen> {
    /// Probe the service. Success closes the circuit, failure reopens it.
    pub fn probe(
        self,
        success: bool,
        now: u64,
    ) -> Result<CircuitBreaker<Closed>, CircuitBreaker<Open>> {
        let event = if success {
            Event::ProbeSuccess(now)
        } else {
            Event::ProbeFailure(now)
        };
        let new_state = step(self.threshold, self.timeout, self.state, &event);
        match new_state {
            State::Closed(_) => Ok(CircuitBreaker {
                threshold: self.threshold,
                timeout: self.timeout,
                state: new_state,
                _marker: PhantomData,
            }),
            State::Open(_) => Err(CircuitBreaker {
                threshold: self.threshold,
                timeout: self.timeout,
                state: new_state,
                _marker: PhantomData,
            }),
            State::HalfOpen => unreachable!("step cannot keep HalfOpen on probe"),
        }
    }

    /// Convert to state representation.
    pub fn to_state(&self) -> State {
        self.state
    }
}

// ============================================================================
// Dynamic wrapper for simulation
// ============================================================================

/// Dynamic state wrapper for event-driven simulation.
pub enum DynCircuitBreaker {
    Closed(CircuitBreaker<Closed>),
    Open(CircuitBreaker<Open>),
    HalfOpen(CircuitBreaker<HalfOpen>),
}

impl DynCircuitBreaker {
    /// Get the current state.
    pub fn to_state(&self) -> State {
        match self {
            Self::Closed(cb) => cb.to_state(),
            Self::Open(cb) => cb.to_state(),
            Self::HalfOpen(cb) => cb.to_state(),
        }
    }

    /// Process an event, returning the new state.
    pub fn process(self, event: Event) -> Self {
        match (self, event) {
            (Self::Closed(cb), Event::Success) => Self::Closed(cb.record_success()),
            (Self::Closed(cb), Event::Failure(now)) => match cb.record_failure(now) {
                Ok(cb) => Self::Closed(cb),
                Err(cb) => Self::Open(cb),
            },
            (Self::Open(cb), Event::Tick(now)) => match cb.check_timeout(now) {
                Ok(cb) => Self::Open(cb),
                Err(cb) => Self::HalfOpen(cb),
            },
            (Self::HalfOpen(cb), Event::ProbeSuccess(now)) => match cb.probe(true, now) {
                Ok(cb) => Self::Closed(cb),
                Err(cb) => Self::Open(cb),
            },
            (Self::HalfOpen(cb), Event::ProbeFailure(now)) => match cb.probe(false, now) {
                Ok(cb) => Self::Closed(cb),
                Err(cb) => Self::Open(cb),
            },
            (state, _) => state, // Ignored events
        }
    }
}

/// Simulate a sequence of events, returning all states.
pub fn simulate(initial: CircuitBreaker<Closed>, events: &[Event]) -> Vec<State> {
    let mut states = vec![initial.to_state()];
    let mut state = DynCircuitBreaker::Closed(initial);
    for event in events {
        state = state.process(event.clone());
        states.push(state.to_state());
    }
    states
}

// ============================================================================
// Test infrastructure
// ============================================================================

/// Test case from Lean's exhaustive enumeration.
#[derive(Debug, Deserialize)]
pub struct ExhaustiveTestCase {
    pub threshold: u64,
    pub timeout: u64,
    pub state: State,
    pub event: Event,
    pub expected: State,
}

#[cfg(test)]
mod bounded_model_checking {
    use super::*;

    /// Verify the Rust `step` function against 83,300 exhaustive test cases
    /// generated by Lean. This test passes if and only if Rust exactly matches
    /// Lean's semantics for all enumerated (config, state, event) combinations.
    #[test]
    fn exhaustive_lean_equivalence() {
        let json = include_str!("../testdata/exhaustive_tests.json");
        let cases: Vec<ExhaustiveTestCase> =
            serde_json::from_str(json).expect("valid exhaustive test JSON");

        let total = cases.len();
        let mut passed = 0;
        let mut failed_cases = Vec::new();

        for case in &cases {
            let actual = step(case.threshold, case.timeout, case.state, &case.event);
            if actual == case.expected {
                passed += 1;
            } else {
                failed_cases.push((case, actual));
            }
        }

        if !failed_cases.is_empty() {
            for (case, actual) in failed_cases.iter().take(10) {
                eprintln!(
                    "FAIL: threshold={}, timeout={}, state={:?}, event={:?}",
                    case.threshold, case.timeout, case.state, case.event
                );
                eprintln!("  expected: {:?}, actual: {:?}", case.expected, actual);
            }
            panic!(
                "Bounded model checking failed: {}/{} cases passed ({} failures)",
                passed,
                total,
                total - passed
            );
        }

        println!(
            "Bounded model checking PASSED: {}/{} transitions verified",
            passed, total
        );
    }

    /// Verify that the typestate API produces the same results as `step`.
    /// This ensures the ergonomic wrapper is faithful to the verified core.
    #[test]
    fn typestate_matches_step() {
        // Test closed -> closed (success)
        let cb = CircuitBreaker::new(3, 100);
        let expected = step(3, 100, State::Closed(0), &Event::Success);
        assert_eq!(cb.record_success().to_state(), expected);

        // Test closed -> closed (failure below threshold)
        let cb = CircuitBreaker::new(3, 100);
        let expected = step(3, 100, State::Closed(0), &Event::Failure(10));
        assert_eq!(cb.record_failure(10).unwrap().to_state(), expected);

        // Test closed -> open (failure at threshold)
        let cb = CircuitBreaker::new(3, 100);
        let cb = cb.record_failure(10).unwrap();
        let cb = cb.record_failure(20).unwrap();
        let expected = step(3, 100, State::Closed(2), &Event::Failure(30));
        let result = cb.record_failure(30);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_state(), expected);
    }
}
