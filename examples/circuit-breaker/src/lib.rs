use serde::de::{self, Deserializer, MapAccess, Visitor};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum State {
    Closed(u64),
    Open(u64),
    HalfOpen,
}

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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Event {
    Success,
    Failure(u64),
    Tick(u64),
    ProbeSuccess(u64),
    ProbeFailure(u64),
}

// ANCHOR: step
#[allow(clippy::match_same_arms)]
pub fn step(threshold: u64, timeout: u64, state: State, event: &Event) -> State {
    match (state, event) {
        (State::Closed(_), Event::Success) => State::Closed(0),
        (State::Closed(failures), Event::Failure(time)) => {
            if failures + 1 >= threshold {
                State::Open(*time)
            } else {
                State::Closed(failures + 1)
            }
        }
        (State::Open(opened_at), Event::Tick(time)) => {
            if time.saturating_sub(opened_at) >= timeout {
                State::HalfOpen
            } else {
                State::Open(opened_at)
            }
        }
        (State::HalfOpen, Event::ProbeSuccess(_)) => State::Closed(0),
        (State::HalfOpen, Event::ProbeFailure(time)) => State::Open(*time),
        (s, _) => s,
    }
}
// ANCHOR_END: step

pub mod states {
    pub struct Closed;
    pub struct Open;
    pub struct HalfOpen;
}

use states::{Closed, HalfOpen, Open};

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
    pub fn new(threshold: u64, timeout: u64) -> Self {
        Self {
            threshold,
            timeout,
            state: State::Closed(0),
            _marker: PhantomData,
        }
    }

    pub fn record_success(self) -> Self {
        let new_state = step(self.threshold, self.timeout, self.state, &Event::Success);
        Self {
            state: new_state,
            ..self
        }
    }

    // ANCHOR: record_failure
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
            State::HalfOpen => unreachable!(),
        }
    }
    // ANCHOR_END: record_failure

    pub fn failures(&self) -> u64 {
        match self.state {
            State::Closed(f) => f,
            _ => unreachable!(),
        }
    }

    pub fn to_state(&self) -> State {
        self.state
    }
}

impl CircuitBreaker<Open> {
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
            State::Closed(_) => unreachable!(),
        }
    }

    pub fn opened_at(&self) -> u64 {
        match self.state {
            State::Open(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn to_state(&self) -> State {
        self.state
    }
}

impl CircuitBreaker<HalfOpen> {
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
            State::HalfOpen => unreachable!(),
        }
    }

    pub fn to_state(&self) -> State {
        self.state
    }
}

pub enum DynCircuitBreaker {
    Closed(CircuitBreaker<Closed>),
    Open(CircuitBreaker<Open>),
    HalfOpen(CircuitBreaker<HalfOpen>),
}

impl DynCircuitBreaker {
    pub fn to_state(&self) -> State {
        match self {
            Self::Closed(cb) => cb.to_state(),
            Self::Open(cb) => cb.to_state(),
            Self::HalfOpen(cb) => cb.to_state(),
        }
    }

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
            (state, _) => state,
        }
    }
}

pub fn simulate(initial: CircuitBreaker<Closed>, events: &[Event]) -> Vec<State> {
    let mut states = vec![initial.to_state()];
    let mut state = DynCircuitBreaker::Closed(initial);
    for event in events {
        state = state.process(event.clone());
        states.push(state.to_state());
    }
    states
}

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
    use flate2::read::GzDecoder;
    use std::io::Read;

    // ANCHOR: exhaustive_test
    #[test]
    fn exhaustive_lean_equivalence() {
        let compressed = include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/testdata/exhaustive_tests.json.gz"
        ));
        let mut decoder = GzDecoder::new(&compressed[..]);
        let mut json = String::new();
        decoder.read_to_string(&mut json).expect("valid gzip");
        let cases: Vec<ExhaustiveTestCase> =
            serde_json::from_str(&json).expect("valid exhaustive test JSON");

        for case in &cases {
            let actual = step(case.threshold, case.timeout, case.state, &case.event);
            assert_eq!(
                actual, case.expected,
                "threshold={}, timeout={}, state={:?}, event={:?}",
                case.threshold, case.timeout, case.state, case.event
            );
        }
    }
    // ANCHOR_END: exhaustive_test

    #[test]
    fn typestate_matches_step() {
        let cb = CircuitBreaker::new(3, 100);
        let expected = step(3, 100, State::Closed(0), &Event::Success);
        assert_eq!(cb.record_success().to_state(), expected);

        let cb = CircuitBreaker::new(3, 100);
        let expected = step(3, 100, State::Closed(0), &Event::Failure(10));
        assert_eq!(cb.record_failure(10).unwrap().to_state(), expected);

        let cb = CircuitBreaker::new(3, 100);
        let cb = cb.record_failure(10).unwrap();
        let cb = cb.record_failure(20).unwrap();
        let expected = step(3, 100, State::Closed(2), &Event::Failure(30));
        let result = cb.record_failure(30);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_state(), expected);
    }
}
