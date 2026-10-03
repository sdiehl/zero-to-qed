import ZeroToQED.AlgebraicStructures
import ZeroToQED.Basics
import ZeroToQED.CircuitBreaker
import ZeroToQED.Compiler
import ZeroToQED.ControlFlow
import ZeroToQED.DataStructures
import ZeroToQED.DependentTypes
import ZeroToQED.Effects
import ZeroToQED.GameOfLife
import ZeroToQED.IO
import ZeroToQED.Mathlib
import ZeroToQED.Polymorphism
import ZeroToQED.ProofStrategy
import ZeroToQED.Proofs.BinomialTheorem
import ZeroToQED.Proofs.Divisibility
import ZeroToQED.Proofs.EuclidLemma
import ZeroToQED.Proofs.Fibonacci
import ZeroToQED.Proofs.InfinitudePrimes
import ZeroToQED.Proofs.InfinitudePrimesGrind
import ZeroToQED.Proofs.Pigeonhole
import ZeroToQED.Proofs.Sqrt2Irrational
import ZeroToQED.Proving
import ZeroToQED.StackMachine
import ZeroToQED.StdLibrary
import ZeroToQED.Subtyping
import ZeroToQED.Tactics
import ZeroToQED.Termination
import ZeroToQED.TypeTheory
import ZeroToQED.Verification

/-!
# From Zero to QED

Root module. It imports every chapter module so that `lake build`
compiles everything the book includes. `scripts/check_includes.py`
verifies that this list stays in sync with the prose.
-/
