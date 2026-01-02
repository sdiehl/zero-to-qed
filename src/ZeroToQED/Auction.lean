import Mathlib.Tactic

/-!
# The Vickrey Auction

William Vickrey won the Nobel Prize for a simple observation: if the highest
bidder wins but pays only the second-highest bid, then honesty is optimal.
You cannot game the system. Bidding your true value is a weakly dominant
strategy, provable from first principles.

This elegance extends to combinatorial auctions, where bidders express
preferences over bundles of assets. The optimization is NP-hard, but the
incentive properties remain. Markets that seem chaotic are actually
mathematical objects with deep structure. Proving theorems about them
reveals invariants that testing could never find.
-/

-- ANCHOR: auction_types
abbrev Bid := Nat
abbrev Value := Nat

/-- A sealed-bid auction between two bidders -/
structure Auction where
  bid1 : Bid
  bid2 : Bid
  deriving DecidableEq, Repr

/-- Higher bid wins; ties favor bidder 1 -/
def winner (a : Auction) : Fin 2 :=
  if a.bid1 ≥ a.bid2 then 0 else 1

/-- Second-price rule: winner pays the losing bid -/
def payment (a : Auction) : Nat :=
  if a.bid1 ≥ a.bid2 then a.bid2 else a.bid1
-- ANCHOR_END: auction_types

-- ANCHOR: auction_clear
/-- Payoff: value minus payment when winning, zero when losing -/
def payoff (value : Value) (a : Auction) : Int :=
  if winner a = 0 then (value : Int) - (payment a : Int) else 0

/-- Bid truthfully: declare your actual value -/
def truthful (value : Value) (otherBid : Bid) : Auction :=
  ⟨value, otherBid⟩

/-- Bid strategically: declare something else -/
def strategic (altBid : Bid) (otherBid : Bid) : Auction :=
  ⟨altBid, otherBid⟩
-- ANCHOR_END: auction_clear

-- ANCHOR: auction_safety
/-- Truthful bidding never loses money -/
theorem truthful_nonneg (value : Value) (otherBid : Bid) :
    payoff value (truthful value otherBid) ≥ 0 := by
  unfold payoff truthful winner payment
  by_cases h : value ≥ otherBid
  · simp [h, Int.ofNat_le.mpr h]
  · simp [h]
-- ANCHOR_END: auction_safety

-- ANCHOR: auction_open
/--
The weak dominance theorem: no strategic bid beats truthful bidding.

For any valuation, any alternative bid, and any opponent behavior,
telling the truth does at least as well as any lie.
-/
theorem weak_dominance (value : Value) (altBid : Bid) (otherBid : Bid) :
    payoff value (truthful value otherBid) ≥
    payoff value (strategic altBid otherBid) := by
  sorry
-- ANCHOR_END: auction_open

/-
Why does this work? Consider the failure modes of lying:

• Overbid when value < otherBid: You win an auction you should lose,
  paying more than the item is worth. Negative payoff.

• Underbid when value > otherBid: You lose an auction you should win,
  missing a profitable trade. Zero instead of positive payoff.

Truthful bidding avoids both. You win exactly when winning is profitable.
The second-price rule makes your bid affect WHETHER you win, not WHAT you pay.
-/

#eval payoff 10 (truthful 10 7)    -- 3: win, pay 7, profit 3
#eval payoff 10 (strategic 5 7)    -- 0: underbid, lose profitable trade
#eval payoff 5 (truthful 5 7)      -- 0: lose unprofitable trade (correct!)
#eval payoff 5 (strategic 10 7)    -- -2: overbid, win at a loss
