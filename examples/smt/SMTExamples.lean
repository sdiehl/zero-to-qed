import Smt

namespace SMTExamples

-- ANCHOR: smt_basic
example (x y : Int) (h1 : x < y) (h2 : y < x + 1) : False := by
  smt [h1, h2]

example (a b c : Int) (h1 : a + b = c) (h2 : a = b) : 2 * b = c := by
  smt [h1, h2]

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  smt
-- ANCHOR_END: smt_basic

-- ANCHOR: smt_uninterpreted
example (f : Int → Int) (x y : Int) (h1 : x = y) : f x = f y := by
  smt [h1]

example (f : Int → Int) (x y z : Int)
    (h1 : x = y) (h2 : y = z) : f x = f z := by
  smt [h1, h2]
-- ANCHOR_END: smt_uninterpreted

-- ANCHOR: smt_quantifiers
example (f : Int → Int) (h : ∀ x, f x = x + 1) : f 5 = 6 := by
  smt [h]

example (h : ∀ x : Int, x < x + 1) : ∃ y : Int, 0 < y := by
  smt [h]
-- ANCHOR_END: smt_quantifiers

-- ANCHOR: smt_combined
example (f : Int → Int) (x : Int)
    (h1 : f x > 0) (h2 : f x < 2) : f x = 1 := by
  smt [h1, h2]

example (f : Int → Int → Int) (a b : Int)
    (h1 : f a b = a + b)
    (h2 : a = 3)
    (h3 : b = 4) : f a b = 7 := by
  smt [h1, h2, h3]
-- ANCHOR_END: smt_combined

end SMTExamples
