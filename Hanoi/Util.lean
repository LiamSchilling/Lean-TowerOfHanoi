import Mathlib.Order.Ideal

variable {α : Type*} [LinearOrder α] {a b : α}

/-- For lower sets `I` in total orderings,
every element in `I` is less than every element not in `I` -/
theorem mem_lt_notMem (I : LowerSet α) (ha : a ∈ I) (hb : b ∉ I) : a < b := by
  cases lt_or_ge a b
  . assumption
  . absurd hb
    apply I.lower
    all_goals assumption
