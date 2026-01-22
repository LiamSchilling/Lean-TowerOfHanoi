import Mathlib.Order.Ideal

variable {α : Type*}

namespace LowerSet

/-- The smallest lower set containing an element -/
def principal [Preorder α] (a : α) : LowerSet α :=
  ⟨{ b : α | b ≤ a }, by intro _ _ h_le ha; exact le_trans h_le ha⟩

/-- Reduce deciding membership in a principal to deciding an inequality -/
instance [Preorder α] [DecidableLE α] (a b : α) : Decidable (b ∈ principal a) :=
  decidable_of_iff (b ≤ a) (by rfl)

/-- For lower sets `I` in total orderings,
every element in `I` is less than every element not in `I` -/
theorem mem_lt_notMem [LinearOrder α] {a b : α} (I : LowerSet α) (ha : a ∈ I) (hb : b ∉ I) :
    a < b := by
  cases lt_or_ge a b
  . assumption
  . absurd hb
    apply I.lower
    all_goals assumption

end LowerSet
