import Hanoi.Util

open Function

/-- A Hanoi configuration is an assignment of blocks to towers -/
abbrev Hanoi (τ β : Type*) :=
  β → τ

variable {τ τ₁ τ₂ β β₁ β₂ : Type*}
variable [LinearOrder β] [LinearOrder β₁] [LinearOrder β₂]
variable {B₂ : LowerSet β₂} [DecidablePred (. ∈ B₂)]

namespace Hanoi

/-- Map a configuration between tower types -/
def mapTower (f : τ₁ → τ₂) : Hanoi τ₁ β → Hanoi τ₂ β
| H => f ∘ H

/-- Map a configuration between block types -/
def mapBlock (g : β₂ → β₁) : Hanoi τ β₁ → Hanoi τ β₂
| H => H ∘ g

/-- Map a configuration to a lower subset of a block type -/
def mapLowerBlock (g : B₂ → β₁) (k : ∀ b, b ∉ B₂ → τ) : Hanoi τ β₁ → Hanoi τ β₂
| H => fun b ↦ if h : b ∈ B₂ then H (g ⟨b, h⟩) else k b h

/-- A move of the smallest block of some tower to a destination tower -/
structure Move (H : Hanoi τ β) where
  block : β
  dest : τ
  source_inf {b} : H block = H b → block ≤ b
  dest_inf {b} : dest = H b → block ≤ b

/-- Execute a move by reassigning the tower of one block -/
def move (H : Hanoi τ β) (m : Move H) : Hanoi τ β :=
  update H m.block m.dest

namespace Move

/-- Reverse a move -/
def reverse {H : Hanoi τ β} (m : Move H) : Move (H.move m) := by
  refine ⟨m.block, H m.block, ?_, ?_⟩
  all_goals
    intro b h
    by_cases hb : b = m.block
    all_goals simp [move, hb] at h
  . exact le_of_eq hb.symm
  . exact m.dest_inf h
  . exact le_of_eq hb.symm
  . exact m.source_inf h

/-- Reverse is its own inverse -/
theorem reverse_reverse {H : Hanoi τ β} (m : Move H) : (H.move m).move m.reverse = H := by
  simp [move, reverse]

/-- Map a move between tower types,
which is well-defined for injective maps -/
def mapTower {H : Hanoi τ₁ β} (f : τ₁ → τ₂) (h_inj : Injective f) (m : Move H) :
    Move (H.mapTower f) := by
  refine ⟨m.block, f m.dest, ?_, ?_⟩
  all_goals intro _ h
  . exact m.source_inf (h_inj h)
  . exact m.dest_inf (h_inj h)

/-- Map a move between block types,
which is well-defined for maps that respect order -/
def mapBlock {H : Hanoi τ β₁} (g : β₂ ≃o β₁) (m : Move H) :
    Move (H.mapBlock g) := by
  refine ⟨g.symm m.block, m.dest, ?_, ?_⟩
  all_goals
    intro _ h
    simp [Hanoi.mapBlock] at h
  . exact g.symm_apply_le.mpr (m.source_inf h)
  . exact g.symm_apply_le.mpr (m.dest_inf h)

/-- Map a move to a lower subset of a block type,
which is well-defined for maps that respect order

Essentially, any lower subset of blocks in a configuration
can be moved independently of the greater blocks -/
def mapLowerBlock {H : Hanoi τ β₁} (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) (m : Move H) :
    Move (H.mapLowerBlock g k) := by
  refine ⟨g.symm m.block, m.dest, ?_, ?_⟩
  all_goals
    intro b h
    by_cases hb : b ∈ B₂
    all_goals simp [Hanoi.mapLowerBlock, hb] at h
  · exact g.symm_apply_le.mpr (m.source_inf h)
  · exact le_of_lt (B₂.mem_lt_notMem (SetLike.coe_mem _) hb)
  · exact g.symm_apply_le.mpr (m.dest_inf h)
  · exact le_of_lt (B₂.mem_lt_notMem (SetLike.coe_mem _) hb)

/-- Mapping distributes over executing a move -/
theorem mapTower_move {H : Hanoi τ₁ β} (m : Move H) (f : τ₁ → τ₂) (h_inj : Injective f) :
    (H.move m).mapTower f = (H.mapTower f).move (m.mapTower f h_inj) := by
  ext b
  by_cases h : b = m.block
  all_goals simp [update, Hanoi.mapTower, move, mapTower, h]

/-- Mapping distributes over executing a move -/
theorem mapBlock_move {H : Hanoi τ β₁} (m : Move H) (g : β₂ ≃o β₁) :
    (H.move m).mapBlock g = (H.mapBlock g).move (m.mapBlock g) := by
  ext b
  by_cases h : b = g.symm m.block
  all_goals simp [update, Hanoi.mapBlock, move, mapBlock, h]
  . intro hn
    absurd h
    simp [←hn]

/-- Mapping distributes over executing a move -/
theorem mapLowerBlock_move {H : Hanoi τ β₁} (m : Move H) (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) :
    (H.move m).mapLowerBlock g k = (H.mapLowerBlock g k).move (m.mapLowerBlock g k) := by
  ext b
  by_cases hb : b ∈ B₂ <;> by_cases h : b = g.symm m.block
  all_goals simp [update, Hanoi.mapLowerBlock, move, mapLowerBlock, h, hb]
  . intro hn
    absurd h
    simp [←hn]

end Move

/-- A sequence of moves whose execution transforms one configuration into another -/
inductive Walk : Hanoi τ β → Hanoi τ β → Sort _ where
| nil {H} : Walk H H
| cons {H₁ H₂} (m : Move H₂) (w : Walk H₁ H₂) : Walk H₁ (move H₂ m)

namespace Walk

/-- The number of moves in a walk -/
def length {H₁ H₂ : Hanoi τ β} (w : Walk H₁ H₂) : ℕ :=
  match w with
  | nil => 0
  | cons _ w => w.length + 1

/-- Append one walk with the reverse of another

Calls should be left-associative for performance because it is the right-hand walk that unfolds -/
def appendReverse {H₁ H₂ H₃ : Hanoi τ β} (w₁ : Walk H₁ H₂) (w₂ : Walk H₃ H₂) : Walk H₁ H₃ :=
  match w₂ with
  | nil => w₁
  | cons m w₂ => appendReverse (cons m.reverse w₁) (m.reverse_reverse.symm ▸ w₂)
decreasing_by sorry

/-- Appending adds lengths -/
theorem appendReverse_length {H₁ H₂ H₃ : Hanoi τ β} (w₁ : Walk H₁ H₂) (w₂ : Walk H₃ H₂) :
    (appendReverse w₁ w₂).length = w₁.length + w₂.length := by
  induction w₂ with
  | nil => simp [length, appendReverse]
  | cons _ _ _ => grind [length, appendReverse]

/-- Map a walk between tower types,
which is well-defined for injective maps -/
def mapTower {H₁ H₂ : Hanoi τ₁ β} (f : τ₁ → τ₂) (h_inj : Injective f) (w : Walk H₁ H₂) :
    Walk (H₁.mapTower f) (H₂.mapTower f) :=
  match w with
  | nil => nil
  | cons m w => m.mapTower_move f h_inj ▸ cons (m.mapTower f h_inj) (w.mapTower f h_inj)

/-- Map a walk between block types,
which is well-defined for maps that respect order -/
def mapBlock {H₁ H₂ : Hanoi τ β₁} (g : β₂ ≃o β₁) (w : Walk H₁ H₂) :
    Walk (H₁.mapBlock g) (H₂.mapBlock g) :=
  match w with
  | nil => nil
  | cons m w => m.mapBlock_move g ▸ cons (m.mapBlock g) (w.mapBlock g)

/-- Map a walk to a lower subset of a block type,
which is well-defined for maps that respect order

Essentially, any lower subset of blocks in a configuration
can be moved independently of the greater blocks -/
def mapLowerBlock {H₁ H₂ : Hanoi τ β₁} (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) (w : Walk H₁ H₂) :
    Walk (H₁.mapLowerBlock g k) (H₂.mapLowerBlock g k) :=
  match w with
  | nil => nil
  | cons m w => m.mapLowerBlock_move g k ▸ cons (m.mapLowerBlock g k) (w.mapLowerBlock g k)

/-- Mapping preserves length -/
theorem mapTower_length
    {H₁ H₂ : Hanoi τ₁ β} (w : Walk H₁ H₂) (f : τ₁ → τ₂) (h_inj : Injective f) :
    (w.mapTower f h_inj).length = w.length := by
  induction w with
  | nil => rfl
  | cons _ _ _ => grind [length, mapTower]

/-- Mapping preserves length -/
theorem mapBlock_length
    {H₁ H₂ : Hanoi τ β₁} (w : Walk H₁ H₂) (g : β₂ ≃o β₁) :
    (w.mapBlock g).length = w.length := by
  induction w with
  | nil => rfl
  | cons _ _ _ => grind [length, mapBlock]

/-- Mapping preserves length -/
theorem mapLowerBlock_length
    {H₁ H₂ : Hanoi τ β₁} (w : Walk H₁ H₂) (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) :
    (w.mapLowerBlock g k).length = w.length := by
  induction w with
  | nil => rfl
  | cons _ _ _ => grind [length, mapLowerBlock]

end Walk

end Hanoi
