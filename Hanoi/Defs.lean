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

/-- Map a move between tower types,
which is well-defined for injective maps -/
def mapTower {H : Hanoi τ₁ β} (f : τ₁ → τ₂) (h_inj : Injective f) : Move H → Move (H.mapTower f)
| ⟨b, d, h_source, h_dest⟩ => by
  refine ⟨b, f d, ?_, ?_⟩ <;>
    intro _ h
  . exact h_source (h_inj h)
  . exact h_dest (h_inj h)

/-- Map a move between block types,
which is well-defined for maps that respect order -/
def mapBlock {H : Hanoi τ β₁} (g : β₂ ≃o β₁) : Move H → Move (H.mapBlock g)
| ⟨b, d, h_source, h_dest⟩ => by
  refine ⟨g.symm b, d, ?_, ?_⟩ <;> (
    intro _ h
    simp [Hanoi.mapBlock] at h)
  . exact g.symm_apply_le.mpr (h_source h)
  . exact g.symm_apply_le.mpr (h_dest h)

/-- Map a move to a lower subset of a block type,
which is well-defined for maps that respect order

Essentially, any lower subset of blocks in a configuration
can be moved independently of the greater blocks -/
def mapLowerBlock {H : Hanoi τ β₁} (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) :
    Move H → Move (H.mapLowerBlock g k)
| ⟨b, d, h_source, h_dest⟩ => by
  refine ⟨g.symm b, d, ?_, ?_⟩ <;> (
    intro b h
    by_cases hb : b ∈ B₂
    simp [Hanoi.mapLowerBlock, hb] at h)
  · exact g.symm_apply_le.mpr (h_source h)
  · exact le_of_lt (mem_lt_notMem B₂ (SetLike.coe_mem _) hb)
  · exact g.symm_apply_le.mpr (h_dest h)
  · exact le_of_lt (mem_lt_notMem B₂ (SetLike.coe_mem _) hb)

/-- Mapping distributes over executing a move -/
theorem mapTower_move {H : Hanoi τ₁ β} (m : Move H) (f : τ₁ → τ₂) {h_inj : Injective f} :
    (H.move m).mapTower f = (H.mapTower f).move (m.mapTower f h_inj) := by
  ext b
  by_cases h : b = m.block <;>
    simp [Hanoi.mapTower, move, h, update, mapTower]

/-- Mapping distributes over executing a move -/
theorem mapBlock_move {H : Hanoi τ β₁} (m : Move H) (g : β₂ ≃o β₁) :
    (H.move m).mapBlock g = (H.mapBlock g).move (m.mapBlock g) := by
  ext b
  by_cases h : b = g.symm m.block <;>
    simp [Hanoi.mapBlock, move, h, propext g.eq_symm_apply ▸ h, update, mapBlock]

/-- Mapping distributes over executing a move -/
theorem mapLowerBlock_move {H : Hanoi τ β₁} (m : Move H) (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) :
    (H.move m).mapLowerBlock g k = (H.mapLowerBlock g k).move (m.mapLowerBlock g k) := by
  sorry

end Move

/-- A sequence of moves whose execution transforms one configuration into another -/
inductive Walk : Hanoi τ β → Hanoi τ β → Sort _ where
| nil {H} : Walk H H
| cons {H₁ H₂} (m : Move H₂) (w : Walk H₁ H₂) : Walk H₁ (move H₂ m)

namespace Walk

/-- The number of moves in a walk -/
def length {H₁ H₂ : Hanoi τ β} : Walk H₁ H₂ → ℕ
| nil => 0
| cons _ w => w.length + 1

/-- Map a walk between tower types,
which is well-defined for injective maps -/
def mapTower {H₁ H₂ : Hanoi τ₁ β} (f : τ₁ → τ₂) (h_inj : Injective f) :
    Walk H₁ H₂ → Walk (H₁.mapTower f) (H₂.mapTower f)
| nil => nil
| cons m w => m.mapTower_move f ▸ cons (m.mapTower f h_inj) (w.mapTower f h_inj)

/-- Map a walk between block types,
which is well-defined for maps that respect order -/
def mapBlock {H₁ H₂ : Hanoi τ β₁} (g : β₂ ≃o β₁) :
    Walk H₁ H₂ → Walk (H₁.mapBlock g) (H₂.mapBlock g)
| nil => nil
| cons m w => m.mapBlock_move g ▸ cons (m.mapBlock g) (w.mapBlock g)

/-- Map a walk to a lower subset of a block type,
which is well-defined for maps that respect order

Essentially, any lower subset of blocks in a configuration
can be moved independently of the greater blocks -/
def mapLowerBlock {H₁ H₂ : Hanoi τ β₁} (g : B₂ ≃o β₁) (k : ∀ b, b ∉ B₂ → τ) :
    Walk H₁ H₂ → Walk (H₁.mapLowerBlock g k) (H₂.mapLowerBlock g k)
| nil => nil
| cons m w => m.mapLowerBlock_move g k ▸ cons (m.mapLowerBlock g k) (w.mapLowerBlock g k)

end Walk

end Hanoi
