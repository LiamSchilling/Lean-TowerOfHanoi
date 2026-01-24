import Hanoi.Defs
import Mathlib.Order.Fin.Basic

open Function

variable {τ : Type*}

namespace Hanoi

/-- A configuration with every block on the same tower -/
abbrev pile (β : Type*) (t : τ) : Hanoi τ β :=
  fun _ ↦ t

namespace Classic

/-- A configuration with every block on the same tower except one -/
abbrev nearPile (β : Type*) [DecidableEq β] (t : τ) (b : β) (t' : τ) : Hanoi τ β :=
  update (pile β t) b t'

/-- If the exceptional block is actually on the same tower, then there is no exceptional block -/
theorem nearPile_pile {β : Type*} [DecidableEq β] (t : τ) (b : β) :
    nearPile β t b t = pile β t := by
  simp

/-- The type of towers is a type with `3` elements -/
abbrev Tower : Type := Fin 3

/-- Assign a name to each tower -/
abbrev start : Tower := 0

/-- Assign a name to each tower -/
abbrev middle : Tower := 1

/-- Assign a name to each tower -/
abbrev goal : Tower := 2

/-- An inequality between tower names -/
theorem start_neq_middle : start ≠ middle := by
  trivial

/-- An inequality between tower names -/
theorem middle_neq_goal : middle ≠ goal := by
  trivial

/-- An inequality between tower names -/
theorem goal_neq_start : goal ≠ start := by
  trivial

/-- A unique block can be moved anywhere -/
def singlePileMove (a b : τ) :
    (pile (Fin 1) a).Move := by
  refine ⟨0, b, ?_, ?_⟩
  all_goals simp

/-- Moving a unique block relocates the entire pile -/
theorem move_singlePileMove (a b : τ) :
    (pile (Fin 1) a).move (singlePileMove a b) = pile (Fin 1) b := by
  ext
  simp [update, Fin.fin_one_eq_zero, move, singlePileMove]

/-- The exceptional block from a pile can be moved anywhere away from the pile -/
def nearPileMove {m : ℕ} (a b c : τ) (hab : a ≠ b) (hbc : b ≠ c) :
    (nearPile (Fin (m + 1)) b (Fin.last m) a).Move := by
  refine ⟨Fin.last m, c, ?_, ?_⟩
  all_goals
    intro k
    by_cases hk : k = Fin.last m
    all_goals simp [hab, hbc.symm, hk]

/-- Moving the exceptional block from a pile relocates the exceptional block -/
def move_nearPileMove {m : ℕ} (a b c : τ) (hab : a ≠ b) (hbc : b ≠ c) :
    (nearPile (Fin (m + 1)) b (Fin.last m) a).move (nearPileMove a b c hab hbc) =
    nearPile (Fin (m + 1)) b (Fin.last m) c := by
  ext k
  by_cases hk : k = Fin.last m
  all_goals simp [update, move, nearPileMove, hk]

/-- An arrangement of the towers

When `a`, `b`, and `c` are distinct, it is a permutation useful for mapping walks -/
def towerMap (a b c : Tower) : Tower → Tower
| 0 => a
| 1 => b
| 2 => c

/-- A tactic that proves `Injective (towerMap a b c)` when `a`, `b`, and `c` are distinct -/
macro "towerMap_inj" : tactic => `(tactic|
  intro a b <;>
  refine (match a with | 0 => ?_ | 1 => ?_ | 2 => ?_) <;>
  refine (match b with | 0 => ?_ | 1 => ?_ | 2 => ?_) <;>
  trivial
)

/-- The `start` pile maps along a `towerMap` -/
theorem towerMap_pile_start (a b c : Tower) :
    (pile τ start).mapTower (towerMap a b c) = pile τ a := by
  ext
  simp [mapTower, towerMap]

/-- The `middle` pile maps along a `towerMap` -/
theorem towerMap_pile_middle (a b c : Tower) :
    (pile τ middle).mapTower (towerMap a b c) = pile τ b := by
  ext
  simp [mapTower, towerMap]

/-- The `goal` pile maps along a `towerMap` -/
theorem towerMap_pile_goal (a b c : Tower) :
    (pile τ goal).mapTower (towerMap a b c) = pile τ c := by
  ext
  simp [mapTower, towerMap]

/-- The equivalence between `Fin (m + 1)` and a lower set of `Fin n` of size `m + 1` -/
def finLowerSetEquiv {n : ℕ} (m : ℕ) (h_lt : m < n) :
    LowerSet.principal (Fin.mk m h_lt) ≃ Fin (m + 1) := by
  refine ⟨fun ⟨k, h⟩ ↦ ⟨k, ?_⟩, fun ⟨k, h⟩ ↦ ⟨Fin.mk k ?_, ?_⟩, ?_, ?_⟩
  · exact Nat.lt_succ_of_le h
  · exact lt_of_le_of_lt (Nat.le_of_lt_succ h) h_lt
  · exact Nat.le_of_lt_succ h
  · simp [LeftInverse]
  · simp [LeftInverse, RightInverse]

/-- The order isomorphism between `Fin (m + 1)` and a lower set of `Fin n` of size `m + 1` -/
def finLowerSetOrderIso {n : ℕ} (m : ℕ) (h_lt : m < n) :
    LowerSet.principal (Fin.mk m h_lt) ≃o Fin (m + 1) := by
  refine ⟨finLowerSetEquiv m h_lt, ?_⟩
  · rfl

/-- A lower pile of size `m + 1` mapped into a pile of size `m + 2` is just a `nearPile` -/
theorem mapLowerBlock_pile (m : ℕ) (a b : τ) :
    (pile (Fin (m + 1)) b).mapLowerBlock (finLowerSetOrderIso m (by simp)) (fun _ _ ↦ a) =
    nearPile (Fin (m + 2)) b (Fin.last (m + 1)) a := by
  ext k
  by_cases hk : k = Fin.last (m + 1)
  all_goals simp [LowerSet.principal, mapLowerBlock, hk]
  · simp [Fin.last]
  · intro h
    absurd hk
    exact Fin.last_le_iff.mp h

/-- The optimal solution to the classic game with `3` towers and a pile of `n` blocks

Though the definition is named `shortestWalk`,
do note that its optimality is yet to be formalized -/
def shortestWalk (n : ℕ) (hn : n ≠ 0) :
    Walk (pile (Fin n) start) (pile (Fin n) goal) :=
  match n with
  | 0 => by contradiction
  | 1 => move_singlePileMove start goal ▸ Walk.cons (singlePileMove start goal) Walk.nil
  | n + 2 =>
    let lowerShortestWalk :=
      shortestWalk (n + 1) (by simp)
    let lowerStartToMiddle :=
      mapLowerBlock_pile _ _ _ ▸ mapLowerBlock_pile _ _ _ ▸
        (towerMap_pile_goal _ _ _ ▸ towerMap_pile_start _ _ _ ▸
          lowerShortestWalk.mapTower (towerMap start goal middle) (by towerMap_inj)).mapLowerBlock
            (finLowerSetOrderIso n (by simp)) (fun _ _ ↦ start)
    let lowerGoalToMiddle :=
      mapLowerBlock_pile _ _ _ ▸ mapLowerBlock_pile _ _ _ ▸
        (towerMap_pile_goal _ _ _ ▸ towerMap_pile_start _ _ _ ▸
          lowerShortestWalk.mapTower (towerMap goal start middle) (by towerMap_inj)).mapLowerBlock
            (finLowerSetOrderIso n (by simp)) (fun _ _ ↦ goal)
    let moveGreatestBlock :=
      nearPileMove start middle goal start_neq_middle middle_neq_goal
    let shortestWalk :=
      nearPile_pile _ (Fin.last _) ▸ nearPile_pile _ (Fin.last _) ▸
        Walk.appendReverse (move_nearPileMove _ _ _ start_neq_middle middle_neq_goal ▸
          Walk.cons moveGreatestBlock lowerStartToMiddle) lowerGoalToMiddle
    shortestWalk

/-- The optimal solution contains `2 ^ n + 1` steps

Though the definition is named `shortestWalk`,
do note that its optimality is yet to be formalized -/
theorem shortestWalk_length (n : ℕ) (hn : n ≠ 0) : (shortestWalk n hn).length = 2 ^ n - 1 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
  match n with
  | 0 => simp [Walk.length, shortestWalk]
  | n + 1 =>
    simp [Walk.length, shortestWalk, ih]
    grind

end Classic

end Hanoi

#print axioms Hanoi.Classic.shortestWalk
#print axioms Hanoi.Classic.shortestWalk_length
