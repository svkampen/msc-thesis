/- Miscellaneous utility lemmas, often ones "missing" from mathlib. -/
import Mathlib.Logic.Relation
import Mathlib.Data.Rel

open Relation

@[simp]
def _root_.Rel.union: Rel α α → Rel α α → Rel α α :=
  fun r₁ r₂ x y ↦ (r₁ x y) ∨ (r₂ x y)

instance _root_.Rel.instUnion: Union (Rel α α) where
  union := Rel.union

def _root_.Rel.union_comm (a b: Rel α α): (a ∪ b) = (b ∪ a) := by
  ext
  simp [(· ∪ ·), _root_.Rel.union]
  tauto

def _root_.Rel.union_left {a b: Rel α α} (x y: α): (a x y) → (a ∪ b) x y := by
  intro h
  simp [Union.union]
  left
  assumption

def _root_.Rel.union_right {a b: Rel α α} (x y: α): (b x y) → (a ∪ b) x y := by
  intro h
  simp [Union.union]
  right
  assumption

abbrev _root_.Rel.reflTransGen: Rel α α → Rel α α := ReflTransGen


attribute [symm] EqvGen.symm
attribute [refl] EqvGen.refl

/-- The reflexive-transitive closure of a relation is a subset of the equivalence closure. -/
lemma _root_.Relation.ReflTransGen.to_equiv {r: Rel α α} {a b} (h: (ReflTransGen r) a b): (EqvGen r) a b := by
  induction h using ReflTransGen.trans_induction_on with
  | ih₁ a => exact EqvGen.refl a
  | ih₂ h => exact EqvGen.rel _ _ h
  | ih₃ _ _ he₁ he₂ => exact EqvGen.trans _ _ _ he₁ he₂

attribute [trans] EqvGen.trans
