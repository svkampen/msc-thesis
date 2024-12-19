/- Miscellaneous utility lemmas and notation -/
import Mathlib.Logic.Relation
import Mathlib.Data.Rel

open Relation

inductive SymmGen (r: Rel α α): Rel α α where
| fw_step: r x y → SymmGen r x y
| bw_step: r y x → SymmGen r x y

attribute [aesop 25% unsafe] SymmGen.fw_step
attribute [aesop 25% unsafe] SymmGen.bw_step

@[simp]
def Rel.union: Rel α β → Rel α β → Rel α β :=
  fun r₁ r₂ x y ↦ (r₁ x y) ∨ (r₂ x y)

instance Rel.instUnion: Union (Rel α β) where
  union := Rel.union

def Rel.union_comm (a b: Rel α α): (a ∪ b) = (b ∪ a) := by
  ext
  simp [(· ∪ ·), Rel.union]
  tauto

def Rel.union_left {a b: Rel α α} (x y: α): (a x y) → (a ∪ b) x y := by
  intro h
  simp [Union.union]
  left
  assumption

def Rel.union_right {a b: Rel α α} (x y: α): (b x y) → (a ∪ b) x y := by
  intro h
  simp [Union.union]
  right
  assumption

abbrev Rel.reflTransGen: Rel α α → Rel α α := ReflTransGen
abbrev Rel.eqvGen: Rel α α → Rel α α := EqvGen
abbrev Rel.transGen: Rel α α → Rel α α := TransGen
abbrev Rel.reflGen: Rel α α → Rel α α := ReflGen


attribute [symm] EqvGen.symm
attribute [refl] EqvGen.refl

/-- The reflexive-transitive closure of a relation is a subset of the equivalence closure. -/
lemma Relation.ReflTransGen.to_equiv {r: Rel α α} {a b} (h: (ReflTransGen r) a b): (EqvGen r) a b := by
  induction h using ReflTransGen.trans_induction_on with
  | ih₁ a => exact EqvGen.refl a
  | ih₂ h => exact EqvGen.rel _ _ h
  | ih₃ _ _ he₁ he₂ => exact EqvGen.trans _ _ _ he₁ he₂

attribute [trans] EqvGen.trans

namespace Thesis

postfix:max (priority := high) "∗" => Rel.reflTransGen
postfix:max (priority := high) "≡" => Rel.eqvGen
postfix:max (priority := high) "⁼" => Rel.reflGen
postfix:max (priority := high) "⁺" => Rel.transGen

section inv_props

variable {r: Rel α α}

/-- Taking the inverse of a relation commutes with reflexive-transitive closure. -/
@[simp]
lemma star_inv_iff_inv_star {r: Rel α α}: r.inv∗ x y ↔ r∗ y x := by
  constructor <;>
  · intro h
    induction h
    · rfl
    · apply ReflTransGen.head <;> assumption

def star_inv_of_inv_star: r.inv∗ x y → r∗ y x := star_inv_iff_inv_star.mp

def inv_star_of_star_inv: r∗ y x → r.inv∗ x y := star_inv_iff_inv_star.mpr

/-- Taking the inverse of a relation commutes with transitive closure. -/
@[simp]
lemma trans_inv_iff_inv_trans {r: Rel α α}: r.inv⁺ x y ↔ r⁺ y x := by
  constructor <;>
  · intro h
    induction h
    · apply TransGen.single; assumption
    · apply TransGen.head <;> assumption

def trans_inv_of_inv_trans: r.inv⁺ x y → r⁺ y x := trans_inv_iff_inv_trans.mp

def inv_trans_of_trans_inv: r⁺ y x → r.inv⁺ x y := trans_inv_iff_inv_trans.mpr

end inv_props

end Thesis
