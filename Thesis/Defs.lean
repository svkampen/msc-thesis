import Mathlib.Logic.Relation
import Lean.Meta.Tactic.Symm
import Mathlib.Tactic

namespace Thesis

open Relation

/-- The symmetric closure over a relation `r`. -/
inductive SymmGen (r : α → α → Prop) : α → α → Prop
  | single {a b} : r a b → SymmGen r a b
  | symm {a b} : SymmGen r a b → SymmGen r b a

attribute [symm] SymmGen.symm

theorem SymmGen.symmetric {r : α → α → Prop} : Symmetric (SymmGen r) :=
  fun _ _ h ↦ by symm; assumption

section ars_def

/--
An Abstract Rewriting System (ARS), consisting of a set `α`, index type `I`
and an indexed set of rewrite relations on `α` over `I` (`ARS.rel`).
-/
structure ARS (α I : Type*) where
  rel : I → α → α → Prop

variable {α I}
variable (A : ARS α I)

/-- The union of the indexed relations of an ARS. -/
abbrev ARS.union_rel: α → α → Prop :=
  fun x y ↦ ∃i, A.rel i x y

/-- The reflexive-transitive closure of an ARS relation. -/
abbrev ARS.rel_star: I → α → α → Prop :=
  fun i ↦ ReflTransGen (A.rel i)

/-- The reflexive-transitive closure of the union of ARS relations. -/
abbrev ARS.union_rel_star: α → α → Prop :=
  ReflTransGen A.union_rel

/--
The convertability relation ≡ generated from the union of ARS relations.
Note that this is denoted using `=` in TeReSe, which we use for true equality.
-/
def ARS.conv: α → α → Prop :=
  EqvGen A.union_rel

/-- `x ⇒ y` means x one-step reduces to y. -/
local infixr:60 (priority := high) " ⇒ " => A.union_rel

/-- `x ⇒∗ y` means x reduces to y reflexive-transitively. -/
local infixr:60 (priority := high) " ⇒∗ " => A.union_rel_star

-- I don't love this notation, but oh well..
local notation:50 (priority := high) x:51 " ⇒[" i "]" y:50 => A.rel i x y
local notation:50 (priority := high) x:51 " ⇒∗[" i "]" y:50 => A.rel_star i x y

/--
`A: ARS α I` is a sub-ARS of `B: ARS β J` if:
- α is a subtype of β (i.e. α ~ Subtype β p for some p)
- for all a, b in α, a reduces to b in B iff a reduces to b in A
- if a is in α (i.e. `p a` holds) and a reduces to b in B, b is in α (i.e. `p b` holds).
-/
def ARS.is_sub_ars_of {p J} (A: ARS (@Subtype β p) I) (B: ARS β J) :=
  (∀a b, A.union_rel a b ↔ B.union_rel a b) ∧
  (∀a b, p a ∧ B.union_rel a b → p b)

section
variable {δ} {p : δ → Prop}
variable (C: ARS δ ι) (D: ARS (@Subtype δ p) κ)

#check D.is_sub_ars_of C

end
end ars_def

section rel_properties

local postfix:max (priority := high) "∗" => ReflTransGen
local postfix:max (priority := high) "⇔" => EqvGen
local postfix:max (priority := high) "⁼" => ReflGen

variable (r s : α → α → Prop)

/--
Two relations r and s commute weakly if `r a b` and `s a c`
imply the existence of a d s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def weakly_commutes :=
  ∀(a b c: α), r a b ∧ s a c → ∃d, s∗ b d ∧ r∗ c d

/--
Two relations r and s commute if `r∗ a b` and `s∗ a c` imply
the existence of a d s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def commutes :=
  ∀(a b c: α), r∗ a b ∧ s∗ a c → ∃d, s∗ b d ∧ r∗ c d

/-- Elementwise confluence (see `confluent`). -/
@[simp] def confluent' (a: α) : Prop :=
  ∀(b c : α), r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Confluence, also known as the Church-Rosser property. -/
@[simp] def confluent :=
  ∀(a b c : α), r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise weak confluence (see `weakly_confluent`). -/
@[simp] def weakly_confluent' (a: α) : Prop :=
  ∀(b c : α), r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Weak confluence, also known as local confluence or weak Church-Rosser. -/
@[simp] def weakly_confluent :=
  ∀(a b c : α), r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise diamond property (see `diamond_property`). -/
@[simp] def diamond_property' (a: α) : Prop :=
  ∀(b c: α), r a b ∧ r a c → ∃d, r b d ∧ r c d

@[simp] def diamond_property : Prop :=
  ∀(a b c: α), r a b ∧ r a c → ∃d, r b d ∧ r c d

-- Ensure that these definitions don't go out of sync:
#check (by simp : confluent r ↔ ∀a, confluent' r a)
#check (by simp : weakly_confluent r ↔ ∀a, weakly_confluent' r a)
#check (by simp : diamond_property r ↔ ∀a, diamond_property' r a)

/-- `ReflTransGen` is idempotent, i.e. applying it once is the same as applying it n>1 times. -/
lemma ReflTransGen.idempotent : ReflTransGen (ReflTransGen r) x y ↔ ReflTransGen r x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ a a_ih => apply ReflTransGen.trans a_ih a
  · intro h
    apply ReflTransGen.tail
    · apply ReflTransGen.refl
    · exact h

/- A few trivial equivalences relating confluence-adjacent properties. -/
lemma confluent_iff_star_weakly_confluent: confluent r ↔ weakly_confluent r∗ := by
  simp [ReflTransGen.idempotent]

lemma confluent_iff_star_self_commutes: confluent r ↔ commutes r∗ r∗ := by
  simp [ReflTransGen.idempotent]

lemma confluent_iff_star_dp: confluent r ↔ diamond_property r∗ := by
  rfl

/--
`semi_confluent` is equivalent to `confluent` (see `semi_confluent_iff_confluent`)
but is sometimes easier to prove as you can simply use induction on the length of `r∗ a b`.
-/
def semi_confluent := ∀a b c, r∗ a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

theorem semi_confluent_iff_confluent: semi_confluent r ↔ confluent r := by
  constructor
  · intro hosc
    rintro a b c ⟨hab, hac⟩
    induction hac with
    | refl => use b
    | tail _ hef ih =>
        rename_i e f _
        obtain ⟨d, hd⟩ := ih
        have ⟨g, hg⟩: ∃g, r∗ d g ∧ r∗ f g := hosc e d f ⟨hd.right, hef⟩
        have hbg: r∗ b g := ReflTransGen.trans hd.left hg.left
        exact ⟨g, ⟨hbg, hg.right⟩⟩
  · rintro hc a b c ⟨hab, hac⟩
    exact hc _ _ _ ⟨hab, ReflTransGen.single hac⟩

/-- "Conversion confluent" (made-up term); equivalent to confluence (see `conv_confluent_iff_confluent`). -/
def conv_confluent := ∀a b, r⇔ a b → ∃c, r∗ a c ∧ r∗ b c

/-- The reflexive-transitive closure of a relation is a subset of the equivalence closure. -/
lemma lift_rt_to_eqv : ∀a b, r∗ a b → r⇔ a b := by
  intro _ _ hrs
  induction hrs using ReflTransGen.trans_induction_on with
  | ih₁ a => exact EqvGen.refl a
  | ih₂ h => exact EqvGen.rel _ _ h
  | ih₃ _ _ he₁ he₂ => exact EqvGen.trans _ _ _ he₁ he₂

theorem conv_confluent_iff_confluent: conv_confluent r ↔ confluent r := by
  constructor
  · intro hcc
    rintro a b c ⟨hab, hac⟩
    apply hcc
    apply EqvGen.trans b a c
    · exact EqvGen.symm _ _ (lift_rt_to_eqv r a b hab)
    · exact lift_rt_to_eqv r a c hac
  · intro hcon
    rintro a b hab
    induction hab with
    | rel x y rxy =>
        have hrefl : r∗ x x := ReflTransGen.refl
        exact hcon x _ _ ⟨hrefl, ReflTransGen.single rxy⟩
    | refl x => exact (fun hrefl ↦ hcon x _ _ ⟨hrefl, hrefl⟩) ReflTransGen.refl
    | symm x y _ ih => tauto
    | trans x y z _ _ xy_ih yz_ih =>
        obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := xy_ih, yz_ih
        have ⟨e, he⟩ : ∃e, r∗ c e ∧ r∗ d e := hcon _ _ _ ⟨hc.right, hd.left⟩
        exact ⟨e, ⟨ReflTransGen.trans hc.left he.left,
                   ReflTransGen.trans hd.right he.right⟩⟩


end rel_properties


section reduction_seq

variable {α I}
variable (A: ARS α I)

/--
`ReductionSeq A is x y` represents a (finite) reduction sequence in `A`,
taking indexed reduction steps as given in `is` from `x` to `y`.

An empty reduction sequence is represented by `ReductionSeq.refl`, allowing a
reduction from `x` to `x` in 0 steps. Using `ReductionSeq.head`, a single step
`a ⇒[i] b` can be prepended to an existing reduction sequence.
-/
inductive ReductionSeq: List I → α → α → Prop
  | refl (x) : ReductionSeq [] x x
  | head {i x y z} : A.rel i x y → ReductionSeq is y z → ReductionSeq (i :: is) x z

theorem ReductionSeq.tail (hr : ReductionSeq A l a b) (hstep : A.rel i b c) : ReductionSeq A (l ++ [i]) a c := by
  induction hr with
  | refl => apply head hstep; exact refl c
  | head step _ ih => exact head step (ih hstep)

theorem ReductionSeq.concat : ReductionSeq A l x y → ReductionSeq A l' y z → ReductionSeq A (l ++ l') x z := by
  intro r₁ r₂
  induction r₁ with
  | refl a => rwa [List.nil_append]
  | head step _ ih => exact ReductionSeq.head step (ih r₂)

/-- A finite reduction sequence exists iff there is a reflexive-transitive reduction. -/
lemma ReductionSeq.exists_iff_union_rel_star {x y : α} : A.union_rel_star x y ↔ ∃is, ReductionSeq A is x y := by
  constructor <;> intro r
  · induction r using ReflTransGen.head_induction_on with
    | refl => use []; exact ReductionSeq.refl y
    | head step _ ih =>
        obtain ⟨is, h⟩ := ih
        obtain ⟨i, h'⟩ := step
        use (i :: is)
        apply ReductionSeq.head h' h
  · rcases r with ⟨is, r⟩
    induction r with
    | refl a => apply ReflTransGen.refl
    | head step _ ih =>
        apply ReflTransGen.head
        · exact Exists.intro _ step
        · exact ih


def ReductionSeq.labels : ReductionSeq A l x y → List I :=
  fun _ ↦ l

end reduction_seq

end Thesis
