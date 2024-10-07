import Mathlib.Logic.Relation
import Mathlib.Tactic
import Thesis.RelProps

namespace Thesis

open Relation

section ars_def

/--
An Abstract Rewriting System (ARS), consisting of a set `α`, index type `I`
and an indexed set of rewrite relations on `α` over `I` (`ARS.rel`).
-/
structure ARS (α I : Type*) where
  rel : I → Rel α α

variable {α I}
variable (A : ARS α I)

/-- The union of the indexed relations of an ARS. -/
abbrev ARS.union_rel: Rel α α :=
  fun x y ↦ ∃i, A.rel i x y

/--
The convertability relation ≡ generated from the union of ARS relations.
Note that this is denoted using `=` in TeReSe, which we use for true equality.
-/
def ARS.conv: Rel α α :=
  EqvGen A.union_rel

/-- `x ⇒ y` means x one-step reduces to y. -/
local infixr:60 (priority := high) " ⇒ " => A.union_rel

/-- `x ⇒∗ y` means x reduces to y reflexive-transitively. -/
local infixr:60 (priority := high) " ⇒∗ " => A.union_rel∗

-- I don't love this notation, but oh well..
local notation:50 (priority := high) x:51 " ⇒[" i "]" y:50 => A.rel i x y
local notation:50 (priority := high) x:51 " ⇒∗[" i "]" y:50 => (A.rel i)∗ x y

/--
`S: ARS {a: α // p a} J` is a sub-ARS of `A: ARS α I` if:
- `S.union_rel` is the _restriction_ of `A.union_rel` to `{a // p a}`, that is
  `a` reduces to `b` in `S.union_rel` iff `a` reduces to `b` in `A.union_rel`.
- `S` is _closed_ under `A.union_rel`; if `a` reduces to `b` in `A.union_rel`
  and `a` is in `S`, `b` must be in `S`.
-/
structure SubARS (A: ARS α I) (p: α → Prop) (J) where
  ars : ARS {a: α // p a} J
  restrict: ∀a b, ars.union_rel a b ↔ A.union_rel a b
  closed: ∀a b, p a ∧ A.union_rel a b → p b

@[simp]
def SubARS.prop {A: ARS α I} (_: SubARS A p J) := p

/-- The sub-ARS generated by a subtype of β (represented by p) -/
def ARS.gen_sub (B: ARS β I) (p: β → Prop) : SubARS B (fun b ↦ ∃a, p a ∧ B.union_rel∗ a b) Unit :=
  { ars := ⟨fun _ a b ↦ B.union_rel a b⟩,
    restrict := by simp,
    closed := by
      rintro a b ⟨⟨a', ha'⟩, h₂⟩
      use a', ha'.left
      apply ReflTransGen.tail ha'.right h₂
  }

def ARS.reduction_graph (B: ARS β I) (b: β) : SubARS B (fun b' ↦ B.union_rel∗ b b') Unit := by
  have := ARS.gen_sub B (fun b' ↦ (b' = b))
  simpa [exists_eq_left]

/--
The restriction property of a sub-ARS extends to the reflexive-transitive closure
of the union of its reduction relations.
-/
lemma SubARS.star_restrict (S: SubARS A p J): (∀a b, S.ars.union_rel∗ a b ↔ A.union_rel∗ a b) := by
  intro a b
  constructor <;> intro h'
  · induction h' with
    | refl => exact ReflTransGen.refl
    | tail h₁ h₂ ih =>
      apply ReflTransGen.tail ih
      rwa [<-S.restrict]
  · rcases a with ⟨a', ha'⟩
    rcases b with ⟨b', hb'⟩
    simp [Subtype.mk] at h'
    induction h' using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | head h₁ _h₂ ih =>
      rename_i b c
      have hc : p c := S.closed b c ⟨ha', h₁⟩
      apply ReflTransGen.head _ (ih hc)
      simp [S.restrict]
      exact h₁

/--
The closure property of a sub-ARS extends to the reflexive-transitive closure
of the union of its reduction relations.
-/
lemma SubARS.star_closed (S: SubARS A p J): (∀a b, p a ∧ A.union_rel∗ a b → p b) := by
  rintro a b ⟨hpa, hab⟩
  induction hab with
  | refl => exact hpa
  | tail h₁ h₂ ih =>
      rename_i b c
      have := S.closed b c
      tauto

/-- A sub-ARS of a confluent ARS is confluent. -/
lemma SubARS.down_confluent (S: SubARS A p J): confluent (A.union_rel) → confluent (S.ars.union_rel) := by
  intro hc a b c hhyp
  have hhyp' : A.union_rel∗ a b ∧ A.union_rel∗ a c := by
    constructor <;> (rw [<-S.star_restrict _ a _]; simp only [hhyp])
  have ⟨d, hd⟩ := hc _ _ _ hhyp'
  have hpd : p d := S.star_closed _ b _ ⟨b.property, hd.left⟩
  use ⟨d, hpd⟩
  constructor <;> (simp [S.star_restrict _ _ ⟨d, hpd⟩]; simp [hd])

/-- A sub-ARS of a strongly normalizing ARS is strongly normalizing. -/
lemma SubARS.down_sn (S: SubARS A p J): strongly_normalizing (A.union_rel) -> strongly_normalizing (S.ars.union_rel) := by
  unfold strongly_normalizing
  intro hsn
  contrapose! hsn
  obtain ⟨f, hf⟩ := hsn
  use (λn => f n)
  intro n
  apply (S.restrict _ _).mp
  exact hf n

-- etc, sub-ARS also preserves WCR, subcommutative, DP, WN, WF, UN, NF, Ind, Inc, FB, CP
-- prove them as needed

end ars_def

end Thesis
