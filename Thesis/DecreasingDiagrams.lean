import Mathlib.Logic.Relation
import Mathlib.Tactic
import Thesis.RelProps
import Thesis.ARS

namespace Thesis

variable {α: Type}

variable (A: ARS α Unit)

open Relation

local infixr:90 " • " => Rel.comp

/--
An ARS `B` is locally trace-decreasing (LTD) if it is indexed by a well-founded
partial order `(I, <)` such that every peak `c <-β a ->α b` can be joined
by reductions of the form

 - `b ->>_<α · ->⁼_β · ->>_{<α ∪ <β} d`
 - `c ->>_<β · ->⁼_α · ->>_{<α ∪ <β} d`
-/
def locally_decreasing [PartialOrder I] [IsWellFounded I (· < ·)] (B: ARS α I) :=
  ∀a b c i j, B.rel i a b ∧ B.rel j a c →
    ∃d, ((B.union_lt i)∗ • (B.rel j)⁼ • (B.union_lt i ∪ B.union_lt j)∗) b d ∧
        ((B.union_lt j)∗ • (B.rel i)⁼ • (B.union_lt i ∪ B.union_lt j)∗) c d

/--
An ARS `A` is called Decreasing Church-Rosser (DCR) if there exists a reduction-
equivalent ARS `B` which is locally decreasing.
-/
def DCR.{u} :=
  ∃(I: Type u) (_: PartialOrder I) (_: IsWellFounded I (· < ·)) (B: ARS α I),
    A.rel () = B.union_rel ∧ locally_decreasing B

/--
An ARS `A` is DCR with n labels if there exists a reduction-equivalent ARS `B`
which is indexed by `{ i | i < n }` which is locally decreasing.
-/
def DCRn (n: Ordinal) (A: ARS α Unit) :=
  ∃(B: ARS α { i | i < n }), A.rel () = B.union_rel ∧ locally_decreasing B

/--
If an ARS is DCRn, it is DCR.

It is somewhat unclear to me why we need these explicit universe annotations,
and Lean can't just figure it out on its own, but I suppose it doesn't matter.
-/
lemma DCRn_imp_DCR: DCRn.{u} n A → DCR.{u + 1} A := by
  intro h
  obtain ⟨B, hb⟩ := h
  simp [DCR]
  use {b | b < n}
  use inferInstance, inferInstance, B

/--
If all components of an ARS are locally decreasing, the whole ARS is locally decreasing.
-/
lemma locally_decreasing_components (n: ℕ) (B: ARS α { i | i < n }):
    (∀b, locally_decreasing (B.component b).ars) → locally_decreasing B := by
  intro hcomponent
  intro a b c i j ⟨hab, hac⟩

  have hconv₁: B.conv a a := EqvGen.refl a
  have hconv₂: B.conv a b := EqvGen.rel a b (Exists.intro i hab)
  have hconv₃: B.conv a c := EqvGen.rel a c (Exists.intro j hac)

  unfold locally_decreasing at hcomponent
  simp only [SubARS.restrict] at hcomponent

  have := hcomponent a ⟨a, hconv₁⟩ ⟨b, hconv₂⟩ ⟨c, hconv₃⟩ i j ⟨hab, hac⟩
  clear hcomponent

  set BS := B.component a
  obtain ⟨d, hd₁, hd₂⟩ := this
  use d

  -- The two goals are symmetric, so we can use the same proof procedure
  -- with h := hd₁ in the first goal, h := hd₂ in the second goal.
  constructor <;> [let h := hd₁; let h := hd₂]

  all_goals
    obtain ⟨s₁, hs₁, h⟩ := h
    use s₁
    simp [SubARS.star_restrict_union_lt] at hs₁
    use hs₁

    obtain ⟨s₂, hs₂, h⟩ := h
    use s₂

    constructor
    · cases hs₂ with
      | refl => use ReflGen.refl
      | single hs₂ =>
        rw [BS.restrict] at hs₂
        use ReflGen.single hs₂
    · eta_expand at h ⊢
      simp [BS.restrict_union_lt, Rel.instUnion, Rel.union] at h ⊢
      exact ReflTransGen.lift Subtype.val (fun _ _ a ↦ a) h

/-- Proof left as an exercise to the reader ;) -/
lemma DCR_imp_confluence: DCR A → confluent (A.rel ()) := by
  sorry

-- trivial example; i should find something actually interesting.
def example_ars: ARS ℕ Unit where
  rel := fun i x y ↦ x < y

example: DCRn 1 example_ars := by
  unfold DCRn
  use { rel := fun i x y ↦ x < y }
  unfold example_ars
  constructor
  · ext
    simp
  · unfold locally_decreasing
    intro a b c i j
    simp [Rel.comp, ARS.union_lt, Union.union, ReflGen]
    intro hab hac
    use (max b c) + 1
    constructor
    · use b, by rfl
      use (max b c) + 1
      constructor
      · apply ReflGen.single
        omega
      · rfl
    · use c, ReflTransGen.refl
      use (max b c) + 1
      constructor
      · apply ReflGen.single
        omega
      · rfl



-- Formalization of Proposition 14.2.30 from Terese.
section prop_14_2_30

@[simp]
def is_reduction_seq_from (a b: α) (f: ℕ → α) (N: ℕ) :=
  f 0 = a ∧ f N = b ∧ reduction_seq A.union_rel N f

-- There exists a reduction sequence from a to b
def exists_red_seq (a b: α): Prop :=
  ∃N f, is_reduction_seq_from A a b f N

/--
For any element a, and b in the reduction graph of a, there exists some
reduction seqence from a to b.
-/
lemma exists_red_seq_in_reduction_graph (a: α) (b: {b // A.union_rel∗ a b }):
    exists_red_seq A a b := by
  have ⟨b, hb⟩ := b
  induction hb with
  | refl =>
    use 0, (fun n ↦ a)
    simp [reduction_seq]
  | @tail b' c hseq hstep ih =>
    obtain ⟨N, f, hf₁, hf₂, hf₃⟩ := ih
    let f' : ℕ → α := fun n ↦ if n ≤ N then f n else c
    use N + 1, f'
    and_intros
    · simp only [zero_le, ↓reduceIte, hf₁, f']
    · simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte, f']
    · unfold reduction_seq at *
      intro n hn
      by_cases hn': (n = N)
      · subst hn'
        simp [f', hf₂]
        exact hstep
      · norm_cast at *
        have hn: n < N := by omega
        have hn₁: n ≤ N := by omega
        have hn₂: n + 1 ≤ N := by omega
        simp only [↓reduceIte, hn₁, hn₂, hf₃ _ hn, f']

open Classical in
noncomputable def d (a: α) (b: { b // A.union_rel∗ a b }): ℕ
  := Nat.find <| exists_red_seq_in_reduction_graph A a b

open Classical in
noncomputable def dX' (a: α) (X: Set { b // A.union_rel∗ a b}) (hX: X.Nonempty): ℕ
  := Nat.find (Set.image_nonempty.mpr hX : (d A a '' X).Nonempty)

noncomputable def dX (a: α) (X: Set α) (hX: ∃x ∈ X, A.union_rel∗ a x): ℕ
  := dX' A a {x | (x.val ∈ X)} (by have ⟨x, hx₁, hx₂⟩ := hX; use ⟨x, hx₂⟩, hx₁)



end prop_14_2_30



end Thesis
