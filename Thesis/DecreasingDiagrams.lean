import Mathlib.Logic.Relation
import Mathlib.Tactic
import Thesis.RelProps
import Thesis.ARS
import Thesis.Cofinality

namespace Thesis

variable {α I: Type}

variable (A: ARS α I)

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

def stronger_decreasing (B: ARS α ℕ) :=
  ∀a b c i j, B.rel i a b ∧ B.rel j a c →
    ∃d, ((B.union_lt (max i j))∗) b d ∧ ((B.union_lt (max i j))∗) c d

lemma stronger_decreasing_imp_locally_decreasing (B: ARS α ℕ):
    stronger_decreasing B → locally_decreasing B := by
  intro h
  rintro a b c i j ⟨hab, hac⟩
  obtain ⟨d, hd₁, hd₂⟩ := h a b c i j ⟨hab, hac⟩
  use d
  constructor
  · use b, (by rfl), b, (by rfl)
    by_cases h: max i j = j
    · rw [h] at hd₁
      apply ReflTransGen.mono Rel.union_right hd₁
    · have: max i j = i := by
        omega
      rw [this] at hd₁
      apply ReflTransGen.mono Rel.union_left hd₁
  · use c, (by rfl), c, (by rfl)
    by_cases h: max i j = j
    · rw [h] at hd₂
      apply ReflTransGen.mono Rel.union_right hd₂
    · have: max i j = i := by
        omega
      rw [this] at hd₂
      apply ReflTransGen.mono Rel.union_left hd₂

/--
An ARS `A` is called Decreasing Church-Rosser (DCR) if there exists a reduction-
equivalent ARS `B` which is locally decreasing.
-/
def DCR :=
  ∃(I: Type) (_: PartialOrder I) (_: IsWellFounded I (· < ·)) (B: ARS α I),
    A.union_rel = B.union_rel ∧ locally_decreasing B

/--
An ARS `A` is DCR with n labels if there exists a reduction-equivalent ARS `B`
which is indexed by `{ i | i < n }` which is locally decreasing.
-/
def DCRn (n: ℕ) (A: ARS α I) :=
  ∃(B: ARS α (Fin n)), A.union_rel = B.union_rel ∧ locally_decreasing B

/--
If an ARS is DCRn, it is DCR.

It is somewhat unclear to me why we need these explicit universe annotations,
and Lean can't just figure it out on its own, but I suppose it doesn't matter.
-/
lemma DCRn_imp_DCR: DCRn n A → DCR A := by
  intro h
  obtain ⟨B, hb⟩ := h
  simp [DCR]
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  use B

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
-- lemma DCR_imp_confluence: DCR A → confluent (A.rel ()) := by
--   sorry

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


namespace MainRoad

variable
  {A: ARS α I}
  (C: Component A)
  (hcp: cofinality_property_conv A)

include hcp in
lemma exists_dcr_main_road:
    ∃N f, ∃(hseq: reduction_seq C.ars.union_rel N f),
      cofinal_reduction hseq ∧ hseq.acyclic := by
  obtain ⟨x, hx⟩ := C.component_nonempty

  have hxeq: C = (A.component x) := (component_mem_eq hx).symm

  obtain ⟨N, f, hseq, hcf, -⟩ := hxeq ▸ hcp x
  obtain ⟨N, f, hseq, hcf, hacyclic⟩ := cofinal_reduction_acyclic hseq hcf
  use N, f, hseq

def main_road :=
  (exists_dcr_main_road C hcp).choose_spec.choose_spec.choose

def main_road_cr :=
  (exists_dcr_main_road C hcp).choose_spec.choose_spec.choose_spec.left

noncomputable def main_road_len :=
  (exists_dcr_main_road C hcp).choose

noncomputable def main_road_f :=
  (exists_dcr_main_road C hcp).choose_spec.choose

def main_road_acyclic :=
  (exists_dcr_main_road C hcp).choose_spec.choose_spec.choose_spec.right


end MainRoad

namespace RewriteDistance

@[simp]
def is_reduction_seq_from (r: Rel α α) (a b: α) (f: ℕ → α) (N: ℕ) :=
  f 0 = a ∧ f N = b ∧ reduction_seq r N f

/--
If some element in X is a reduct of a, there must be a reduction sequence
from a to some x in X.
-/
lemma exists_red_seq_set (X: Set α) (hX: ∃x ∈ X, r∗ a x):
    ∃N f x, x ∈ X ∧ is_reduction_seq_from r a x f N := by
  have ⟨x, hmem, hx⟩ := hX
  induction hx using ReflTransGen.head_induction_on with
  | refl =>
    use 0, (fun n ↦ x), x, hmem
    simp [is_reduction_seq_from]
    apply reduction_seq.refl
  | @head b c rel₁ rel₂ ih =>
    have: ∃x ∈ X, r∗ c x := by use x
    have ⟨N, f, x', hx', hseq⟩ := ih this
    let f' := fun n ↦ if n = 0 then b else f (n - 1)
    use N + 1, f', x', hx'
    and_intros
    · simp only [↓reduceIte, f']
    · simp [f']
      exact hseq.2.1
    · intro n hn
      cases n
      · simp [f', hseq.1, rel₁]
      · simp [f']
        exact hseq.2.2 _ (by norm_cast at hn ⊢; omega)

open Classical in
noncomputable def dX (a: α) (X: Set α) (hX: ∃x ∈ X, r∗ a x)
  := Nat.findX <| exists_red_seq_set X hX

lemma dX.spec (X: Set α) (hX: ∃x ∈ X, r∗ a x):
    ∃f x, x ∈ X ∧ is_reduction_seq_from r a x f (dX a X hX) :=
  (dX a X hX).prop.left

lemma dX.min (X: Set α) (hX: ∃x ∈ X, r∗ a x):
    ∀ m < ↑(dX a X hX), ¬∃ f, ∃ x ∈ X, is_reduction_seq_from r a x f m :=
  (dX a X hX).prop.right

section step
open MainRoad

variable {A: ARS α I} {C: Component A} (hcp: cofinality_property_conv A)

/--
If `a -> b` and the minimal distance from `a` to the main road is `n + 1`, the
distance from `b` to the main road must be at least `n`. (If not, `a` could go
via `b` and arrive at the main road earlier.)
-/
lemma dX_step_ge (a b: C.Subtype) (hrel: C.ars.union_rel a b) {n: ℕ} (hdX: dX a (main_road C hcp).elems (main_road_cr C hcp a) = n + 1):
    dX b (main_road C hcp).elems (main_road_cr C hcp b) ≥ n := by

  let dXb := dX b (main_road C hcp).elems (main_road_cr C hcp b)
  by_contra! hlt

  -- there is a length-d(b) path from b to m ∈ M
  have ⟨f, x, hmem, heq₁, heq₂, hseq⟩ := dX.spec _ (main_road_cr C hcp b)

  -- d(a) is minimal, so there cannot be a path with length d(b) + 1, because d(b) < n.
  have hmin := dX.min _ (main_road_cr C hcp a) (dXb.val + 1) (by unfold_let; rw [hdX]; omega)

  push_neg at hmin

  let total_f' := fun n ↦ if n = 0 then a else f (n - 1)

  apply hmin total_f' x hmem

  and_intros
  · simp [total_f']
  · simp only [is_reduction_seq_from,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, total_f', dXb]
    exact heq₂
  · intro n hn
    norm_cast at hn
    cases n with
    | zero =>
      simp [total_f', heq₁, hrel]
    | succ n =>
      simp [total_f']
      apply hseq
      norm_cast
      dsimp only [dXb] at hn
      linarith

/--
If there is a length-`n + 1` path from `a` to the main road, and `b` lies on the
path from `a` to the main road, the minimal distance from `b` to the main road
is at most `n`, since the path without its head is a length-`n` path from `b` to
the main road.
-/
lemma dX_step_le (a x: C.Subtype) (hx: x ∈ (main_road C hcp).elems) {f: ℕ → C.Subtype} {n: ℕ} (hseq: is_reduction_seq_from C.ars.union_rel a x f (n + 1)):
    dX (f 1) (main_road C hcp).elems (main_road_cr C hcp _) ≤ n := by

  let f' := fun n ↦ f (n + 1)
  have: is_reduction_seq_from C.ars.union_rel (f 1) x f' n := by
    and_intros
    · dsimp [f']
    · simpa [f'] using hseq.right.left
    · intro m hm
      simp [f']
      apply hseq.right.right
      norm_cast at hm ⊢
      omega

  by_contra! hgt
  apply dX.min (main_road C hcp).elems (main_road_cr C hcp (f 1)) n hgt
  use f', x

end step

end RewriteDistance



-- Formalization of Proposition 14.2.30 from Terese.
namespace Prop14230

section componentwise
open MainRoad
open RewriteDistance

variable
  {A: ARS α I}
  (C: Component A)
  (hcp: cofinality_property_conv A)

def red_step_in_seq {f: ℕ → α} (b c: α) (hseq: reduction_seq r N f) :=
  ∃(n: ℕ) (hn: n < N), b = f n ∧ c = f (n + 1)

lemma red_step_in_seq.is_red_step {b c: α} {r: Rel α α} {f: ℕ → α} {hseq: reduction_seq r N f}:
    red_step_in_seq b c hseq → (r b c) := by
  rintro ⟨n, ⟨hn, hb, hc⟩⟩
  aesop

def dcr_component_ars: ARS C.Subtype ℕ where
  rel := fun n b c ↦
    match n with
      | 0 => red_step_in_seq b c (main_road C hcp)
      | n + 1 => C.ars.union_rel b c ∧ n = dX c (main_road C hcp).elems ((main_road_cr C hcp) c)

/--
If `f (n + k)` is within our sequence, we can take `k` `0`-steps from `f n` to `f (n + k)`.
-/
lemma steps_along_hseq {n k: ℕ} (hk: n + k < (main_road_len C hcp) + 1):
    ((dcr_component_ars C hcp).rel 0)∗ ((main_road_f C hcp) n) ((main_road_f C hcp) (n + k)) := by
  set N := (main_road_len C hcp) with N_def
  set f := (main_road_f C hcp) with f_def

  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hlt: n + k < N := by
      cases h: N <;> (rw [h] at hk ih N_def; norm_cast at *)
      · apply WithTop.coe_lt_top
      · omega
    have hlt': n + k < N + 1 := lt_of_lt_of_le hlt le_self_add
    apply ReflTransGen.tail (ih hlt')
    use (n + k)
    simp_all only [SubARS.Subtype, Nat.cast_add, Nat.cast_one, exists_and_left, exists_prop, N, f]
    and_intros <;> first | rfl | exact hlt

/--
`dcr_component_ars` is reduction-equivalent to the component of A it stems from.
-/
lemma dcr_component_ars.reduction_equivalent (b c: C.Subtype):
    C.ars.union_rel b c ↔ (dcr_component_ars C hcp).union_rel b c := by
  constructor <;> intro h
  · simp only [dcr_component_ars, ARS.union_rel]

    let n := dX c (main_road C hcp).elems (main_road_cr C hcp c)
    use (n + 1)
  · simp only [dcr_component_ars, ARS.union_rel] at h
    obtain ⟨n, hn⟩ := h
    split at hn
    · exact hn.is_red_step
    · tauto

/--
One of the main parts of the proof for 14.2.30: if the distance from `b` to some
`x ∈ X` is `n`, there is a reduction sequence from `b` to `x` using steps with indices
smaller than `n + 1`.
-/
lemma dX_imp_red_seq (n: ℕ) (b: C.Subtype):
    dX b (main_road C hcp).elems (main_road_cr C hcp b) = n →
      ∃x f, x ∈ (main_road C hcp).elems ∧ f 0 = b ∧ f n = x ∧
      reduction_seq ((dcr_component_ars C hcp).union_lt (n + 1)) n f := by
  let hcr := main_road_cr C hcp
  let hseq := main_road C hcp

  intro h
  induction n generalizing b with
  | zero =>
    obtain ⟨f, x, hfx⟩ := dX.spec hseq.elems (hcr b)
    rw [h] at hfx
    simp at hfx
    obtain ⟨hmem, hfeq₁, hfeq₂, hseq⟩ := hfx
    use x, f, hmem, hfeq₁, hfeq₂
    apply reduction_seq.refl
  | succ n ih =>
    obtain ⟨f, x, hmem₁, heq₁, heq₂, hseq'⟩ := dX.spec hseq.elems (hcr b)

    have hpath: ∃x ∈ (main_road C hcp).elems, C.ars.union_rel∗ (f 1) x := by
      use x, hmem₁
      rw [<-heq₂]
      apply hseq'.star
      norm_cast
      norm_num
      omega

    have: (dX (f 1) _ hpath) = n := by
      apply Nat.le_antisymm
      · apply dX_step_le hcp b x hmem₁ ⟨heq₁, ⟨h ▸ heq₂, h ▸ hseq'⟩⟩
      · apply dX_step_ge hcp b (f 1) _ h
        rw [<-heq₁]
        apply hseq'
        rw [h]
        norm_cast
        norm_num

    have hrel: (dcr_component_ars C hcp).rel (n + 1) b (f 1) := by
      simp only [dcr_component_ars]
      constructor
      · rw [<-heq₁]
        apply hseq'
        rw [h]
        norm_num
      · exact this.symm

    have ⟨x, f', hmem, tail_heq₁, tail_heq₂, tail_hseq⟩ := ih (f 1) this

    -- sketch: we now have the tail of the sequence, need to prepend a single
    -- step of b -> f 1 (hrel)

    let total_f := fun n ↦ if n = 0 then f 0 else f' (n - 1)

    use x, total_f, hmem, heq₁, tail_heq₂

    intro i hi
    cases i with
    | zero =>
      simp [total_f, tail_heq₁]
      use n + 1, by omega
      rw [heq₁]
      exact hrel
    | succ i =>
      dsimp only [SubARS.Subtype, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
        ↓dreduceIte, Nat.add_one_sub_one, and_self, total_f]
      obtain ⟨idx, hidx⟩ := tail_hseq i (by norm_cast at hi ⊢; omega)
      use idx, (by omega), hidx.right

lemma dcr_component_ars.is_stronger_decreasing:
    stronger_decreasing (dcr_component_ars C hcp) := by
  rintro b c d i j ⟨hbc, hbd⟩

  set N := main_road_len C hcp with N_def
  set f := main_road_f C hcp with f_def

  wlog hij: i ≤ j generalizing i j c d
  · have ⟨d, hd⟩ := this d c j i hbd hbc (by omega)
    use d
    rw [max_comm] at hd
    tauto

  have htail: ∀(x y: ℕ) (hx: x < N + 1) (hy: y < N + 1), ((dcr_component_ars C hcp).rel 0)∗ (f x) (f (max x y)) := by
    intro x y hx hy
    have ⟨k, hk⟩: ∃k, (max x y) = x + k := by
      apply Nat.exists_eq_add_of_le
      omega

    rw [hk]
    apply steps_along_hseq
    norm_cast
    rw [<-hk]

    rw [<-N_def]
    revert hx hy
    cases N
    · simp
    · norm_cast at *
      omega

  rcases i with (- | i) <;> rcases j with (- | j)
  · -- coincide, hseq is acyclic
    simp [dcr_component_ars, red_step_in_seq] at hbc hbd
    obtain ⟨n, hbeq, hn, hceq⟩ := hbc
    obtain ⟨m, hbeq', hm, hdeq⟩ := hbd
    have: c = d := by
      have heq := (main_road_acyclic C hcp) hn hm (by aesop)
      subst heq
      rw [hceq, hdeq]
    subst this
    use c
  · -- i = 0, j > 0
    dsimp only [dcr_component_ars, red_step_in_seq] at hbd hbc
    obtain ⟨x, g, hxmem, hdeq, hxeq, hseq'⟩ := dX_imp_red_seq C hcp _ _ hbd.2.symm

    simp at hxmem

    obtain ⟨idx₁, hidx₁, heq_idx₁⟩ := hxmem
    obtain ⟨idx₂, hidx₂, heq_idx₂⟩ := hbc

    let hend_idx := max idx₁ (idx₂ + 1)
    use f hend_idx

    have hctail: ((dcr_component_ars C hcp).rel 0)∗ c (f hend_idx) := by
      rw [heq_idx₂.2]
      have := htail (idx₂ + 1) _ ?_ hidx₁
      rw [max_comm] at this
      apply this
      push_cast
      exact WithTop.add_lt_add_right WithTop.one_ne_top hidx₂

    have hxtail: ((dcr_component_ars C hcp).rel 0)∗ x (f hend_idx) := by
      rw [<-heq_idx₁]
      have := htail idx₁ (idx₂ + 1) hidx₁
      apply this
      push_cast
      exact WithTop.add_lt_add_right WithTop.one_ne_top hidx₂

    constructor
    · apply ReflTransGen.mono _ hctail
      intro x y h
      use 0, by omega
    · trans x
      · rw [<-hdeq, <-hxeq]
        apply hseq'.star
        norm_cast; norm_num; norm_num
      · apply ReflTransGen.mono _ hxtail
        intro x y h
        use 0, by omega

  · contradiction
  · -- i > 0, j > 0; they both lead to some element a_m, a_n in the CRS
    -- so they converge at a_(max m n).
    dsimp only [dcr_component_ars] at hbc hbd
    obtain ⟨x, g, hxmem, hdeq, hxeq, hseq₁⟩ := dX_imp_red_seq C hcp _ _ hbd.2.symm
    obtain ⟨y, h, hymem, hceq, hyeq, hseq₂⟩ := dX_imp_red_seq C hcp _ _ hbc.2.symm

    simp at hxmem hymem
    obtain ⟨idx₁, hidx₁, heq_idx₁⟩ := hxmem
    obtain ⟨idx₂, hidx₂, heq_idx₂⟩ := hymem

    use f (max idx₁ idx₂)
    constructor <;> [
      (let elem := y; let eq₁ := hceq; let eq₂ := hyeq; let seq := hseq₂;
       let i₁ := hidx₂; let i₂ := hidx₁; let ieq := heq_idx₂);
      (let elem := x; let eq₁ := hdeq; let eq₂ := hxeq; let seq := hseq₁;
       let i₁ := hidx₁; let i₂ := hidx₂; let ieq := heq_idx₁; rw [max_comm])]

    all_goals (
      trans elem
      · simp_rw [elem, <-eq₁, <-eq₂]
        apply ReflTransGen.mono (dcr_component_ars C hcp).union_lt_max
        apply seq.star
        norm_cast
        all_goals omega
      · have := htail _ _ i₁ i₂
        rw [f_def, main_road_f, ieq] at this
        simp [max_comm] at this
        apply ReflTransGen.mono _ this
        intro x y h
        use 0, by omega)

/--
`dcr_component_ars` is locally decreasing.
-/
lemma dcr_component_ars.is_ld:
    locally_decreasing (dcr_component_ars C hcp) := by
  apply stronger_decreasing_imp_locally_decreasing
  exact is_stronger_decreasing C hcp

/--
If A has the cofinality property, any component of A is DCR.
-/
def dcr_component (hcp: cofinality_property A): ∀(C: Component A), DCR C.ars := by
  intro C
  -- we use the natural numbers as labels, with the expected partial order
  use ℕ, inferInstance, inferInstance

  use dcr_component_ars C hcp.to_conv
  constructor
  · ext
    rw [<-dcr_component_ars.reduction_equivalent]
  · apply dcr_component_ars.is_ld

end componentwise

open Classical in
def dcr_total_ars (hcp': cofinality_property_conv A): ARS α ℕ where
  rel := fun n b c ↦
    ∃(C: Component A) (h: C.p b ∧ C.p c),
      (dcr_component_ars C hcp').rel n ⟨b, h.1⟩ ⟨c, h.2⟩


def dcr_total.reduction_equivalent:
    A.union_rel = (dcr_total_ars A hcp').union_rel := by
  ext a b
  constructor
  · intro h
    simp [ARS.union_rel, dcr_total_ars]

    have hbmem: (A.component a).p b := EqvGen.rel _ _ h

    let a': (A.component a).Subtype := ⟨a, A.component_root_mem⟩
    let b': (A.component a).Subtype := ⟨b, hbmem⟩

    have := dcr_component_ars.reduction_equivalent (A.component a) hcp' a' b'
    rw [SubARS.restrict_union] at this
    obtain ⟨i, h⟩ := this.mp h

    use i, (A.component a), ⟨a'.prop, b'.prop⟩
  · intro h
    rcases h with ⟨i, C, ⟨ha, hb⟩, hrel⟩
    have: (dcr_component_ars C hcp').union_rel ⟨a, ha⟩ ⟨b, hb⟩ := ⟨i, hrel⟩
    rwa [<-dcr_component_ars.reduction_equivalent, SubARS.restrict_union] at this


/--
The dcr_total_ars is locally decreasing. This follows from the fact that each
component is locally decreasing, any diverging steps z <-j x i-> y must be
within one component, and thus have a decreasing diagram from z ->> d <<- y.
-/
def dcr_total.is_ld:
    locally_decreasing (dcr_total_ars A hcp') := by
  apply stronger_decreasing_imp_locally_decreasing
  intro x y z i j ⟨hxy, hxz⟩

  -- Without loss of generality i ≤ j, by symmetry of the diverging steps.
  wlog hij: i ≤ j generalizing i j y z
  · have ⟨d, hd⟩ := this z y j i hxz hxy (by omega)
    aesop (add norm max_comm)

  -- A step within a component also exists within the total ARS.
  have hunion_lt {C: Component A} (i) (a b):
      (dcr_component_ars C hcp').union_lt i a b → (dcr_total_ars A hcp').union_lt i a b := by
    rintro ⟨j, hjlt, hjrel⟩
    use j, hjlt, C
    aesop

  -- x i-> y in some component C, and x j-> z in some component C₂
  simp [dcr_total_ars] at hxy hxz
  obtain ⟨C, ⟨hx, hy⟩, hxy⟩ := hxy
  obtain ⟨C₂, ⟨hx₂, hz⟩, hxz⟩ := hxz

  -- because x is in both components, the components must be the same.
  have heq: C = C₂ := component_unique x hx hx₂
  subst heq

  -- then by LD of an individual component (actually SD, but who's counting),
  -- there is a reduct d of y and z, which we can reach using only steps `<j`.
  obtain ⟨d, hyd, hzd⟩
    := dcr_component_ars.is_stronger_decreasing C hcp' ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ i j ⟨hxy, hxz⟩

  use d
  simp [hij] at hyd hzd ⊢
  rw [(by simp: y = Subtype.val ⟨y, hy⟩), (by simp: z = Subtype.val ⟨z, hz⟩)]

  -- the reduction sequences from y to d and z to d follow by lifting
  -- `hyd` and `hzd` from the component into the total ARS.
  constructor <;>
  · apply ReflTransGen.lift _ (hunion_lt j) _
    assumption


/--
Proposition 14.2.30: Any ARS with the cofinality property is DCR.
-/
def cp_imp_dcr (hcp: cofinality_property A): DCR A := by
  use ℕ, inferInstance, inferInstance

  use (dcr_total_ars A hcp.to_conv)
  constructor
  · exact dcr_total.reduction_equivalent A
  · exact dcr_total.is_ld A


end Prop14230

end Thesis
