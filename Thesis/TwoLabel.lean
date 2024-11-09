import Thesis.DecreasingDiagrams

namespace Thesis.TwoLabel

namespace Componentwise

-- We can reuse the notions of main road and rewrite distance from
-- the proof of proposition 14.2.30.
open RewriteDistance

open Relation

variable
  {α I: Type} {A: ARS α I}
  {C: Component A}
  (hcp: cofinality_property_conv A)

variable
  {N: ℕ∞} {f: ℕ → C.Subtype}
  (main_road: reduction_seq C.ars.union_rel N f)
  {hacyclic: main_road.acyclic}
  (hcr: cofinal_reduction main_road)


-- At some points we will require there to be a well-order on α.
-- Note that this can always be satisfied, by the well-ordering theorem
-- (see `exists_wellOrder`).
variable [LinearOrder α]

def on_main_road_imp_d0 {a} (heq: a ∈ main_road.elems):
    (dX a main_road.elems (hcr a)).val = 0 := by
  have: is_reduction_seq_from C.ars.union_rel a a (fun n ↦ a) 0 := by
    simp
    exact reduction_seq.refl C.ars.union_rel fun n ↦ a

  by_contra h
  have hzerolt: 0 < (dX a main_road.elems (hcr a)).val := by
    omega

  simp at heq
  obtain ⟨n, hlt, heq⟩ := heq

  apply dX.min _ _ 0 hzerolt
  use (fun n ↦ a)
  use a
  rw [<-heq]
  constructor
  · simp
    use n
  · rw [<-heq] at this
    exact this


def step_on_main_road_imp_step {a b: C.Subtype} (hs: main_road.contains a b): C.ars.union_rel a b := by
  simp [reduction_seq.contains] at hs
  obtain ⟨n, rfl, rfl, hlt⟩ := hs
  exact main_road n hlt

def step_minimizing (a b: C.Subtype) :=
  C.ars.union_rel a b ∧ (dX a main_road.elems (hcr a)).val = (dX b main_road.elems (hcr b)).val + 1 ∧ -- a -> b ∧ d(a) = d(b) + 1
  ∀b', C.ars.union_rel a b' ∧ (dX b main_road.elems (hcr b)).val = (dX b' main_road.elems (hcr b')).val → b' ≥ b -- for all b' s.t. a -> b' ∧ d(b) = d(b'), b' ≥ b.

def step_minimizing_imp_step {a b: C.Subtype} (hs: step_minimizing main_road hcr a b):
    C.ars.union_rel a b := by
  simp [step_minimizing] at hs
  tauto

def C': ARS C.Subtype (Fin 2) where
  rel := fun n b c ↦
    match n with
      | 0 => (main_road.contains b c ∨ step_minimizing main_road hcr b c)
      | 1 => C.ars.union_rel b c ∧ ¬(main_road.contains b c ∨ step_minimizing main_road hcr b c)


/-- Lemma 4.9(i): our labeled ARS is reduction-equivalent to C.ars. -/
lemma C'.reduction_equivalent (b c: C.Subtype):
    C.ars.union_rel b c ↔ (C' main_road hcr).union_rel b c := by
  constructor <;> intro h
  · simp only [C', ARS.union_rel]
    by_cases h: (main_road.contains b c ∨ step_minimizing main_road hcr b c)
    · use 0
    · use 1
  · simp [C', ARS.union_rel] at h
    obtain ⟨i, hi⟩ := h
    split at hi
    · cases hi
      · simp [step_on_main_road_imp_step main_road, *]
      · simp [step_minimizing_imp_step main_road, *]
    · simpa [ARS.union_rel] using hi.left

/-- Equivalent to steps_along_hseq in Prop 14.2.30. -/
lemma steps_on_main_road {n k: ℕ} (hk: n + k < N + 1):
    ((C' main_road hcr).rel 0)∗ (f n) (f (n + k)) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hlt: n + k < N := by
      cases h: N
      · norm_cast; exact WithTop.coe_lt_top _
      · rw [h] at hk
        norm_cast at hk ⊢
        omega
    have hlt': n + k < N + 1 := lt_of_lt_of_le hlt le_self_add
    apply ReflTransGen.tail (ih hlt')

    simp [C']
    left
    use (n + k)
    use rfl, rfl
    norm_cast

/-- Lemma 4.9(ii); if a, b ∈ M, ∃d, a ->>_0 d ∧ b ->>_0 d. -/
lemma L4_9_ii (a b: C.Subtype) (ha: a ∈ main_road.elems) (hb: b ∈ main_road.elems):
    ∃d, ((C' main_road hcr).rel 0)∗ a d ∧ ((C' main_road hcr).rel 0)∗ b d := by
  simp at ha hb

  obtain ⟨n₁, hlt₁, heq₁⟩ := ha
  obtain ⟨n₂, hlt₂, heq₂⟩ := hb

  wlog hn: n₁ ≤ n₂ generalizing a b n₁ n₂
  · obtain ⟨d, hd₁, hd₂⟩ := this b a n₂ hlt₂ heq₂ n₁ hlt₁ heq₁ (by linarith)
    use d, hd₂, hd₁

  obtain ⟨k, rfl⟩: ∃k, n₂ = n₁ + k := by
    exact Nat.exists_eq_add_of_le hn

  use b
  rw [<-heq₁, <-heq₂]

  constructor
  · apply steps_on_main_road
    norm_cast
  · rfl

include hacyclic in
/-- There is at most one b s.t. a ->₀ b. -/
lemma L4_9_iii {a b b': C.Subtype}:
    (C' main_road hcr).rel 0 a b ∧ (C' main_road hcr).rel 0 a b' → b = b' := by
  rintro ⟨hb, hb'⟩

  -- we distinguish between the case where a is on the main road, and the case
  -- where a is not on the main road.
  by_cases h: ∃n, a = f n ∧ n < N + 1
  · have hmem: a ∈ main_road.elems := by
      obtain ⟨n, hn⟩ := h
      use n
      tauto

    have d0 := on_main_road_imp_d0 main_road hcr hmem
    -- steps a->b and a->b' cannot be minimizing, as a = 0 and 0 cannot be n + 1.
    replace hb: main_road.contains a b := by
      apply hb.resolve_right
      rw [step_minimizing]
      omega

    replace hb': main_road.contains a b' := by
      apply hb'.resolve_right
      rw [step_minimizing]
      omega

    rw [reduction_seq.contains] at hb hb'
    obtain ⟨n, heqa₁, heqb, hlt₁⟩ := hb
    obtain ⟨n', heqa₂, heqb', hlt₂⟩ := hb'

    rw [<-heqb', <-heqb]
    congr
    apply hacyclic hlt₁ hlt₂
    rw [heqa₁, heqa₂]
  · replace hb: step_minimizing main_road hcr a b := by
      apply hb.resolve_left
      push_neg at h
      rintro ⟨n, hn⟩
      specialize h n hn.left.symm
      apply not_le_of_gt hn.2.2
      trans N + 1
      · apply le_self_add
      · exact h
    replace hb': step_minimizing main_road hcr a b' := by
      apply hb'.resolve_left
      push_neg at h
      rintro ⟨n, hn⟩
      specialize h n hn.left.symm
      apply not_le_of_gt hn.2.2
      trans N + 1
      · apply le_self_add
      · exact h

    unfold step_minimizing at *
    simp [-forall_exists_index] at hb hb'
    obtain ⟨hrel, heq, hgt⟩ := hb
    obtain ⟨hrel', heq', hgt'⟩ := hb'
    apply le_antisymm
    · apply hgt _ _ hrel'
      linarith
    · apply hgt' _ _ hrel
      linarith

variable [WellFoundedLT α]

lemma L4_9_iv (a: C.Subtype) (ha: a ∉ main_road.elems):
    ∃b, (C' main_road hcr).rel 0 a b ∧
      (dX a main_road.elems (hcr a)).val =
      (dX b main_road.elems (hcr b)).val + 1 := by
  obtain ⟨n, hdX⟩: ∃n, (dX a main_road.elems (hcr a)).val = n + 1 := by
    suffices: (dX a main_road.elems (hcr a)).val ≠ 0
    · exact Nat.exists_eq_succ_of_ne_zero this

    intro hdx
    have := dX.spec main_road.elems (hcr a)
    rw [hdx] at this

    obtain ⟨f, x, hxmem, hseq⟩ := this
    simp at ha hxmem

    unfold is_reduction_seq_from at hseq

    obtain ⟨n, hlt, heq⟩ := hxmem
    specialize ha n hlt
    apply ha
    rw [heq, <-hseq.left, <-hseq.right.left]

  obtain ⟨f, m, hmem, heq₁, heq₂, hseq⟩ := dX.spec main_road.elems (hcr a)
  have hrel: C.ars.union_rel (f 0) (f 1) := by
    apply hdX ▸ hseq; norm_num

  rw [hdX]

  have hdXb: dX (f 1) main_road.elems (hcr (f 1)) = n := by
    apply le_antisymm
    · apply dX_step_le hcr a m hmem
      and_intros
      · exact heq₁
      · exact hdX ▸ heq₂
      · exact hdX ▸ hseq
    · apply dX_step_ge hcr (f 0) (f 1)
      · exact hrel
      · exact heq₁ ▸ hdX

  -- there is at least one one-step reduct of a with d(a) = d(b) + 1.
  -- now we need to pick the minimal one. Here we need the well-order on α,
  -- because we need the property that there is a minimal α for any set.

  let B := { b' | C.ars.union_rel a b' ∧ (dX a main_road.elems (hcr a)).val = (dX b' main_road.elems (hcr b')).val + 1}

  have hnonempty: B.Nonempty := by
    use (f 1)
    and_intros
    · apply heq₁ ▸ hrel
    · rw [hdXb, hdX]

  have hwf: IsWellFounded C.Subtype (· < ·) := inferInstance

  obtain ⟨b, hbmem, hmin⟩ := hwf.wf.has_min B hnonempty
  dsimp only [B,  Set.mem_setOf_eq] at hbmem
  use b
  constructor
  · simp [C']
    right
    and_intros
    · exact hbmem.left
    · exact hbmem.right
    · rintro b' ⟨hb'rel, hb'dist⟩
      have := hmin b' ?_
      simp at this
      exact this
      use hb'rel
      rw [<-hb'dist]
      exact hbmem.right
  · rw [<-hbmem.right, hdX]


lemma L4_9_v (a: C.Subtype) (n: ℕ) (hn: n = dX a main_road.elems (hcr a)):
    ∃m ∈ main_road.elems, ((C' main_road hcr).rel 0)∗ a m := by
  induction n generalizing a with
  | zero =>
    have := dX.spec main_road.elems (hcr a)
    rw [<-hn] at this
    obtain ⟨f, m, hmem, hseq⟩ := this
    use m, hmem
    unfold is_reduction_seq_from at hseq
    rw [<-hseq.1, <-hseq.2.1]
  | succ n ih =>
    have := dX.spec main_road.elems (hcr a)
    obtain ⟨f', m, hmem, hseq⟩ := this

    have ha: a ∉ main_road.elems := by
      by_contra ha
      have := on_main_road_imp_d0 _ hcr ha
      omega

    obtain ⟨b, hbrel, hgt⟩ := L4_9_iv main_road hcr a ha

    obtain ⟨m', hmem', hseq⟩ := ih b (by omega)

    use m', hmem'

    apply ReflTransGen.head
    exact hbrel
    exact hseq

include hacyclic in
lemma C'.locally_decreasing: locally_decreasing (C' main_road hcr) := by
  rintro a b c i j ⟨hab, hac⟩

  by_cases heq: b = c
  · subst heq
    use b
    constructor <;>
    · use b, (by rfl), b

  have: i = 1 ∨ j = 1 := by
    by_contra!
    obtain ⟨rfl, rfl⟩: i = 0 ∧ j = 0 := by omega
    apply heq
    apply L4_9_iii main_road hcr ⟨hab, hac⟩
    assumption

  obtain ⟨mb, hmbmem, hmbseq⟩ := L4_9_v main_road hcr b (dX b main_road.elems (hcr b)) rfl
  obtain ⟨mc, hmcmem, hmcseq⟩ := L4_9_v main_road hcr c (dX c main_road.elems (hcr c)) rfl

  obtain ⟨d, hd₁, hd₂⟩ := L4_9_ii main_road hcr mb mc hmbmem hmcmem

  have (a b: C.Subtype): (C' main_road hcr).rel 0 a b → ((C' main_road hcr).union_lt i ∪ (C' main_road hcr).union_lt j) a b := by
    introv h
    rcases this with (rfl | rfl)
    · left
      use 0, (by norm_num)
    · right
      use 0, (by norm_num)


  use d
  constructor
  · use b, (by rfl), b, (by rfl)
    apply ReflTransGen.mono
    exact this
    trans mb
    exact hmbseq
    exact hd₁
  · use c, (by rfl), c, (by rfl)
    apply ReflTransGen.mono
    exact this
    trans mc
    exact hmcseq
    exact hd₂


end Componentwise

variable (A: ARS α I)

/--
If A has the cofinality property, any component of A is DCR₂.
-/
def dcr₂_component (hcp: cofinality_property A): ∀(C: Component A), DCRn 2 C.ars := by
  intro C
  unfold DCRn
  obtain ⟨linorder, wellfounded⟩ := exists_wellOrder α

  use Componentwise.C' (MainRoad.main_road C hcp.to_conv) (MainRoad.main_road_cr C hcp.to_conv)
  constructor
  · ext
    rw [<-Componentwise.C'.reduction_equivalent]
  · apply Componentwise.C'.locally_decreasing
    exact MainRoad.main_road_acyclic C hcp.to_conv

end Thesis.TwoLabel
