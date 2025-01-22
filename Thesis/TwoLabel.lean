import Thesis.DecreasingDiagrams

namespace Thesis.TwoLabel

namespace SingleComponent

-- We can reuse the notions of main road and rewrite distance from
-- the proof of proposition 14.2.30.
open RewriteDistance

open Relation

variable
  {α I: Type} {A: ARS α I}
  {C: Component A}
  (hcp: cofinality_property_conv A)
  {N: ℕ∞} {f: ℕ → C.Subtype}
  (main_road: reduction_seq C.ars.union_rel N f)
  {hacyclic: main_road.acyclic}
  (hcr: cofinal_reduction main_road)
  (a b: C.Subtype)


-- At some points we will require there to be a well-order on α.
-- Note that this can always be satisfied, by the well-ordering theorem
-- (see `exists_wellOrder`).
variable [LinearOrder α]

def d0_of_on_main_road {a} (hmem: a ∈ main_road.elems):
    (dX a main_road.elems (hcr a)).val = 0 := by
  have: is_reduction_seq_from C.ars.union_rel a a (fun n ↦ a) 0 := by
    simp

  by_contra h
  replace h: 0 < (dX a main_road.elems (hcr a)).val := by
    omega

  apply dX.min _ _ 0 h
  use (fun n ↦ a), a, hmem


def step_minimizing (a b: C.Subtype) :=
  (dX a main_road.elems (hcr a)).val = (dX b main_road.elems (hcr b)).val + 1 ∧
  ∀b', C.ars.union_rel a b' →
    (dX b main_road.elems (hcr b)).val = (dX b' main_road.elems (hcr b')).val → b' ≥ b

def C': ARS C.Subtype (Fin 2) where
  rel := fun n b c ↦
    match n with
      | 0 => C.ars.union_rel b c ∧ (main_road.contains b c ∨ step_minimizing main_road hcr b c)
      | 1 => C.ars.union_rel b c ∧ ¬(main_road.contains b c ∨ step_minimizing main_road hcr b c)


/-- Lemma 4.9(i): our labeled ARS is reduction-equivalent to C.ars. -/
lemma C'.reduction_equivalent (b c: C.Subtype):
    C.ars.union_rel b c ↔ (C' main_road hcr).union_rel b c := by
  constructor <;> intro h
  · simp only [C', ARS.union_rel]
    by_cases h: (main_road.contains b c ∨ step_minimizing main_road hcr b c)
    · use 0
    · use 1
  · dsimp [C', ARS.union_rel] at h
    obtain ⟨i, hi⟩ := h
    split at hi <;> tauto

/-- Equivalent to steps_along_hseq in Prop 14.2.30. -/
lemma steps_on_main_road {n k: ℕ} (hk: n + k < N + 1):
    ((C' main_road hcr).rel 0)∗ (f n) (f (n + k)) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hlt: n + k < N := by
      cases N
      · norm_cast; exact WithTop.coe_lt_top _
      · norm_cast at hk ⊢
        omega
    have hlt': n + k < N + 1 := lt_of_lt_of_le hlt le_self_add
    apply ReflTransGen.tail (ih hlt')

    simp [C']
    have: main_road.contains (f (n + k)) (f (n + (k + 1))) := by
      use (n + k), rfl, rfl
      norm_cast

    refine ⟨?_, ?_⟩
    · convert main_road.contains_step this
      simp
    · left; exact this

/-- Lemma 4.9(ii); if a, b ∈ M, ∃d, a ->>_0 d ∧ b ->>_0 d. -/
lemma main_road_join (ha: a ∈ main_road.elems) (hb: b ∈ main_road.elems):
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
/-- Lemma 4.9 (iii): There is at most one b s.t. a ->₀ b. -/
lemma zero_step_unique {a b b'}:
    (C' main_road hcr).rel 0 a b ∧ (C' main_road hcr).rel 0 a b' → b = b' := by
  rintro ⟨hb, hb'⟩

  -- we distinguish between the case where a is on the main road, and the case
  -- where a is not on the main road.
  by_cases h: ∃n, a = f n ∧ n < N + 1
  · have hmem: a ∈ main_road.elems := by
      obtain ⟨n, hn⟩ := h
      use n
      tauto

    have d0 := d0_of_on_main_road main_road hcr hmem

    -- steps a->b and a->b' cannot be minimizing, as d(a) = 0 and 0 cannot be n + 1.
    replace hb: main_road.contains a b := by
      apply hb.right.resolve_right
      rw [step_minimizing]
      omega

    replace hb': main_road.contains a b' := by
      apply hb'.right.resolve_right
      rw [step_minimizing]
      omega

    rw [reduction_seq.contains] at hb hb'
    obtain ⟨n, heqa₁, heqb, hlt₁⟩ := hb
    obtain ⟨n', heqa₂, heqb', hlt₂⟩ := hb'

    rw [<-heqb', <-heqb]
    congr
    apply hacyclic hlt₁ hlt₂
    rw [heqa₁, heqa₂]
  · replace hb: C.ars.union_rel a b ∧ step_minimizing main_road hcr a b := by
      refine ⟨hb.left, hb.right.resolve_left ?_⟩
      push_neg at h
      rintro ⟨n, hn⟩
      specialize h n hn.left.symm
      apply not_le_of_gt hn.2.2
      trans N + 1
      · apply le_self_add
      · exact h
    replace hb': C.ars.union_rel a b' ∧ step_minimizing main_road hcr a b' := by
      refine ⟨hb'.left, hb'.right.resolve_left ?_⟩
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

lemma exists_distance_decreasing_step (a: C.Subtype) (ha: a ∉ main_road.elems):
    ∃b, (C' main_road hcr).rel 0 a b ∧
      (dX a main_road.elems (hcr a)).val =
      (dX b main_road.elems (hcr b)).val + 1 := by
  obtain ⟨n, hdX⟩: ∃n, (dX a main_road.elems (hcr a)).val = n + 1 := by
    suffices: (dX a main_road.elems (hcr a)).val ≠ 0
    · exact Nat.exists_eq_succ_of_ne_zero this

    contrapose! ha
    obtain ⟨f', x, hmem, rfl, rfl, hseq⟩ := ha ▸ dX.spec main_road.elems (hcr a)
    exact hmem

  obtain ⟨f, m, hmem, heq₁, heq₂, hseq⟩ := dX.spec main_road.elems (hcr a)
  have hrel: C.ars.union_rel (f 0) (f 1) := by
    apply hdX ▸ hseq; norm_num

  rw [hdX]

  have hdXb: dX (f 1) main_road.elems (hcr (f 1)) = n := by
    apply le_antisymm
    · apply dX_step_le (f 1) m hmem (f := fun n ↦ f (n + 1))
      and_intros
      · rfl
      · simp only [hdX ▸ heq₂]
      · intro n' hlt
        apply hseq
        norm_cast at hlt ⊢
        omega
    · apply dX_step_ge (f 0) (f 1) (hcr (f 0)) (hcr (f 1))
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
    refine ⟨?_, Or.inr ?_⟩
    simpa using hbmem.left
    and_intros
    · exact hbmem.right
    · intro b' hb'rel hb'dist
      have := hmin b' ?_
      simpa using this
      use hb'rel
      rw [<-hb'dist]
      exact hbmem.right
  · rw [<-hbmem.right, hdX]


private lemma main_road_reduction_aux (a: C.Subtype) (n: ℕ) (hn: n = dX a main_road.elems (hcr a)):
    ∃m ∈ main_road.elems, ((C' main_road hcr).rel 0)∗ a m := by
  induction n generalizing a with
  | zero =>
    have := dX.spec main_road.elems (hcr a)
    rw [<-hn] at this
    obtain ⟨f, m, hmem, hseq⟩ := this
    use m, hmem
    rw [<-hseq.1, <-hseq.2.1]
  | succ n ih =>
    by_cases ha: a ∈ main_road.elems
    · use a

    obtain ⟨b, hbrel, hgt⟩ := exists_distance_decreasing_step main_road hcr a ha
    obtain ⟨m', hmem', hseq⟩ := ih b (by omega)

    use m', hmem'
    apply ReflTransGen.head hbrel hseq

/--
Lemma 4.9 (v):
Every element `a` reduces to some element in the main road using only 0-steps.
-/
lemma main_road_reduction (a: C.Subtype):
    ∃m ∈ main_road.elems, ((C' main_road hcr).rel 0)∗ a m := by
  apply main_road_reduction_aux main_road hcr a (dX a main_road.elems (hcr a)).val
  rfl


include hacyclic in
lemma C'.stronger_decreasing: stronger_decreasing (C' main_road hcr) := by
  rintro a b c i j ⟨hab, hac⟩

  by_cases heq: b = c
  · subst heq
    use b

  have: i = 1 ∨ j = 1 := by
    by_contra!
    obtain ⟨rfl, rfl⟩: i = 0 ∧ j = 0 := by omega
    apply heq
    apply zero_step_unique main_road hcr ⟨hab, hac⟩
    assumption

  obtain ⟨mb, hmbmem, hmbseq⟩ := main_road_reduction main_road hcr b
  obtain ⟨mc, hmcmem, hmcseq⟩ := main_road_reduction main_road hcr c

  obtain ⟨d, hd₁, hd₂⟩ := main_road_join main_road hcr mb mc hmbmem hmcmem

  have (a b: C.Subtype): (C' main_road hcr).rel 0 a b → ((C' main_road hcr).union_lt (max i j)) a b := by
    introv h
    rcases this with (rfl | rfl)
    · use 0, (by norm_num)
    · use 0, (by norm_num)

  use d
  constructor
  · apply ReflTransGen.mono
    exact this
    trans mb
    exact hmbseq
    exact hd₁
  · apply ReflTransGen.mono
    exact this
    trans mc
    exact hmcseq
    exact hd₂


end SingleComponent

variable {α I: Type} (A: ARS α I)

/--
If A has the cofinality property, any component of A is DCR₂.
-/
lemma dcr₂_component (hcp: cofinality_property A): ∀(C: Component A), DCRn 2 C.ars := by
  intro C
  unfold DCRn
  obtain ⟨linorder, wellfounded⟩ := exists_wellOrder α

  use SingleComponent.C' (MainRoad.seq C hcp.to_conv) (MainRoad.is_cr C hcp.to_conv)
  constructor
  · ext
    rw [<-SingleComponent.C'.reduction_equivalent]
  · apply stronger_decreasing_imp_locally_decreasing (SingleComponent.C'.stronger_decreasing _ _)
    exact MainRoad.is_acyclic C hcp.to_conv


namespace MultiComponent

open Relation

variable
  {α I: Type}
  {A: ARS α I}
  [hlo: LinearOrder α] [hwf: WellFoundedLT α]
  (hcp: cofinality_property_conv A)

def cp_dcr₂_ars: ARS α (Fin 2) where
  rel := fun n a b ↦
    ∃(C: Component A) (h: C.p a ∧ C.p b),
      (SingleComponent.C' (MainRoad.seq C hcp) (MainRoad.is_cr C hcp)).rel n ⟨a, h.1⟩ ⟨b, h.2⟩


def reduction_equivalent {a b}: A.union_rel a b ↔ (cp_dcr₂_ars hcp).union_rel a b := by
  let C := A.component a

  constructor
  · intro h
    let a': C.Subtype := ⟨a, A.component_root_mem⟩
    let b': C.Subtype := ⟨b, EqvGen.rel _ _ h⟩

    have := SingleComponent.C'.reduction_equivalent (MainRoad.seq C hcp) (MainRoad.is_cr _ hcp) a' b'
    simp [SubARS.restrict_union] at this
    obtain ⟨i, hi⟩ := this.mp h

    use i, C, ⟨a'.prop, b'.prop⟩
  · rintro ⟨i, C, ⟨ha, hb⟩, hrel⟩
    have hrel': (SingleComponent.C' ..).union_rel .. := Exists.intro i hrel
    rw [<-SingleComponent.C'.reduction_equivalent (MainRoad.seq C hcp) (MainRoad.is_cr _ hcp)] at hrel'
    simp_rw [SubARS.restrict_union] at hrel'
    exact hrel'

def locally_decreasing:
    locally_decreasing (cp_dcr₂_ars hcp) := by
  apply stronger_decreasing_imp_locally_decreasing
  intro x y z i j ⟨hxy, hxz⟩

  -- Without loss of generality i ≤ j, by symmetry of the diverging steps.
  wlog hij: i ≤ j generalizing i j y z
  · have ⟨d, hd⟩ := this z y j i hxz hxy (by omega)
    aesop (add norm max_comm)

  -- A step within a component also exists within the total ARS.
  have hunion_lt {C: Component A} (i) (a b):
      (SingleComponent.C' (MainRoad.seq C hcp) (MainRoad.is_cr _ hcp)).union_lt i a b → (cp_dcr₂_ars hcp).union_lt i a b := by
    rintro ⟨j, hjlt, hjrel⟩
    use j, hjlt, C, ⟨a.prop, b.prop⟩

  -- x i-> y in some component C, and x j-> z in some component C₂
  simp [cp_dcr₂_ars] at hxy hxz
  obtain ⟨C, ⟨hx, hy⟩, hxy⟩ := hxy
  obtain ⟨C₂, ⟨hx₂, hz⟩, hxz⟩ := hxz

  -- because x is in both components, the components must be the same.
  have heq: C = C₂ := component_unique x hx hx₂
  subst heq

  -- then by LD of an individual component (actually SD, but who's counting),
  -- there is a reduct d of y and z, which we can reach using only 0-steps.
  obtain ⟨d, hyd, hzd⟩
    := SingleComponent.C'.stronger_decreasing (MainRoad.seq C hcp) (MainRoad.is_cr C hcp) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ i j ⟨hxy, hxz⟩ (hacyclic := MainRoad.is_acyclic C hcp)

  use d
  simp [hij] at hyd hzd ⊢
  rw [(by simp: y = Subtype.val ⟨y, hy⟩), (by simp: z = Subtype.val ⟨z, hz⟩)]

  -- the reduction sequences from y to d and z to d follow by lifting
  -- `hyd` and `hzd` from the component into the total ARS.
  constructor <;>
  · apply ReflTransGen.lift _ (hunion_lt j) _
    assumption

end MultiComponent

/-- Any ARS with the cofinality property is DCR₂ -/
def cp_dcr₂ (hcp: cofinality_property A): DCRn 2 A := by
  obtain ⟨linearorder, wellorder⟩ := exists_wellOrder α
  use (MultiComponent.cp_dcr₂_ars hcp.to_conv)
  constructor
  · ext
    exact MultiComponent.reduction_equivalent hcp.to_conv
  · exact MultiComponent.locally_decreasing hcp.to_conv


/-- DCR₂ is a complete method for proving confluence of countable ARSs. -/
def dcr₂_complete [Countable α] (A: ARS α I) (hc: confluent A.union_rel): DCRn 2 A :=
  -- A is countable and confluent => A has CP => A is DCR₂ by `cp_dcr₂`.
  cp_of_countable_cr A hc |> cp_dcr₂ A

end Thesis.TwoLabel
