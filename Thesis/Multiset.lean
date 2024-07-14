import Thesis.RelProps

section multiset_ext

open Relation
open Classical

section

variable {a} (r: Rel α α)

/--
We define a multiset extension of a relation `r`, which is generally expected
to be a strict order. The idea behind the extension is that a multiset is
"one-step" smaller than another if it is obtained by replacing an element
in the larger multiset by any amount of smaller (by `r`) elements.

`MultisetExt1` defines the "one-step" relation. The full extension is formed
by taking the transitive closure over `MultisetExt1`.
-/
inductive MultisetExt1 : Multiset α → Multiset α → Prop where
| rel (M M': Multiset α) (s: α) (h: ∀m ∈ M', r m s) : MultisetExt1 (M + M') (s ::ₘ M)

abbrev MultisetExt := (MultisetExt1 r)⁺


/--
`MSESeq r l M N` represents a sequence of smaller-than steps between `M` and `N`,
with all intermediate steps in `l`. This is isomorphic to `MultisetExt`; see
`MSESeq.iff_multiset_ext`.
-/
inductive MSESeq: List (Multiset α) → Multiset α → Multiset α → Prop
| single (h: MultisetExt1 r M N) : MSESeq [M, N] M N
| step (h: MultisetExt1 r M N) (tail: MSESeq l N O): MSESeq (M::l) M O

end

variable {α} {r: Rel α α}
variable [sor: IsStrictOrder α r]

lemma MSESeq.l_nonempty (h: MSESeq r l M N): l.length > 0 := by
  cases h <;>
  simp_all only
    [List.length_cons, List.length_singleton, Nat.reduceAdd, gt_iff_lt, or_true,
     Nat.ofNat_pos, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one]

lemma MSESeq.l_expand (h: MSESeq r l M N): ∃l', l = (M::l') := by
  cases h <;> simp_all only [List.cons.injEq, true_and, exists_eq']

/-- There is a sequence of MSE1 steps iff `MultisetExt r M N` holds.-/
lemma MSESeq.iff_multiset_ext: MultisetExt r M N ↔ ∃l, MSESeq r l M N := by
  constructor <;> intro h
  · induction h using TransGen.head_induction_on with
    | @base M h =>
      use [M, N], MSESeq.single h
    | @ih O P h₁ _ ih =>
      rcases ih with ⟨l, hl⟩
      use (O::l), MSESeq.step h₁ hl
  · rcases h with ⟨l, hl⟩
    induction hl <;> aesop (add unsafe TransGen.single) (add unsafe TransGen.head)

/-- Every index in l represents a step `l[n] <# l[n+1]`. -/
def MSESeq.get_step (hseq: MSESeq r l M N): ∀n, (hlen: n < l.length - 1) → MultisetExt1 r l[n] l[n+1] := by
  intro n hn
  induction hseq generalizing n with
  | single h => simp at hn; simpa [hn]
  | @step M' N' l' O' h tail ih =>
    cases' n with n
    · obtain ⟨l'', hl''⟩ := tail.l_expand
      simpa [hl'']
    · have := ih n (by simp at hn; omega)
      simpa

/-- An element has never increased if for all steps M <# N, the count of x is no higher in M than in N -/
def never_increased_elem (hseq: MSESeq r l M N) (x: α) := ∀n, (hlen: n < l.length - 1) → l[n].count x ≤ l[n+1].count x

/-- An element has decreased in a step if the count in M is one less than the count in N. -/
def decreased_elem1 (M N: Multiset α) (m: α) := M.count m + 1 = N.count m

/-- An element has decreased if there is some step M <# N in which it has decreased. -/
def decreased_elem (hseq: MSESeq r l M N) (x: α) := ∃n, ∃(h: n < l.length - 1), decreased_elem1 l[n] l[n+1] x

/-- If an element has never increased, in particular the count at the end is no larger than at the start. -/
lemma never_increased_elem.overall {r: Rel α α} (hseq: MSESeq r l M N) (x: α) (hni: never_increased_elem hseq x): M.count x ≤ N.count x := by
  induction hseq with
  | single h => exact hni 0 (by simp)
  | step h tail ih =>
    obtain ⟨l', hl'⟩ := tail.l_expand
    simp [hl'] at hni
    have hni₀ := hni 0 (by simp)
    simp only [List.getElem_cons_zero, zero_add, List.getElem_cons_succ] at hni₀
    refine Nat.le_trans hni₀ (ih ?_)
    intro n hlen
    simp only [hl', List.length_cons, add_tsub_cancel_right, List.getElem_cons_succ] at hlen ⊢
    exact hni (n + 1) (by simpa)

/-- If an element has decreased between (M + M') and (M + {s}), it must be s. -/
lemma decreased_elem1.is_s (hde: decreased_elem1 (M + M') (s ::ₘ M) m): m = s := by
  simp [decreased_elem1, Multiset.count_cons] at hde
  by_contra h
  rw [if_neg h] at hde
  linarith

/-- Two elements that have decreased in a single step must be equal, i.e. a one-step decreased element is unique. -/
lemma decreased_elem1.unique (h: MultisetExt1 r M N) (hde: decreased_elem1 M N m): ∀k, decreased_elem1 M N k → k = m := by
  intro k hk
  cases h
  simp [hde.is_s, hk.is_s]

/-- An element is the _largest decreased element_ (LDE) if it has decreased, and no decreased element is larger than it. -/
def is_largest_decreased_elem {r: Rel α α} (hseq: MSESeq r l M N) (m: α) :=
  decreased_elem hseq m ∧ (∀m', decreased_elem hseq m' → ¬(r m m'))

/--
Extending a MSESeq with a step that has a larger decreased elem makes that element the sequence's LDE.
-/
lemma is_largest_decreased_elem.cons_larger
    (hseq: MSESeq r l N O) (hlde: is_largest_decreased_elem hseq k)
    (h: MultisetExt1 r M N) (hde: decreased_elem1 M N k') (hlt: ¬(r k k')):
  is_largest_decreased_elem (MSESeq.step h hseq) k := by
    unfold is_largest_decreased_elem at hlde ⊢
    constructor
    · obtain ⟨n, hlen, hn⟩ := hlde.1
      use (n + 1), (by simp; omega)
      simpa only [List.getElem_cons_succ]
    intro m' hm'
    simp [decreased_elem] at hm'
    obtain ⟨n, ⟨hlen, hde'⟩⟩ := hm'
    cases' n with n
    · cases hseq <;>
      · simp [hlen] at hde'
        rwa [hde.unique h m' hde']
    · apply hlde.2 m'
      use n, (by omega), hde'

/--
Extending a MSESeq with a step that has a smaller decreased elem doesn't change the sequence's LDE.
-/
lemma is_largest_decreased_elem.cons_smaller
    (hseq: MSESeq r l N O) (hlde: is_largest_decreased_elem hseq k)
    (h: MultisetExt1 r M N) (hde: decreased_elem1 M N k') (hlt: r k k'):
  is_largest_decreased_elem (MSESeq.step h hseq) k' := by
    unfold is_largest_decreased_elem at hlde ⊢
    constructor
    · use 0
      obtain ⟨l', hl'⟩ := hseq.l_expand
      simpa [hl']
    unfold decreased_elem
    intro m hm
    simp at hm
    obtain ⟨n, ⟨hlen, hde'⟩⟩ := hm
    cases' n with n
    · cases hseq <;>
      · simp at hde'
        have hmk': m = k' := decreased_elem1.unique h hde m hde'
        rw [hmk']
        apply sor.irrefl
    · exact (hlde.2 m (by use n, (by omega), hde')) ∘ (sor.trans _ _ _ hlt ·)

/-- An element decreases in every step. -/
lemma MultisetExt1.has_dec_elem (h: MultisetExt1 r M N):
    ∃m: α, decreased_elem1 M N m := by
  rcases h with ⟨M, M', s, h⟩
  use s
  simp [decreased_elem1]
  exact sor.irrefl _ ∘ (h _ ·)

/-- If an element increases in a step, a larger element must decrease. -/
lemma MultisetExt1.inc_req_dec (h: MultisetExt1 r M N):
    ∀m, M.count m > N.count m → ∃n, r m n ∧ decreased_elem1 M N n := by
  rcases h with ⟨M, M', s, h⟩
  intro m hm
  simp [Multiset.count_cons] at hm
  have: m ∈ M' := Multiset.count_pos.mp (by omega)
  use s, h _ this
  simp [decreased_elem1]
  exact sor.irrefl _ ∘ (h _ ·)

/--
A sequence always has a largest decreased element.
-/
lemma MSESeq.has_largest_decreased_elem (hseq: MSESeq r l M N):
    ∃m, is_largest_decreased_elem hseq m := by
  induction hseq with
  | single h =>
    unfold is_largest_decreased_elem
    by_contra! hlde
    obtain ⟨m, hm⟩ := h.has_dec_elem
    obtain ⟨m', hm', hrmm'⟩ := hlde m (by use 0; simpa)
    obtain ⟨n, hlen, hn⟩ := hm'
    simp at hlen; simp [hlen] at hn
    rw [decreased_elem1.unique h hm _ hn] at hrmm'
    apply sor.irrefl _ hrmm'
  | @step M N l O h tail ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨s', hs'⟩ := h.has_dec_elem
    by_cases hss'₂: r s s'
    · use s'; exact is_largest_decreased_elem.cons_smaller tail hs h hs' hss'₂
    · use s; exact is_largest_decreased_elem.cons_larger tail hs h hs' hss'₂

/--
The largest decreased element has never increased; if it had, there must be
a larger element which has decreased, yielding a contradiction.
-/
lemma MSESeq.largest_decreased_elem_never_increased (hseq: MSESeq r l M N):
    ∀m, is_largest_decreased_elem hseq m → never_increased_elem hseq m := by
  intro m hlde
  unfold never_increased_elem
  by_contra! hni
  obtain ⟨n, hlen, hn⟩ := hni
  have hstep := hseq.get_step n hlen
  obtain ⟨s'', hs''⟩ := hstep.inc_req_dec m hn
  have hsdec: decreased_elem hseq s'' := by use n, hlen, hs''.2
  apply hlde.2 s'' hsdec hs''.1

/--
The largest decreased element has never increased, and therefore has lower
multiplicity at the end of the sequence than at the beginning.
-/
lemma MSESeq.largest_decreased_elem_has_lower_multiplicity (hseq: MSESeq r l M N):
    ∀m, is_largest_decreased_elem hseq m → M.count m < N.count m := by
  intro m
  intro hlde
  have hni : never_increased_elem hseq m := hseq.largest_decreased_elem_never_increased m hlde
  induction hseq generalizing m with
  | single h =>
    obtain ⟨⟨n, h, hn⟩, -⟩ := hlde
    norm_num at h
    simp [h, decreased_elem1] at hn
    linarith
  | @step M N l O h tail ih =>
    have hni': never_increased_elem tail m := by
      intro n hlen
      have := hni (n + 1) (by simp; omega)
      simpa
    obtain ⟨m', hm'⟩ := h.has_dec_elem
    obtain ⟨l, hl'⟩ := tail.l_expand
    by_cases hmm': (m = m')
    · refine Nat.lt_of_lt_of_le ?_ (hni'.overall _ m)
      rw [<-hmm', decreased_elem1] at hm'
      linarith
    · simp [is_largest_decreased_elem] at hlde
      obtain ⟨hde, hlde⟩ := hlde
      obtain ⟨n, hn, hde⟩ := hde
      cases' n with n
      · simp [hl'] at hde
        exact False.elim <| hmm' <| decreased_elem1.unique h hm' _ hde
      · have: decreased_elem tail m := by
          use n, (by simp at hn; omega)
          simpa
        have hlde': is_largest_decreased_elem tail m := by
          use this
          intro m₂ hm₂
          have: decreased_elem (step h tail) m₂ := by
            obtain ⟨n, hn, hde⟩ := hm₂
            use n + 1, (by simp; omega)
            simpa
          apply hlde _ this
        have := hni 0
        simp [hl'] at this
        exact Nat.lt_of_le_of_lt this (ih _ hlde' hni')

/--
MSESeq is irreflexive; this follows trivially from
`MSESeq.has_largest_decreased_elem` and
`MSESeq.largest_decreased_elem_has_lower_multiplicity`
-/
lemma MSESeq.irrefl: ¬(MSESeq r l M M) := by
  intro h
  obtain ⟨m, hm⟩ := h.has_largest_decreased_elem
  have := h.largest_decreased_elem_has_lower_multiplicity m hm
  linarith

instance MultisetExt.strict_order [i: IsStrictOrder α r]: IsStrictOrder (Multiset α) (MultisetExt r) where
  irrefl := by
    intro M hM
    obtain ⟨l, h⟩ := MSESeq.iff_multiset_ext.mp hM
    apply h.irrefl

lemma MultisetExt1.nonempty (h: MultisetExt1 r M N): N ≠ 0 := by
  cases h
  simp only [ne_eq, Multiset.cons_ne_zero, not_false_eq_true]

/--
`less_add` and `all_accessible` are adapted from the Isabelle theory Multiset.

`all_accessible` especially is a wonderfully short proof of well-foundedness
of `MultisetExt1 r`. The proof has a long history, appearing in the Isabelle
source in 1998 in a commit by Tobias Nipkow, with his proof apparently
deriving from a pen-and-paper proof by Wilfried Buchholz. A version of the proof
as given by Nipkow can be found in `misc/multiset_order_wf.pdf`.

The tree-based proofs found in many parts of the literature are much more
intuitive, but this proof only uses notions that have already been formalized.
-/

lemma less_add (h: MultisetExt1 r N M) (hM: M = a ::ₘ M0):
    (∃M, MultisetExt1 r M M0 ∧ N = a ::ₘ M) ∨
    (∃K, (∀b ∈ K, r b a) ∧ N = M0 + K) := by
  rcases h with ⟨M, M', s, h⟩
  have hM': (M = M0 ∧ s = a) ∨ (∃K, M = a ::ₘ K ∧ M0 = s ::ₘ K) := by
    have := Multiset.cons_eq_cons.mp hM
    tauto
  by_cases has: (a = s)
  · rw [has] at hM ⊢
    right
    use M'
    simp at hM
    simpa [hM, h]
  · left
    rcases hM' with (_ | ⟨K, hK⟩)
    · simp_all
    · use (M' + K)
      constructor
      · rw [hK.2, add_comm]
        apply MultisetExt1.rel
        exact h
      · simp [hK]; ac_rfl

theorem all_accessible (hwf: WellFounded r): ∀M, Acc (MultisetExt1 r) M := by
  intro M
  induction M using Multiset.induction with
  | empty =>
    constructor
    intro y hy
    simpa using hy.nonempty
  | cons a M hM =>
    induction a using hwf.induction generalizing M with
    | h a wf_ih =>
      induction hM with
      | intro M0 h ih₂ =>
        have acc_ih: ∀y, MultisetExt1 r y M0 → Acc (MultisetExt1 r) (a ::ₘ y) := by
          intro y hy; apply ih₂ y hy
        constructor
        intro N hN
        rcases less_add hN (by rfl) with ⟨M, hM₁, rfl⟩ | ⟨K, hK₁, rfl⟩
        · apply acc_ih M hM₁
        · clear acc_ih hN
          induction K using Multiset.induction with
          | empty => simp; exact Acc.intro M0 h
          | cons a' K' ih =>
            rw [add_comm, Multiset.cons_add, add_comm]
            apply wf_ih a' (by simp [hK₁]) (M0 + K') (ih (by simp_all))



instance MultisetExt.wf [IsWellFounded α r]: IsWellFounded (Multiset α) (MultisetExt r) where
  wf := by
    apply WellFounded.transGen
    apply WellFounded.intro
    apply all_accessible
    apply (isWellFounded_iff α r).mp
    exact inferInstance

end multiset_ext
