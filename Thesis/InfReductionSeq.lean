import Mathlib.Tactic
import Mathlib.Logic.Relation
import Thesis.ReductionSeq

namespace Thesis.InfReductionSeq

section inf_reduction_seq

open Relation Classical

variable {α}

section irs_def

variable (r: Rel α α)

def is_inf_reduction_seq (f: ℕ → α) :=
  ∀n, r (f n) (f (n + 1))

end irs_def

variable {r: Rel α α}

lemma trans_chain: r⁺ a b → ∃l, l.getLast? = some b ∧ List.Chain r a l := by
  intro hr
  induction hr using TransGen.head_induction_on with
  | @base a h =>
    use [b]; simp; exact h
  | @ih a c h₁ h₂ ih =>
    obtain ⟨l, hl, hchain⟩ := ih
    use c::l
    simp [hl, h₁, hchain]
    show (c :: l).getLast? = some b
    exact Option.mem_def.mp (List.mem_getLast?_cons hl) -- suggested by apply?


noncomputable def trans_chain': r⁺ a b → List α :=
  fun h ↦ choose (trans_chain h)

lemma trans_chain'.spec {r: Rel α α} {a b: α} (h: r⁺ a b):
    (trans_chain' h).getLast? = b ∧ List.Chain r a (trans_chain' h) := by
  simp [choose_spec (trans_chain h), trans_chain']

lemma trans_chain'.nonempty: 1 ≤ (trans_chain' h).length := by
  by_contra! h'
  rw [Nat.lt_one_iff, List.length_eq_zero] at h'
  apply ((trans_chain' h).getLast?_isSome).mp
  rwa [(spec h).1, Option.isSome_some]


lemma trans_chain'.nonempty': trans_chain' h ≠ [] := by
  refine List.length_pos.mp ?_
  simp [<-Nat.one_add_le_iff]
  apply nonempty

noncomputable def inf_trans_lists (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f): ℕ → List α
| n => trans_chain' (hf n)

lemma inf_trans_lists.nonempty: ∀n, 1 ≤ (inf_trans_lists f hf n).length
| n => by simp [inf_trans_lists, trans_chain'.nonempty]

lemma inf_trans_lists.nonempty': ∀n, (inf_trans_lists f hf n) ≠ []
| n => by
  refine List.length_pos.mp ?_
  simp [<-Nat.one_add_le_iff]
  apply nonempty

section aux

variable (l_seq: ℕ → List α) (hne: ∀n, 1 ≤ (l_seq n).length)

def aux (start: ℕ) (add: ℕ) : α :=
  if h: add < (l_seq start).length then
    (l_seq start).get ⟨add,h⟩
  else
    have : add - (l_seq start).length < add := by
      exact Nat.sub_lt_self (hne start) (Nat.le_of_not_lt h)
    aux (start + 1) (add - (l_seq start).length)


lemma aux_skip (m k: ℕ): ∃n, aux l_seq hne m (k + n) = aux l_seq hne (m + 1) k := by
  use (l_seq m).length
  conv => left; unfold aux; simp

lemma aux_skip_i (i m k: ℕ): ∃n, aux l_seq hne m (k + n) = aux l_seq hne (m + i) k := by
  induction i generalizing m with
  | zero => use 0; simp
  | succ i ih =>
    obtain ⟨n, hn⟩ := ih (m + 1)
    obtain ⟨n', hn'⟩ := aux_skip l_seq hne m (k + n)
    ring_nf at hn hn' ⊢

    rw [<-hn]
    rw [<-hn']
    use (n + n')
    simp [add_assoc]


lemma aux_elem (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    let ls := inf_trans_lists f hf; ∀n > 0, f n = aux ls inf_trans_lists.nonempty (n - 1) ((ls (n - 1)).length - 1) := by
  simp
  intro n hn
  have hn': n ≠ 0 := by linarith
  unfold aux
  split
  next h =>
    · simp [inf_trans_lists]
      let c := trans_chain' (hf (n - 1))
      have ⟨h₁, h₂⟩ := trans_chain'.spec (hf (n - 1))
      have heq₁ := List.getLast_eq_get (trans_chain' (hf (n - 1))) trans_chain'.nonempty'
      dsimp at heq₁
      rw [<-heq₁]
      have heq₂ := List.getLast?_eq_getLast (trans_chain' (hf (n - 1))) trans_chain'.nonempty'
      rw [heq₂] at h₁
      simp [Option.some_inj] at h₁
      conv => left; rw [<-Nat.sub_one_add_one hn']
      symm; exact h₁
  next h =>
    · simp at h
      exfalso
      have h': 1 ≤ (inf_trans_lists f hf _).length := inf_trans_lists.nonempty (n - 1)
      simp_all only [List.length_nil, nonpos_iff_eq_zero]

lemma aux_elem' (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    let ls := inf_trans_lists f hf; ∀n > 0, ∃n', f n = aux ls inf_trans_lists.nonempty 0 n' := by
  simp
  intro n hn
  have := aux_elem f hf n hn
  obtain ⟨n, hn⟩ := aux_skip_i (inf_trans_lists f hf) inf_trans_lists.nonempty (n - 1) 0 ((inf_trans_lists f hf (n - 1)).length - 1)
  simp only [zero_add] at hn
  rw [<-hn] at this
  tauto

noncomputable def seq (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f): ℕ → α
| 0 => f 0
| n + 1 => aux (inf_trans_lists f hf) inf_trans_lists.nonempty 0 n


lemma seq_contains_elems (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    ∀n, ∃m, f n = seq f hf m := by
  intro n
  cases n with
  | zero => use 0; simp [seq]
  | succ n =>
    simp [seq]
    obtain ⟨n', hn'⟩ := aux_elem' f hf (n + 1) (by omega)
    use n' + 1

lemma l_idx_isLast (l: List α) (hne: 0 < l.length) (hl: l[l.length - 1] = x): l.getLast (List.length_pos.mp hne) = x := by
  rw [<-hl]
  rw [List.getLast_eq_get]
  simp


lemma aux_is_inf_reduction_seq
    -- the first list by itself forms a chain
    (h0 : List.Chain' r (l_seq 0))
    -- and each subsequent list continues where the last one left off.
    (h1 : ∀ n, List.Chain r ((l_seq n).getLast (List.length_pos.mp (hne n))) (l_seq (n + 1))):
    ∀ start, is_inf_reduction_seq r (aux l_seq hne start) := by
  intro start
  dsimp [is_inf_reduction_seq]
  intro add
  induction start, add using aux.induct l_seq hne
  next start add hlt =>
    unfold aux
    simp [dif_pos hlt]
    split
    case isTrue h =>
      rcases start with (_ | start)
      · rw [List.chain'_iff_get] at h0
        apply h0
        omega
      · specialize h1 start
        rw [List.chain_iff_get] at h1
        apply h1.2
        omega
    case isFalse h =>
      rw [aux]
      have : add = (l_seq start).length - 1 := by omega
      subst this
      simp_all
      have := Nat.succ_le.mp <| hne (start + 1)
      simp [dif_pos this]
      have heq: (l_seq start).getLast (List.length_pos.mp (hne start)) = (l_seq start)[(l_seq start).length - 1] :=
        l_idx_isLast (l_seq start) (Nat.succ_le.mp <| hne start) rfl
      specialize h1 start
      rw [heq, List.chain_iff_get] at h1
      rcases h1 with ⟨h1₁, -⟩
      specialize h1₁ this
      simpa using h1₁
  next start add h1 _ ih =>
    rw [aux, dif_neg h1]
    nth_rw 2 [aux]
    have not_add_succ_lt: ¬ add + 1 < (l_seq start).length :=
      fun h => h1 ((lt_add_one add).trans h)
    rw [dif_neg not_add_succ_lt]
    have nat_fact: add - (l_seq start).length + 1 = add + 1 - (l_seq start).length := by omega
    rw [nat_fact] at ih
    exact ih

lemma hchain0 (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f): List.Chain' r (inf_trans_lists f hf 0) := by
  obtain ⟨hlast, hchain⟩ := trans_chain'.spec (hf 0)
  rw [inf_trans_lists, List.Chain']
  split
  next x heq => simp
  next x head as heq =>
    simp at heq
    rw [heq] at hchain
    exact List.chain_of_chain_cons hchain

lemma hchain1 (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    ∀n, List.Chain r ((inf_trans_lists f hf n).getLast (inf_trans_lists.nonempty' n)) (inf_trans_lists f hf (n + 1)) := by
  intro n
  unfold inf_trans_lists
  simp
  obtain ⟨hlast₁, -⟩ := trans_chain'.spec (hf n)
  obtain ⟨-, hchain₂⟩:= trans_chain'.spec (hf (n + 1))
  convert hchain₂
  rw [<-Option.some_inj, <-hlast₁]
  symm
  apply List.getLast?_eq_getLast

lemma seq_is_inf_reduction_seq (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    is_inf_reduction_seq r (seq f hf) := by
  intro n
  cases n with
  | zero =>
    simp [seq]
    unfold aux
    have h: 0 < (inf_trans_lists f hf 0).length := by
      exact Nat.succ_le.mp <| inf_trans_lists.nonempty 0
    rw [dif_pos h]
    unfold inf_trans_lists
    obtain ⟨-, hchain⟩ := trans_chain'.spec (hf 0)
    rw [List.chain_iff_get] at hchain
    exact hchain.1 h
  | succ n =>
    have := aux_is_inf_reduction_seq (inf_trans_lists f hf) inf_trans_lists.nonempty (hchain0 f hf) (hchain1 f hf) 0
    have := this n
    unfold seq; simp
    assumption

lemma exists_regular_seq (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f):
    ∃f', is_inf_reduction_seq r f' ∧
         (∀n, ∃m, f n = f' m) ∧
         f 0 = f' 0 := by
  use (seq f hf)
  and_intros
  · exact seq_is_inf_reduction_seq f hf
  · exact fun n ↦ seq_contains_elems f hf n
  · unfold seq; simp

end aux

/-- A transitive step can be decomposed into a step and, potentially, a remaining transitive step. -/
lemma internal_step: r⁺ a b → ∃c, r a c ∧ (c = b ∨ r⁺ c b) := by
  intro hr
  induction hr using TransGen.head_induction_on with
  | base h => use b, h; left; rfl
  | ih h₁ h₂ _ih =>
    rename_i a c
    use c, h₁; right; exact h₂

/-- Given an infinite sequence of transitive steps, there is always a next small step. -/
lemma step (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f) (a: α): (∃n, r⁺ a (f n)) → (∃(p: ℕ × α), r a p.2 ∧ r⁺ p.2 (f p.1)) := by
  rintro ⟨n, hr⟩
  obtain ⟨c, hc⟩ := internal_step hr
  cases hc.right with
  | inl h =>
    use (n + 1, c), hc.left
    simp [h, hf n]
  | inr h =>
    use (n, c)
    tauto

/--
A transitive infinite reduction sequence can be turned into
a regular infinite reduction sequence.
-/
lemma of_trans (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f): ∃f', is_inf_reduction_seq r f' := by
  have hstep := step f hf

  let f': α → α :=
    fun x ↦ if h: ∃n, r⁺ x (f n) then (choose (hstep x h)).2 else x

  have h₁ : ∀a, (∃n, r⁺ a (f n)) → (∃n, r⁺ (f' a) (f n)) := by
    rintro a h
    have := choose_spec (hstep a h)
    simp [f', dif_pos h]
    obtain ⟨-, right⟩ := this
    exact Exists.intro (choose (hstep a h)).1 right

  have h₂ : ∀a, (∃n, r⁺ a (f n)) → r a (f' a) := by
    intro a h
    have := choose_spec (hstep a h)
    simp [f', dif_pos h]
    tauto

  have: ∀N, ∃n, r⁺ (f'^[N] (f 0)) (f n) := Function.Iterate.rec _ h₁ ⟨1, hf 0⟩

  use (f'^[·] (f 0))
  simp only [is_inf_reduction_seq]
  intro n
  rw [Function.iterate_succ', Function.comp]
  exact h₂ (f'^[n] (f 0)) (this n)


-- The above is still not as strong as ReductionSeq.flatten, and only
-- flattens a transitive reduction sequence.

-- Building an `of_refl_trans` is even more complicated, and if the
-- reflexive-transitive seq has a point beyond which all steps are reflexive,
-- the 'flattened' version would be finite, so there really need to be two
-- separate defs which produce either version depending on the sequence.
-- lemma of_refl_trans (f: ℕ → α) (hf: is_inf_reduction_seq r∗ f): ???

end inf_reduction_seq

end Thesis.InfReductionSeq
