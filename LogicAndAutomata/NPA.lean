import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic
import Mathlib

-- set_option diagnostics true

namespace Automata

variable {A : Type}

class NPA A extends NA A where
    FinState : Finite State
    FinAlph : Finite A
    parityMap : State → ℕ
    DecidableA : DecidableEq A

def NPA.ParityAccept (M : NPA A) (as : Stream' A) :=
∃ ss : Stream' M.State, M.InfRun as ss ∧ Even (sSup ((InfOcc ss).image M.parityMap))

def NPA.AcceptedOmegaLang (M : NPA A) : Set (Stream' A) :=
  { as | M.ParityAccept as }

def NA.FinRunStart (M : NA A) (n : ℕ) (as : Stream' A) (ss : Stream' M.State) (start : M.State):=
  ss 0 = start ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

lemma ssupinrange {A : Type} {M : NPA A} {inp : Set M.State} (hnonemp: inp.Nonempty) (hfin: Finite inp) :
    sSup (M.parityMap '' inp) ∈ Set.range M.parityMap := by
  have rangebddabove : BddAbove (M.parityMap '' inp) := by
    apply Set.Finite.bddAbove
    apply Finite.Set.finite_image inp M.parityMap
  have subset : M.parityMap '' inp ⊆ (Set.range M.parityMap) := by grind [← Set.image_univ]
  have nonemp : (M.parityMap '' inp).Nonempty := Set.Nonempty.image NPA.parityMap hnonemp
  apply Set.mem_of_subset_of_mem subset (Nat.sSup_mem nonemp rangebddabove)

lemma inpnonemp {A : Type} {M : NPA A} (ss : Stream' M.State) (start diff : ℕ) (hdiff : diff > 0):
  (ss '' {l | start < l ∧ l ≤ start + diff}).Nonempty := by
  have startplusonein : start + 1 ∈  {l | start < l ∧ l ≤ start + diff} := by
    apply Set.mem_setOf.2
    omega
  exact Set.Nonempty.image ss (Set.nonempty_of_mem startplusonein)

lemma inpfinite {A : Type} {M : NPA A} (ss : Stream' M.State) (start : ℕ) (diff : ℕ):
  Finite ↑(ss '' {l | start < l ∧ l ≤ start + diff}) := by
  apply Set.Finite.image ss
  refine Set.Finite.subset (s:= {l | l ≤ start + diff}) ?_ ?_
  · exact Set.finite_le_nat (start + diff)
  · exact Set.sep_subset_setOf start.succ.le fun x ↦ x ≤ start + (diff)

def NPA.StutterClosed (M: NPA A) : NPA A where
  State := M.State × (A ⊕ Set.range M.parityMap)
  init := {(s, Sum.inr ⟨M.parityMap s, by simp⟩)| s ∈ M.init}
  parityMap := fun (_, s) ↦ (Sum.elim (fun (l: A) ↦ 1) (fun (k: Set.range M.parityMap) ↦ (k+2)) s)
  next
  -- | (s, Sum.inlₗ l), k => {(s', y) | ∃ l, y = Sum.inl l ∧ l=k ∧ s'=s} ∪ {(s, Sum.inr (M.parityMap s))| l=k} (other option)
  | (s, Sum.inlₗ l), k => if @decide  (l=k) (M.DecidableA l k)
                      then {(s, Sum.inl l), (s, Sum.inr ⟨M.parityMap s, by simp⟩)}
                      else ∅
  | (s, Sum.inrₗ p), k => {(s', Sum.inr ⟨ M.parityMap s', by simp ⟩)| s' ∈ M.next s k}
                          ∪ {(s', Sum.inl k) | s' ∈ (M.next s k)}
                          -- ∪ (if p ≠ M.parityMap s then {(x, n)| ∃s', s ∈ (M.next s' k) ∧ x=s ∧ n = Sum.inl k} else ∅)
                          ∪ {(x, p') | ∃ n, ∃ ss : Stream' M.State, ∃n_ge : n ≥ 1, (M.FinRunStart n (fun _ ↦ k) ss s)
                            ∧ p' = Sum.inr ⟨sSup (M.parityMap '' (ss '' {l| (l > 0) ∧ (l ≤ n)})), ssupinrange
                            (by rw [← zero_add n] ; exact (inpnonemp ss 0 n n_ge))
                            (by rw [← zero_add n]; exact inpfinite ss 0 n)⟩
                            ∧ x = ss n}

  FinAlph := FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd
  DecidableA := DecidableA

-- Lemma:
lemma inrange {A : Type} {M : NPA A} (q : M.State) :
  -- let q := ss (∑ m ∈ Finset.range k, (f m + 1));
  NPA.parityMap q ∈ Set.range M.parityMap := by
  simp only [Set.mem_range, exists_apply_eq_apply]
