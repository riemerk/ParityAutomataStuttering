import AutomataTheory.Automata.Basic
import AutomataTheory.Sequences.InfOcc

namespace Automata
variable {Alph : Type}

class NPA Alph extends NA Alph where
    parityMap : State → ℕ
    FinState : Finite State
    FinAlph : Finite Alph
    DecidableAlph : DecidableEq Alph

def NPA.ParityAccept (A : NPA Alph) (w : Stream' Alph) :=
∃ ρ : Stream' A.State, A.InfRun w ρ ∧ Even (sSup ((InfOcc ρ).image A.parityMap))

def NPA.AcceptedOmegaLang (A : NPA Alph) : Set (Stream' Alph) :=
  { w | A.ParityAccept w }

def NA.FinRunStart (A : NA Alph) (n : ℕ) (w : Stream' Alph) (ρ : Stream' A.State)
    (start : A.State) :=
  ρ 0 = start ∧ ∀ k < n, ρ (k + 1) ∈ A.next (ρ k) (w k)

lemma ssupinrange {Alph : Type} {A : NPA Alph} {inp : Set A.State} (hnonemp : inp.Nonempty)
      (hfin : Finite inp) : sSup (A.parityMap '' inp) ∈ Set.range A.parityMap := by
  have rangebddabove : BddAbove (A.parityMap '' inp) := by
    apply Set.Finite.bddAbove
    apply Finite.Set.finite_image inp A.parityMap
  have subset : A.parityMap '' inp ⊆ (Set.range A.parityMap) := by grind [← Set.image_univ]
  have nonemp : (A.parityMap '' inp).Nonempty := Set.Nonempty.image NPA.parityMap hnonemp
  apply Set.mem_of_subset_of_mem subset (Nat.sSup_mem nonemp rangebddabove)

lemma inpnonemp {Alph : Type} {A : NPA Alph} (ρ : Stream' A.State) (start diff : ℕ)
      (hdiff : diff > 0) : (ρ '' {l | start < l ∧ l ≤ start + diff}).Nonempty := by
  have startplusonein : start + 1 ∈  {l | start < l ∧ l ≤ start + diff} := by
    apply Set.mem_setOf.2
    omega
  exact Set.Nonempty.image ρ (Set.nonempty_of_mem startplusonein)

lemma inpfinite {Alph : Type} {A : NPA Alph} (ρ : Stream' A.State) (start : ℕ) (diff : ℕ) :
  Finite ↑(ρ '' {l | start < l ∧ l ≤ start + diff}) := by
  apply Set.Finite.image ρ
  refine Set.Finite.subset (s:= {l | l ≤ start + diff}) ?_ ?_
  · exact Set.finite_le_nat (start + diff)
  · exact Set.sep_subset_setOf start.succ.le fun x ↦ x ≤ start + (diff)

def NPA.StutterClosed (A : NPA Alph) : NPA Alph where
  State := A.State × (Alph ⊕ Set.range A.parityMap)
  init := {(a, Sum.inr ⟨A.parityMap a, by simp⟩)| a ∈ A.init}
  parityMap := fun (_, a) ↦ (Sum.elim (fun (l: Alph) ↦ 1)
      (fun (k: Set.range A.parityMap) ↦ (k + 2)) a)
  next
  | (a, Sum.inlₗ l), k => if @decide  (l=k) (A.DecidableAlph l k)
                      then {(a, Sum.inl l), (a, Sum.inr ⟨A.parityMap a, by simp⟩)}
                      else ∅
  | (a, Sum.inrₗ m), k => {(a', Sum.inl k) | a' ∈ (A.next a k)}
                          ∪ {(a', m') | ∃ n, ∃ ρ : Stream' A.State, ∃n_ge : n ≥ 1,
                            (A.FinRunStart n (fun _ ↦ k) ρ a)
                            ∧ m' = Sum.inr ⟨sSup (A.parityMap '' (ρ '' {l| (l > 0) ∧ (l ≤ n)})),
                            ssupinrange (by rw [← zero_add n] ; exact (inpnonemp ρ 0 n n_ge))
                            (by rw [← zero_add n]; exact inpfinite ρ 0 n)⟩
                            ∧ a' = ρ n}
  FinAlph := FinAlph
  FinState := by
    have hState : Finite A.State := FinState
    have hAlph: Finite Alph := FinAlph
    exact Finite.instProd
  DecidableAlph := DecidableAlph

lemma inrange {Alph : Type} {A : NPA Alph} (a : A.State) :
  NPA.parityMap a ∈ Set.range A.parityMap := by
  simp only [Set.mem_range, exists_apply_eq_apply]

end Automata
