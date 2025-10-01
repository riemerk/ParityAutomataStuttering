import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic

set_option diagnostics true

namespace Automata
-- open Sequences

variable {A : Type}

class NPA A extends NA A where
    FinState : Finite State
    FinAlph : Finite A
    parityMap : State → ℕ
    DecidableA : DecidableEq A

inductive PosNat where
| one : PosNat
| succ : PosNat → PosNat

def PosNat.toNat : PosNat → Nat
| one => Nat.succ Nat.zero
| succ n => Nat.succ n.toNat

def NPA.ParityAccept (M : NPA A) (as : ℕ → A) :=
∃ ss : ℕ → M.State, M.InfRun as ss ∧ Even (sSup ((InfOcc ss).image M.parityMap))

def NPA.AcceptedOmegaLang (M : NPA A) : Set (ℕ → A) :=
  { as | M.ParityAccept as }

def NA.FinRunStart (M : NA A) (n : ℕ) (as : ℕ → A) (ss : ℕ → M.State) (start : M.State):=
  ss 0 = start ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

-- Add decidability of Equals A

def NPA.StutterClosed (M: NPA A) : NPA A where
  State := M.State × (A ⊕ (M.parityMap '' Set.univ))
  init := {(s, Sum.inr ⟨M.parityMap s, by simp⟩)| s ∈ M.init}
  parityMap := fun (_, s) ↦ (Sum.elim (fun _ ↦ 0) (fun k ↦ k) s)
  next
  -- | (s, Sum.inlₗ l), k => {(s', y) | ∃ l, y = Sum.inl l ∧ l=k ∧ s'=s} ∪ {(s, Sum.inr (M.parityMap s))| l=k} (other option)
  | (s, Sum.inlₗ l), k => if @decide  (l=k) (M.DecidableA l k)
                      then {(s, Sum.inl l), (s, Sum.inr ⟨M.parityMap s, by simp⟩)}
                      else ∅
  | (s, Sum.inrₗ p), k => {(s', Sum.inr ⟨ M.parityMap s, by simp ⟩)| s' ∈ M.next s k}
                          ∪ {(s', Sum.inl k) | s'∈ (M.next s k)}
                          ∪ (if p ≠ M.parityMap s then {(x, n)| ∃s', s ∈ (M.next s' k)∧ x=s∧ n = Sum.inl k} else ∅)
                          ∪ {(x, p') | ∃ n, ∃ ss : ℕ → M.State, (M.FinRunStart n (fun _ ↦ k) ss s) ∧ p' = Sum.inr ⟨sSup (M.parityMap '' {ss k | k ≤ n}), sorry⟩ }

  FinAlph := FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd
  DecidableA := DecidableA

def functiononword (w: ℕ → A) (f : ℕ → (PosNat)) : ℕ → A :=
AppendListInf ((List.range (f 0).toNat).map (λ _ => w 0)) (functiononword (SuffixFrom w 1) (fun k ↦ f (k+1)))

def StutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
∃ wb : ℕ → A,  ∃ f : ℕ → (PosNat),  ∃ f' : ℕ → (PosNat), w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

open Set
theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
    apply Subset.antisymm

    -- rcases
    -- left

-- #example : (NPA.StutterClosed).AcceptedOmegaLang = StutterClosure (NPA.AcceptedOmegaLang)
-- #eval functiononword
