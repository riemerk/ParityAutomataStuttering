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

def NPA.StutterClosure (M: NPA A) : NPA A where
  -- State := M.State × (A ⊕ Fin (sSup (Set.image M.parityMap Set.univ)))
  State := M.State × (A ⊕ Fin (sSup (M.parityMap '' Set.univ) + 1))
  -- State := M.State × (A ⊕ ℕ)
  -- State := M.State × A
  init := {(s, Sum.inr (Fin.ofNat (sSup (M.parityMap '' Set.univ) + 1) (M.parityMap s))) | s ∈ M.init}
  parityMap := fun (_, s) ↦ (Sum.elim (fun _ ↦ 0) (fun k ↦ k) s)
  -- next := fun s l ↦ (Sum.elim ({(s.fst, Sum.inl l), (s.fst, Sum.inr (Fin.ofNat (sSup (M.parityMap '' Set.univ) + 1) (M.parityMap s.fst)))})
  -- next := fun s l ↦ (Sum.elim (fun k ↦ l => {(s.fst, Sum.inl l), (s.fst, Sum.inr (M.parityMap s.fst))})
  --                   ({(x,Sum.inr (M.parityMap x)) | x∈ M.next s.fst l}) s.snd)
  next
  | (s, Sum.inlₗ l), k => if l = k
                      then {(s, Sum.inl l), (s, Sum.inr (Fin.ofNat (sSup (M.parityMap '' Set.univ) + 1) (M.parityMap s)))}
                      else ∅
  | (s, Sum.inrₗ p), k => {(s', Sum.inr (Fin.ofNat (sSup (M.parityMap '' Set.univ) + 1) (M.parityMap s))) | s' ∈ M.next s k}
                          ∪ {(s', Sum.inl k) | s'∈ (M.next s k)}
                          ∪ (if p ≠ M.parityMap s then {(s, Sum.inl k) : M.State × (A ⊕ Fin (sSup (M.parityMap '' Set.univ) + 1)) | ∃s', s ∈ (M.next s' k)} else ∅)
                          ∪ {(x, Sum.inr p') | ∃ n, ∃ ss : ℕ → M.State, (M.FinRunStart n (fun _ ↦ k) ss s) ∧ p' = (Fin.ofNat (sSup (M.parityMap '' Set.univ) + 1) sSup (M.parityMap '' {ss k | k ≤ n}))}

  FinAlph := by exact FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd

-- def

def functiononword (w: ℕ → A) (f : ℕ → (PosNat)) : ℕ → A :=
AppendListInf ((List.range (f 0).toNat).map (λ _ => w 0)) (SuffixFrom w 1)

def StutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
∃ wb : ℕ → A,  ∃ f : ℕ → (PosNat),  ∃ f' : ℕ → (PosNat), w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosure).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) :=
    sorry
