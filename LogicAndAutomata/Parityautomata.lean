import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc

namespace Automata

variable {A : Type}

class NPA A extends NA A where
    FinState: Finite State
    parityMap : State → ℕ

inductive PosNat where
| one : PosNat
| succ (n : PosNat) : PosNat

def PosNat.toNat : PosNat → Nat
| one => Nat.succ Nat.zero
| succ n => Nat.succ n.toNat

def NPA.ParityAccept (M : NPA A) (as : ℕ → A) :=
∃ ss : ℕ → M.State, M.InfRun as ss ∧ Even (sSup ((InfOcc ss).image M.parityMap))

def NPA.AcceptedOmegaLang (M : NPA A)  : Set (ℕ → A) :=
  { as | M.ParityAccept as }


def NPA.StutterClosure (M: NPA A) : NPA A :=
sorry

def functiononword (w: ℕ → A) (f : ℕ → (PosNat)) : ℕ → A:=
sorry
-- w.foldR (fun )

def StutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
∃ wb : ℕ → A,  ∃ f : ℕ → (PosNat),  ∃ f' : ℕ → (PosNat), w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosure).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) :=
    sorry
