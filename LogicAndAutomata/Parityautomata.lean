import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc

namespace Automata

variable {A : Type}

class NPA A extends NA A where
    FinState: Finite State
    parityMap : State → ℕ



def NPA.ParityAccept (M : NPA A) (as : ℕ → A) :=
∃ ss : ℕ → M.State, M.InfRun as ss ∧ Even (sSup ((InfOcc ss).image M.parityMap))

def NPA.AcceptedOmegaLang (M : NPA A)  : Set (ℕ → A) :=
  { as | M.ParityAccept as }


def NPA.StutterClosure (M: NPA A) : NPA A :=
sorry

def SutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
sorry

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
sorry

theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosure).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) :=
    sorry
