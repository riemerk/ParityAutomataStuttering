import Mathlib

namespace MuTL
abbrev Atom : Type := Nat

/-- Add the restirction that formula is clean -/
inductive MuTLForm : (bs : Multiset Nat) → Type
| top {bs} : MuTLForm bs
| bot {bs} : MuTLForm bs
| prop {bs} : Atom → MuTLForm bs
| nprop {bs} : (x : Atom) → (x ∉ bs) → MuTLForm bs
| or {bs} : MuTLForm bs →  MuTLForm bs → MuTLForm bs
| and {bs} : MuTLForm bs → MuTLForm bs → MuTLForm bs
| next {bs} : MuTLForm bs → MuTLForm bs
| until {bs} : MuTLForm bs → MuTLForm bs → MuTLForm bs
| mu {bs} : (x : Nat) → MuTLForm (x :: bs) → MuTLForm bs
| nu {bs} : (x : Nat) → MuTLForm (x :: bs) → MuTLForm bs

open MuTLForm

/-! ## SEMANTICS -/
structure Model where
  val: Atom → Set Nat

def Model.assign (𝕊 : Model) (x : Atom) (X : Set Nat) : Model :=
  ⟨fun y => if x == y then X else 𝕊.val y⟩

mutual
def Model.eval {b} (𝕊 : Model) : MuTLForm b → Set Nat
 | .top => Set.univ
 | .bot => ∅
 | .prop p => 𝕊.val p
 | .nprop p _ => Set.univ \ 𝕊.val p
 | .or φ1 φ2 => 𝕊.eval φ1 ∪ 𝕊.eval φ2
 | .and φ1 φ2 => 𝕊.eval φ1 ∩ 𝕊.eval φ2
 | .next φ1 => {n | (n + 1) ∈ 𝕊.eval φ1}
 | .mu x φ => sInf (Function.fixedPoints (𝕊.setval φ x))
 | .nu x φ => sSup (Function.fixedPoints (𝕊.setval φ x))
 | .until φ ψ => {n | ∃ m ∈ 𝕊.eval ψ, m >=n ∧ ∀ t, (n ≤ t ∧ t < m) → t ∈ 𝕊.eval φ}

def Model.setval {b} : Model → MuTLForm b → Atom → Set ℕ → Set ℕ
  | 𝕊, φ, x, X => Model.eval (𝕊.assign x X) φ

  -- Do we need some relation between φ and x here? Must it be bound / free?
end
