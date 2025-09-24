namespace LTL

inductive Formula : Type
| prop : Nat → Formula
| nprop : Nat → Formula
| or : Formula → Formula -> Formula
| and : Formula → Formula → Formula
| box : Formula → Formula
| circ: Formula → Formula
| until: Formula → Formula → Formula

-- Nog toevoegen diamond?

structure Model where
  S: Type
  V: Nat → S → Prop
  σ: Nat -> S

open Formula

def truth (𝔐: Model) (j : Nat) : Formula  → Prop
| .prop n => 𝔐.V n (𝔐.σ j)
| .nprop n => Not  (𝔐.V n (𝔐.σ j))
| .or φ ψ => truth 𝔐 j φ ∨ truth 𝔐 j ψ
| .and φ ψ => truth 𝔐 j φ ∧ truth 𝔐 j ψ
| .box φ => ∀ k, k ≥ j → truth 𝔐 k φ
| .circ φ => truth 𝔐 (j + 1) φ
| .until φ ψ => ∃ k, k ≥ j ∧ truth 𝔐 k ψ ∧ (∀ i, (j≤ i ∧ i < k)→ truth 𝔐 i φ)
