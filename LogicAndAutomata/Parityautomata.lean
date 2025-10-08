import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic

set_option diagnostics false

namespace Automata
-- open Sequences

variable {A : Type}

class NPA A extends NA A where
    FinState : Finite State
    FinAlph : Finite A
    parityMap : State → ℕ
    DecidableA : DecidableEq A

def NPA.ParityAccept (M : NPA A) (as : ℕ → A) :=
∃ ss : ℕ → M.State, M.InfRun as ss ∧ Even (sSup ((InfOcc ss).image M.parityMap))

def NPA.AcceptedOmegaLang (M : NPA A) : Set (ℕ → A) :=
  { as | M.ParityAccept as }

def NA.FinRunStart (M : NA A) (n : ℕ) (as : ℕ → A) (ss : ℕ → M.State) (start : M.State):=
  ss 0 = start ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

lemma ssupinrange {A : Type} (M : NPA A) (n : ℕ) (ss : ℕ → NA.State A) :
    sSup (M.parityMap '' {x | ∃ k ≤ n, ss k = x}) ∈ Set.range M.parityMap := by
  have image : {ss k | k ≤ n} = ss '' {k | k ≤ n} := rfl
  have inpfin : Finite  {ss k | k ≤ n} := by rw [image]; exact Set.Finite.image ss (Set.finite_le_nat n)
  have rangebddabove : BddAbove (M.parityMap '' {ss k | k ≤ n}) := by
    apply Set.Finite.bddAbove
    apply Finite.Set.finite_image {x | ∃ k ≤ n, ss k = x} M.parityMap
  have domsubset : {ss k | k ≤ n} ⊆ Set.univ := by exact fun ⦃a⦄ a ↦ trivial
  have subset : M.parityMap '' {ss k | k ≤ n} ⊆ (Set.range M.parityMap) := by
    rw [← Set.image_univ]
    exact Set.image_mono domsubset
  have nbig : n ≥ 0 := by omega
  have onein : ss 0 ∈ {ss k | k ≤ n} := by
    apply Set.mem_setOf.2
    exists 0
  have memim : M.parityMap (ss 0) ∈ (M.parityMap '' {ss k | k ≤ n}):= Set.mem_image_of_mem M.parityMap onein
  have nonemp : (M.parityMap '' {ss k | k ≤ n}).Nonempty := by
    exact Set.nonempty_of_mem memim
  apply Set.mem_of_subset_of_mem subset
  exact Nat.sSup_mem nonemp rangebddabove

-- Add decidability of Equals A
def NPA.StutterClosed (M: NPA A) : NPA A where
  State := M.State × (A ⊕ Set.range M.parityMap)
  -- State := M.State × (A ⊕ (M.parvityMap '' Set.univ))
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
                          ∪ {(x, p') | ∃ n, ∃ ss : ℕ → M.State, n ≥ 1 ∧ (M.FinRunStart n (fun _ ↦ k) ss s) ∧ p' = Sum.inr ⟨sSup (M.parityMap '' {ss k | k ≤ n}), ssupinrange _ _ _⟩}

  FinAlph := FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd
  DecidableA := DecidableA

-- Is this implementation efficient?
-- And is this proof efficient??
def functiononword (w: ℕ → A) (f : ℕ → ℕ+) (n : ℕ) : A :=
if _h : n < (f 0) then
  w 0
else
  functiononword (SuffixFrom w 1) (SuffixFrom f 1) (n - (f 0))
termination_by n
decreasing_by
let m : ℕ+ := (f 0)
have nbiggerm: n ≥ m := by grind
  -- simp only [not_lt] at _h
  -- simp only [ge_iff_le]
  -- exact _h
apply Nat.sub_lt
· exact Nat.lt_of_lt_of_le (PNat.one_le m) nbiggerm
· exact (PNat.one_le m)

def StutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
∃ wb : ℕ → A,  ∃ f : ℕ → (ℕ+),  ∃ f' : ℕ → (ℕ+), w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
    generalize (M.StutterClosed) = Ms
    apply Set.Subset.antisymm
    rw [Set.subset_def]
    intro x
    intro h
    rw [NPA.AcceptedOmegaLang]
    rw [NPA.AcceptedOmegaLang] at h
    apply Set.mem_setOf.1 at h
    rw [NPA.ParityAccept] at h
    rw [StutterClosure]
    apply Set.mem_setOf.2
    apply Exists.elim at h
    sorry
    sorry
    rw [Set.subset_def]
    intro x
    intro h
    rw [StutterClosure] at h
    apply Membership.mem.out at h
    rw [NPA.AcceptedOmegaLang]
    obtain ⟨w', hw'⟩ := h
    obtain ⟨hw'inlang, hw'stutequiv⟩ := hw'
    rw [StutterEquivalent] at hw'stutequiv
    obtain ⟨wb, f, f', hwb⟩ := hw'stutequiv
    have wbaccepted : wb ∈ Ms.AcceptedOmegaLang
    rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢

    obtain ⟨ss, hssacc⟩ := hw'inlang
    let ss' : ℕ → Ms.State :=
    -- let ss' : ℕ → ℕ :=
    fun k ↦
    if k = 0 then
    (ss 0, Sum.inr (M.parityMap (ss 0))) -- Wat gebeurt hier? Dit is state A maar ik wil dat het Ms.State is
    else if f k = 1 then
    sorry
    else
    sorry

    -- have newrun : Ms.InfRun wb ss'
    -- apply Exists.elim ss'




    -- rw [Set.mem_setOf]
    -- rw [NPA.ParityAccept]


    sorry
