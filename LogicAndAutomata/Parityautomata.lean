import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic
-- import Mathlib.Probability.Distributions.Fernique
import Mathlib

-- set_option diagnostics true

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

-- lemma ssupinrange {A : Type} (M : NPA A) (n : ℕ) (ss : ℕ → NA.State A) :
--     sSup (M.parityMap '' {x | ∃ k ≤ n, ss k = x}) ∈ Set.range M.parityMap := by
--   have inpfin : Finite  {ss k | k ≤ n} := Set.Finite.image ss (Set.finite_le_nat n)
--   have rangebddabove : BddAbove (M.parityMap '' {ss k | k ≤ n}) := by
--     apply Set.Finite.bddAbove
--     apply Finite.Set.finite_image {x | ∃ k ≤ n, ss k = x} M.parityMap
--   -- have domsubset : {ss k | k ≤ n} ⊆ Set.univ := by exact fun ⦃a⦄ a ↦ trivial
--   have subset : M.parityMap '' {ss k | k ≤ n} ⊆ (Set.range M.parityMap) := by grind [← Set.image_univ]
--     -- rw [← Set.image_univ]
--     -- exact Set.image_mono domsubset
--   have nbig : n ≥ 0 := by omega
--   have onein : ss 0 ∈ {ss k | k ≤ n} := by
--     apply Set.mem_setOf.2
--     exists 0
--   have memim : M.parityMap (ss 0) ∈ (M.parityMap '' {ss k | k ≤ n}):= Set.mem_image_of_mem M.parityMap onein
--   have nonemp : (M.parityMap '' {ss k | k ≤ n}).Nonempty := Set.nonempty_of_mem memim
--   apply Set.mem_of_subset_of_mem subset (Nat.sSup_mem nonemp rangebddabove)

theorem ssupinrange {A : Type} (M : NPA A) (inp : Set M.State) (hnonemp: inp.Nonempty) (hfin: Finite inp) :
    sSup (M.parityMap '' inp) ∈ Set.range M.parityMap := by
  have rangebddabove : BddAbove (M.parityMap '' inp) := by
    apply Set.Finite.bddAbove
    apply Finite.Set.finite_image inp M.parityMap
  have subset : M.parityMap '' inp ⊆ (Set.range M.parityMap) := by grind [← Set.image_univ]
  have nonemp : (M.parityMap '' inp).Nonempty := Set.Nonempty.image NPA.parityMap hnonemp
  apply Set.mem_of_subset_of_mem subset (Nat.sSup_mem nonemp rangebddabove)

lemma inpnonemp1 {A : Type} (M : NPA A) (n : ℕ) (ss : ℕ → M.State) :
          {ss k | k ≤ n}.Nonempty := by
          have nbig : n ≥ 0 := by omega
          have zeroin : ss 0 ∈ {ss k | k ≤ n} := by
            apply Set.mem_setOf.2
            exists 0
          exact Set.nonempty_of_mem zeroin

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
  | (s, Sum.inrₗ p), k => {(s', Sum.inr ⟨ M.parityMap s', by simp ⟩)| s' ∈ M.next s k}
                          ∪ {(s', Sum.inl k) | s'∈ (M.next s k)}
                          -- ∪ (if p ≠ M.parityMap s then {(x, n)| ∃s', s ∈ (M.next s' k) ∧ x=s ∧ n = Sum.inl k} else ∅)
                          ∪ {(x, p') | ∃ n, ∃ ss : ℕ → M.State, n ≥ 1 ∧ (M.FinRunStart n (fun _ ↦ k) ss s)
                            ∧ p' = Sum.inr ⟨sSup (M.parityMap '' {ss k | k ≤ n}), ssupinrange _ _ (inpnonemp1 _ _ _) (Set.Finite.image ss (Set.finite_le_nat n))⟩}

  FinAlph := FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd
  DecidableA := DecidableA

-- Is this implementation efficient?
-- And is this proof efficient?? (leesbaarheid verbeteren en probeer met omega en linarith)
-- En gebruik simp alleen maar simp only als tussenstap
-- Indentatie, := by maar kan ook · voor andere goals
theorem kexists (n:ℕ) (f: ℕ → ℕ) : ∃k, (((∑ m∈Finset.range k, (f m + 1))≤ n) ∧ (n < (∑ m∈ Finset.range (k + 1), (f m + 1)))) := by
  let g : ℕ → ℕ :=  fun k ↦ (∑ m∈Finset.range k, (f m + 1))
  have fstrictmono : StrictMono fun k ↦ (∑ m∈Finset.range k, (f m + 1)) := by
    refine strictMono_nat_of_lt_succ ?_
    expose_names
    -- let g :ℕ → ℕ := fun x ↦ f_1 x + 1
    intro m
    rw [Finset.sum_range_succ]
    simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

  -- have rangegunbounded : ¬ BddAbove (Set.range fun k ↦ (∑ m∈Finset.range k, (f m + 1))) :=
  --   StrictMono.not_bddAbove_range_of_wellFoundedLT fstrictmono
  -- apply StrictMono.exists_between_of_tendsto_atTop
  sorry
  -- refine StrictMono.exists_between_of_tendsto_atTop


  -- sorry


def functiononword (w: ℕ → A) (f : ℕ → ℕ) (n : ℕ) : A :=
-- let d : ℕ := 0
-- have exists : ∃ d, (∑ M∈ Finset.range d, (f' m + 1))≤ n ∧ n < (∑ M∈ Finset.range (d + 1), (f' m + 1)) := by sorry
-- ((∑ m ∈ Finset.range k, (f' m + 1)))

-- let d : ℕ := Nat.findGreatest (correct n f)
-- w d

-- while d: (d < sorry ∧ d ≥ sorry) do
--   let d := d + 1
if n < (f 0 + 1) then
  w 0
else
  functiononword (SuffixFrom w 1) (SuffixFrom f 1) (n - (f 0 + 1))
termination_by n
decreasing_by
-- let m : Nat := (f 0 + 1)
omega

-- def posnat :
#eval functiononword (fun n↦ if (Even n) then 'a' else 'b') (fun _ ↦ 1) 6

-- def test
-- #eval (f )
def StutterEquivalent (w: ℕ → A) (w' : ℕ → A) : Prop :=
∃ wb : ℕ → A,  ∃ f : ℕ → Nat,  ∃ f' : ℕ → Nat, w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (ℕ → A)) : Set (ℕ → A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

lemma inpfinite1 {A : Type} (M : NPA A) (ss : ℕ → M.State) (start : ℕ) (f' : ℕ → ℕ) (k : ℕ) :
  Finite ↑(ss '' {l | start < l ∧ l ≤ start + f' (k - 1) + 1}) := by
  apply Set.Finite.image ss
  have supsetfin:  {l | l ≤ start + f' (k - 1) + 1}.Finite := Set.finite_le_nat (start + f' (k - 1) + 1)
  have subset : {l | start < l ∧ l ≤ start + (f' (k - 1) + 1)} ⊆ {l | l ≤ start + (f' (k - 1) + 1) } :=
    Set.sep_subset_setOf start.succ.le fun x ↦ x ≤ start + (f' (k - 1) + 1)
  exact Set.Finite.subset supsetfin subset

lemma inpnonemp2 {A : Type} (M : NPA A) (ss : ℕ → M.State) (start : ℕ) (f' : ℕ → ℕ) (k : ℕ) :
  (ss '' {l | start < l ∧ l ≤ start + f' (k - 1) + 1}).Nonempty := by
  -- have mbigger1 : c(f' (k - 1)) ≥ 1:= PNat.one_le (f' (k - 1))
    -- have biggerzero : ↑(f' (k-1)) > 0 := by simp
  have startplusonein : start + 1 ∈  {l | start < l ∧ l ≤ start + f' (k - 1) + 1} := by
    apply Set.mem_setOf.2
    constructor
    · omega
    · omega
  exact Set.Nonempty.image ss (Set.nonempty_of_mem startplusonein)

-- noncomputable def wbrun (M : NPA A) (ss : ℕ → M.State) (f' : ℕ → ℕ+) : ℕ → (M.StutterClosed).State
--   | 0 =>  (ss 0 , Sum.inr ⟨(M.parityMap (ss 0)), by simp⟩)
--   | n + 1 => if f' (n) = 1 then
--           -- let q : M.State := ss (Nat.fold (n - 1) (fun i _ xs ↦ xs + (f' i)) 1)
--           let q : M.State := (wbrun M ss f' n).fst -- Dit werkt zo niet, maar hoe wel??
--           (q, Sum.inr ⟨(M.parityMap q), by simp⟩)
--         else
--           let start : ℕ := (Nat.fold (n - 1) (fun i _ xs ↦ xs + (f' i)) 1) - 1
--           -- let p : ℕ := sSup (M.parityMap '' {ss k | (k > start) ∧ k ≤ (start + (f (k - 1)))})
--           let maxp : ℕ := sSup (M.parityMap '' (ss '' {l | (start < l) ∧ (l ≤ (start + f' (n - 1)))}))
--           (ss (start + f' (n - 1)), Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange _ _ (inpnonemp2 _ _ _ _ _) (inpfinite1 _ _ _ _ _)⟩)

  -- | _ => sorry
theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
  let Ms : NPA A := M.StutterClosed
  ext w
  constructor
  · intro h
    rw [NPA.AcceptedOmegaLang] at h ⊢
    apply Set.mem_setOf.1 at h
    rw [NPA.ParityAccept] at h
    rw [StutterClosure]
    apply Set.mem_setOf.2
    apply Exists.elim at h
    sorry
    sorry
  · intro h
    rw [StutterClosure] at h
    apply Membership.mem.out at h
    -- rw [NPA.AcceptedOmegaLang]
    obtain ⟨w', ⟨hw'inlang, ⟨wb, f, f', hwb⟩⟩⟩ := h -- Is this better than doing it in two steps?
    -- obtain ⟨wb, f, f', hwb⟩ := hw'stutequiv
    have wbaccepted : wb ∈ Ms.AcceptedOmegaLang := by
      rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
      obtain ⟨ss, ⟨⟨ssinit, ssnext⟩ , sspareven⟩ ⟩ := hw'inlang

      let ss' : ℕ → Ms.State :=
        fun k ↦
        if k = 0 then
          (ss 0 , Sum.inr ⟨(M.parityMap (ss 0)), by simp⟩)
        else if f' (k - 1) = 0 then
          let q : M.State := ss ((∑ m ∈ Finset.range k, (f' m + 1)))
          -- let q : M.State := (ss' (k - 1)).fst -- Dit werkt zo niet, maar hoe wel??
          (q, Sum.inr ⟨(M.parityMap q), by simp⟩)
        else
          let start : ℕ := ∑ m ∈ Finset.range (k-1), (f' m + 1)
          let maxp : ℕ := sSup (M.parityMap '' (ss '' {l | (start < l) ∧ (l ≤ (start + f' (k - 1) + 1))}))
          ( ss (start + f' (k - 1) + 1)
          , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange _ _ (inpnonemp2 _ _ _ _ _) (inpfinite1 _ _ _ _ _)⟩)
      use ss'

      rw [NA.InfRun]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · apply Set.mem_setOf.2
        use ss 0
        constructor
        · exact ssinit
        · exact rfl
      · intro k
        have sumcorrect : (ss' k).fst = ss (∑ m ∈ Finset.range k, (f' m + 1)) := by
          cases k
          · unfold ss'
            simp only [↓reduceIte, Finset.range_zero, Finset.sum_empty]
          case succ n =>
            simp only [ss']
            simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
            if h1 : (f' n) = 0 then
              simp only [↓reduceIte, h1]
            else
              simp only [↓reduceIte, h1]
              apply congrArg
              rw [Finset.sum_range_succ]
              rw [add_assoc]

        have ss'numstate : ∃ p : ↑(Set.range M.parityMap) , (ss' k).snd = Sum.inr p := by
          cases k
          · unfold ss'
            simp only [↓reduceIte, Sum.inr.injEq, exists_eq']
          · unfold ss'
            expose_names
            simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
              Subtype.exists, Set.mem_range]
            if h1 : (f' n) = 0 then
              simp only [↓reduceIte, h1]
              simp only [Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right',
                exists_apply_eq_apply]
            else
              simp only [↓reduceIte, h1]
              simp only [Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right']
              sorry




        if h1 : (f' k) = 0  then
          conv =>
            rhs
            simp only [ss']

          simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
          simp only [Nat.add_one_sub_one]
          simp [h1]
          rw [← Prod.eta (ss' k)]
          rw [sumcorrect]
          rcases ss'numstate with ⟨p, hp⟩
          rw [hp]

          rw [Finset.sum_range_succ]
          rw [h1]
          simp only [zero_add]
          unfold next NPA.toNA Ms

          unfold NPA.StutterClosed
          simp only [Set.mem_union]
          left
          left

          simp
          let r := ∑ m ∈ Finset.range k, (f' m + 1)
          have sumstutequiv (l : ℕ ) : wb l = w' (∑ m ∈ Finset.range l, (f' m + 1)) := by
            induction' l with d hd
            · simp only [Finset.range_zero, Finset.sum_empty]
              rw [hwb.2]
              unfold functiononword
              simp only [add_pos_iff, zero_lt_one, or_true, ↓reduceIte]
            ·
              rw [hwb.2] at  ⊢
              unfold functiononword at ⊢
              rw [Finset.sum_range_succ]

              sorry
          rw [sumstutequiv]
          exact ssnext (∑ m ∈ Finset.range k, (f' m + 1))

        else

          sorry
          -- let m := (f' k).toNat
          -- cases m
          -- split
          -- · case
      · sorry

    sorry


#eval let f : ℕ → ℕ := (fun i ↦ if i = 1 then 0 else if i = 0 then 0 else if i = 2 then 2 else 0); ∑ m∈ Finset.range 5, (f m + 1)
example (n: ℕ+) : PNat.val n = n := by exact rfl
