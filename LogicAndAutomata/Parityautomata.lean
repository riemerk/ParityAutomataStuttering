import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic
import Mathlib
import Mathlib.Probability.Distributions.Fernique

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

lemma inpnonemp1 {A : Type} {M : NPA A} (n : ℕ) (ss : Stream' M.State) (hn: n ≥ 1) :
          (ss '' {k | (k > 0) ∧ (k ≤ n)}).Nonempty:= by
          have onein : 1 ∈ {k | (k>0)∧ (k ≤ n)} := by
            apply Set.mem_setOf.2
            simp only [gt_iff_lt, zero_lt_one, true_and, hn]
          exact Set.Nonempty.image ss (Set.nonempty_of_mem onein)

lemma inpfinite1 {A : Type} {M : NPA A} (n : ℕ) (ss : Stream' M.State):
          (ss '' {k | (k > 0) ∧ (k ≤ n)}).Finite:= by
          apply Set.Finite.image ss
          have supsetfin:  {k | k≤n}.Finite := Set.finite_le_nat (n)
          have subset : {k | (k > 0) ∧ (k ≤ n)} ⊆ {k |k ≤ n } :=
            Set.sep_subset_setOf (Nat.succ 0).le fun x ↦ x ≤ n
            -- Set.sep_subset_setOf start.succ.le fun x ↦ x ≤ start + (f' (k - 1) + 1)
          exact Set.Finite.subset supsetfin subset
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
                          ∪ {(x, p') | ∃ n, ∃ ss : Stream' M.State, n ≥ 1 ∧ (M.FinRunStart n (fun _ ↦ k) ss s)
                            ∧ p' = Sum.inr ⟨sSup (M.parityMap '' (ss '' {k | (k > 0) ∧ (k ≤ n)})), ssupinrange _ _ (inpnonemp1
                              n ss sorry) (inpfinite1 n ss)⟩}

  FinAlph := FinAlph
  FinState := by have h1 : Finite M.State := FinState ; have h2: Finite A := FinAlph; exact Finite.instProd
  DecidableA := DecidableA

-- Is this implementation efficient?
-- And is this proof efficient?? (leesbaarheid verbeteren en probeer met omega en linarith)
-- En gebruik simp alleen maar simp only als tussenstap
-- Indentatie, := by maar kan ook · voor andere goals

def nbetweensumk (n:Nat) (f: Stream' ℕ) (k : Nat): Prop := ((∑ m∈Finset.range k, (f m + 1))≤ n) ∧ (n < (∑ m∈ Finset.range (k + 1), (f m + 1)))

-- Met Nat.find kan je ook alleen de tweede pakken
theorem kexists (n:ℕ) (f: Stream' ℕ) : ∃k, ((∑ m∈Finset.range k, (f m + 1))≤ n) ∧ (n < (∑ m∈ Finset.range (k + 1), (f m + 1))) := by
  let g : Stream' ℕ :=  fun k ↦ (∑ m∈Finset.range k, (f m + 1))
  have fstrictmono : StrictMono fun k ↦ (∑ m∈Finset.range k, (f m + 1)) := by
    refine strictMono_nat_of_lt_succ ?_
    expose_names
    intro m
    rw [Finset.sum_range_succ]
    simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]


  have statement1: ∃ k, (((∑ m∈ Finset.range (k), (f m + 1))< (n+1)) ∧ ((n+1) ≤ (∑ m∈Finset.range (k+1), (f m + 1)))) := by
    refine StrictMono.exists_between_of_tendsto_atTop  fstrictmono ?_ ?_
    · exact StrictMono.tendsto_atTop fstrictmono
    · simp only [Finset.range_zero, Finset.sum_empty, add_pos_iff, zero_lt_one, or_true]

  obtain ⟨m, ⟨statml, statmr⟩⟩ := statement1
  rw [← Nat.succ_eq_add_one] at statml statmr
  rw [Nat.lt_succ] at statml
  use m
  exact ⟨statml, Nat.lt_of_succ_le statmr⟩

def functiononword (w: Stream' A) (f : Stream' ℕ) (n : ℕ) : A :=
  let l : ℕ := Nat.find (kexists n f)
  w l

#eval functiononword (fun n↦ if (Even n) then 'a' else 'b') (fun _ ↦ 3) 3

def StutterEquivalent (w: Stream' A) (w' : Stream' A) : Prop :=
∃ wb : Stream' A,  ∃ f : Stream' Nat,  ∃ f' : Stream' Nat, w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L: Set (Stream' A)) : Set (Stream' A) :=
{w | ∃ w' ∈ L, (StutterEquivalent w w')}

lemma inpfinite2 {A : Type} (M : NPA A) (ss : Stream' M.State) (start : ℕ) (f' : Stream' ℕ) (k : ℕ) :
  Finite ↑(ss '' {l | start < l ∧ l ≤ start + f' (k - 1) + 1}) := by
  apply Set.Finite.image ss
  have supsetfin:  {l | l ≤ start + f' (k - 1) + 1}.Finite := Set.finite_le_nat (start + f' (k - 1) + 1)
  have subset : {l | start < l ∧ l ≤ start + (f' (k - 1) + 1)} ⊆ {l | l ≤ start + (f' (k - 1) + 1) } :=
    Set.sep_subset_setOf start.succ.le fun x ↦ x ≤ start + (f' (k - 1) + 1)
  exact Set.Finite.subset supsetfin subset

lemma inpnonemp2 {A : Type} (M : NPA A) (ss : Stream' M.State) (start : ℕ) (f' : Stream' ℕ) (k : ℕ) :
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

-- lemma wbaccepted (w w' Stream' A) (h: StutterEquivalent w w') (M: NPA A) :  ∈ M.AcceptedOmegaLang := by sorry
--lemma maken, dan extract_goal en dan lemma beetje mooier maken
lemma wbaccepted_of_specific_stutterequivalent {A : Type} (M : NPA A) (w w' : Stream' A) (wb : Stream' A) (f f' : Stream' ℕ):
    w' ∈ M.AcceptedOmegaLang →
        w = functiononword wb f ∧ w' = functiononword wb f' → wb ∈ M.StutterClosed.AcceptedOmegaLang := by sorry

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
    -- by apply wbaccepted M w w' hw'inlang wb f f' hwb
      rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
      obtain ⟨ss, ⟨⟨ssinit, ssnext⟩ , sspareven⟩ ⟩ := hw'inlang

      let ss' : Stream' Ms.State :=
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
          , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange _ _ (inpnonemp2 _ _ _ _ _) (inpfinite2 _ _ _ _ _)⟩)
      use ss'

      rw [NA.InfRun]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · apply Set.mem_setOf.2
        exact ⟨ss 0, ssinit, rfl⟩
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
              simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right',
                exists_apply_eq_apply]
            else
              simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right']
              have inrange : sSup (M.parityMap '' (ss '' {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1})) ∈ Set.range M.parityMap := by
                refine ssupinrange M ((ss '' {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1})) ?_ ?_
                · simp only [Set.image_nonempty]
                  have mem: (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)∈ {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1} := by
                    apply Set.mem_setOf.2
                    simp only [add_assoc, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, le_refl,
                      and_self]
                  exact Set.nonempty_of_mem mem
                · apply Set.Finite.image ss
                  have supsetfin:  {l | l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1}.Finite := Set.finite_le_nat (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)
                  have subset : {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1} ⊆ {l | l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1} := by
                    exact
                      Set.sep_subset_setOf (∑ m ∈ Finset.range n, (f' m + 1)).succ.le fun x ↦
                        x ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1
                  exact Set.Finite.subset supsetfin subset
              exact inrange

        -- algemener maken
        -- w' = functiononword wb f
        have sumstutequiv (l : ℕ ) : wb l = w' (∑ m ∈ Finset.range l, (f' m + 1)) := by
            induction' l with d hd
            · simp only [Finset.range_zero, Finset.sum_empty]
              rw [hwb.2]
              unfold functiononword
              have zerotrue : ∑ m ∈ Finset.range 0, (f' m + 1) ≤ 0 ∧ 0 < ∑ m ∈ Finset.range (0 + 1), (f' m + 1) := by
                simp only [Finset.range_zero, Finset.sum_empty, le_refl, zero_add, Finset.range_one,
                  Finset.sum_singleton, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_self]
              simp only [nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_range, Nat.add_eq_zero,
                one_ne_zero, and_false, imp_false, not_lt]

              apply congrArg
              apply Eq.symm
              apply (Nat.find_eq_zero (kexists 0 f')).2
              exact zerotrue
            · rw [hwb.2]
              unfold functiononword
              simp at hd
              simp only
              apply congrArg

              have donetrue : ∑ m ∈ Finset.range (d+1), (f' m + 1) ≤ ∑ m ∈ Finset.range (d + 1), (f' m + 1) ∧
            ∑ m ∈ Finset.range (d + 1), (f' m + 1) < ∑ m ∈ Finset.range (d + 2), (f' m + 1) := by
                constructor
                · exact Finset.sum_le_sum_of_ne_zero fun x a a_1 ↦ a

                · rw [← one_add_one_eq_two]
                  rw [← add_assoc]
                  nth_rewrite 2 [← Nat.succ_eq_add_one]
                  nth_rewrite 2 [Finset.sum_range_succ]
                  simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

              have smaller : Nat.find (kexists ((∑ m ∈ Finset.range (d + 1), (f' m + 1))) f') ≤ d+1 := by
                exact Nat.find_le donetrue

              have dfalse: ¬( ∑ m ∈ Finset.range (d+1), (f' m + 1) ≤ ∑ m ∈ Finset.range (d), (f' m + 1) ∧
                    ∑ m ∈ Finset.range (d), (f' m + 1) < ∑ m ∈ Finset.range (d + 2), (f' m + 1)) := by
                    simp only [not_and_or]
                    left
                    simp only [not_le]
                    rw [Finset.sum_range_succ]
                    simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

              have bigger : Nat.find (kexists ((∑ m ∈ Finset.range (d + 1), (f' m + 1))) f') ≥ d+1 := by
                apply (Nat.le_find_iff (kexists ((∑ m ∈ Finset.range (d + 1), (f' m + 1))) f') (d+1)).2
                intro t
                intro ht
                simp only [not_and_or]
                right
                simp only [not_lt]
                have fstrictmono : StrictMono fun k ↦ (∑ m∈Finset.range k, (f' m + 1)) := by
                  refine strictMono_nat_of_lt_succ ?_
                  expose_names
                  intro m
                  rw [Finset.sum_range_succ]
                  simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
                simp only [ge_iff_le]



                apply Nat.lt_iff_add_one_le.1 at ht
                have fmono: Monotone fun k ↦ (∑ m∈Finset.range k, (f' m + 1)) := by
                  exact StrictMono.monotone fstrictmono
                exact fmono ht
              exact Nat.le_antisymm bigger smaller

        conv =>
          rhs
          simp only [ss']
        simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
        simp only [Nat.add_one_sub_one]
        if h1 : (f' k) = 0  then

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
          rw [sumstutequiv]
          exact ssnext (∑ m ∈ Finset.range k, (f' m + 1))

        else

          simp [h1]
          rw [← Prod.eta (ss' k)]
          rw [sumcorrect]
          rcases ss'numstate with ⟨p, hp⟩
          rw [hp]
          unfold next NPA.toNA Ms

          unfold NPA.StutterClosed
          simp only [Set.mem_union]
          right
          nth_rewrite 1 [add_assoc]
          apply Set.mem_setOf.2
          use (f' k + 1)
          use Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ss
          have stutw' (b :ℕ) (hb : b < f' k + 1) : w' (b + ∑ m ∈ Finset.range k, (f' m + 1)) = w' (∑ m ∈ Finset.range k, (f' m + 1)):= by
            rw [hwb.2]
            unfold functiononword
            simp only
            apply congrArg

            have fstrictmono : StrictMono fun k ↦ (∑ m∈Finset.range k, (f' m + 1)) := by
              refine strictMono_nat_of_lt_succ ?_
              expose_names
              intro m
              rw [Finset.sum_range_succ]
              simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
            have same : ∀ (q :ℕ),
            (∑ m ∈ Finset.range q, (f' m + 1) ≤ b + ∑ m ∈ Finset.range k, (f' m + 1) ∧
            b + ∑ m ∈ Finset.range k, (f' m + 1) < ∑ m ∈ Finset.range (q + 1), (f' m + 1)) ↔ (∑ m ∈ Finset.range q, (f' m + 1) ≤ ∑ m ∈ Finset.range k, (f' m + 1) ∧
            ∑ m ∈ Finset.range k, (f' m + 1) < ∑ m ∈ Finset.range (q + 1), (f' m + 1)):= by
              intro q
              constructor
              · intro hq
                constructor
                · have lekplusone : (∑ m ∈ Finset.range q, (f' m + 1)) < (∑ m ∈ Finset.range (k+1), (f' m + 1)) := by
                    rw [Finset.sum_range_succ]
                    have ble : b + ∑ m ∈ Finset.range k, (f' m + 1) < (f' k + 1) + ∑ m ∈ Finset.range k, (f' m + 1) := Nat.add_lt_add_right hb (∑ m ∈ Finset.range k, (f' m + 1))
                    rw [add_comm]
                    exact Nat.lt_of_le_of_lt hq.1 ble
                  apply (StrictMono.lt_iff_lt fstrictmono).1 at lekplusone
                  apply (StrictMono.le_iff_le fstrictmono).2
                  exact Nat.le_of_lt_succ lekplusone
                · exact Nat.lt_of_add_left_lt hq.2
              · intro hq
                constructor
                · apply le_add_left
                  exact hq.1
                · have kplusone : ∑ m ∈ Finset.range (k+1), (f' m + 1) ≤  ∑ m ∈ Finset.range (q + 1), (f' m + 1) := by
                    have kleqone : k < q+1 := by
                      apply (StrictMono.lt_iff_lt fstrictmono).1
                      exact hq.2
                    apply (StrictMono.le_iff_le fstrictmono).2
                    exact kleqone
                  have blekplusone : b + ∑ m ∈ Finset.range k, (f' m + 1) <   ∑ m ∈ Finset.range (k+1), (f' m + 1) := by
                    rw [Finset.sum_range_succ]
                    rw [add_comm]
                    exact Nat.add_lt_add_left hb (∑ m ∈ Finset.range k, (f' m + 1))
                  exact Nat.lt_of_lt_of_le blekplusone kplusone
            exact Nat.find_congr' @same


          refine ⟨?_, ⟨?_, ?_⟩⟩
          · simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
          · unfold FinRunStart
            refine ⟨?_, ?_⟩
            · unfold Stream'.drop
              unfold Stream'.get
              simp only [zero_add]
            · intro b hb
              unfold Stream'.drop
              unfold Stream'.get
              simp only
              rw [sumstutequiv k]
              rw [add_right_comm]
              rw [← stutw' b hb]
              exact ssnext  (b + ∑ m ∈ Finset.range k, (f' m + 1))
          · simp only [Sum.inr.injEq, Subtype.mk.injEq]
            have inpsame : (ss '' {l | ∑ m ∈ Finset.range k, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range k, (f' m + 1) + f' k + 1}) = (Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ss '' {k_1 | k_1 > 0 ∧ k_1 ≤ f' k + 1}) := by
              unfold Stream'.drop
              unfold Stream'.get
              unfold Set.image
              apply Set.ext_iff.2
              intro x
              repeat rw [Set.mem_setOf]
              refine ⟨?_,?_⟩
              · intro h
                obtain ⟨a, ⟨ha, ssax⟩⟩:=h
                rw [Set.mem_setOf] at ha
                use a - ∑ m ∈ Finset.range k, (f' m + 1)
                constructor
                · rw [add_assoc] at ha
                  rw [add_comm] at ha
                  apply Set.mem_setOf.2
                  constructor
                  · simp only [gt_iff_lt, tsub_pos_iff_lt, ha.1]
                  · simp only [tsub_le_iff_right, ha.2]
                · simp only
                  rw [add_comm]
                  rw [Nat.add_sub_cancel' (le_of_lt ha.1)]
                  exact ssax
              · intro h
                obtain ⟨a, ⟨ha, ssax⟩⟩:=h
                use (a + ∑ m ∈ Finset.range k, (f' m + 1))

                constructor
                · rw [Set.mem_setOf]
                  apply Set.mem_setOf.1 at ha
                  constructor
                  · simp only [lt_add_iff_pos_left, ha]
                  · rw [add_assoc]
                    rw [add_comm]
                    simp only [add_le_add_iff_left, ha]
                · simp only [ssax]
            exact congrArg sSup (congrArg (Set.image M.parityMap) inpsame)

      · have sSupsame : (sSup (M.parityMap '' InfOcc ss)) = (sSup (Ms.parityMap '' InfOcc ss')) := by

          let s := (sSup (M.parityMap '' InfOcc ss))
          have h1 : ∀ a ∈ (Ms.parityMap '' InfOcc ss'), a ≤ s := by sorry
          have h : ∃ n, (∀ a ∈ (Ms.parityMap '' InfOcc ss'), a ≤ n) := by use s

          have h2 : ∀ w < s, ∃ a ∈ (Ms.parityMap '' InfOcc ss'), w < a := by
            sorry

          rw [Nat.sSup_def h]
          apply Eq.symm
          have dec (n: ℕ) : Decidable  (∀ a ∈ (Ms.parityMap '' InfOcc ss'), a ≤ n) := by

            have := @Fintype.decidableForallFintype (Ms.parityMap '' InfOcc ss') (· ≤ n) _
            have inpfin : Fintype ↑(NPA.parityMap '' InfOcc ss') := by sorry

            simp only [Subtype.forall, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂] at this
            apply this
          expose_names
          have equals  : Nat.find h = s := by
            refine (Nat.find_eq_iff h).mpr ?_
            constructor
            · exact h1
            · intro n hn f
              -- Nu zeggen dat we dus een toestand hebben in ss die de max parity heeft. Dan op een of andere manier die vinden in ss' en klaar
              -- Vragen hoe het zit met decidable!!!
              sorry


          unfold s at equals
          convert equals

        rw [← sSupsame]
        exact sspareven

    sorry


#eval let f : Stream' ℕ := (fun i ↦ if i = 1 then 0 else if i = 0 then 0 else if i = 2 then 2 else 0); ∑ m∈ Finset.range 5, (f m + 1)
example (n: ℕ+) : PNat.val n = n := by exact rfl
