import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic
import Mathlib
import Mathlib.Probability.Distributions.Fernique
import LogicAndAutomata.NPA
import LogicAndAutomata.Stuttering

-- set_option diagnostics true

namespace Automata
variable {A : Type}

-- Proof subset
-- Definitions
-- Definition 4.2.1
def subset_wb_f_pair {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
    (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
    : Stream' (A × ℕ)
| i =>
    let l := if i = 0 then 0 else (subset_wb_f_pair ρ_w_run ρ_w_pareven (i-1)).2
    have notloopinletterstate : ∃ n>0, ρ_w (l+n) matches (b, Sum.inr c) := by sorry
    let m := Nat.find notloopinletterstate
    (w l, l + m)

def subset_wb {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
    (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' A
| i => (subset_wb_f_pair ρ_w_run ρ_w_pareven i).1

def subset_f {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
    (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' ℕ
| 0 => (subset_wb_f_pair ρ_w_run ρ_w_pareven 0).2 - 1
| i => (subset_wb_f_pair ρ_w_run ρ_w_pareven i).2 - (subset_wb_f_pair ρ_w_run ρ_w_pareven (i - 1)).2 - 1

-- ss is run op w
-- Definition 4.2.3
open Classical in
noncomputable def subset_f'_rhow'_pair {M : NPA A} {w : Stream' A}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                  (f : Stream' ℕ) : Stream' (ℕ × (Stream' M.State))
| i =>
  if f i = 0 then
    let a := ((subset_wb_f_pair ρ_w_run ρ_w_pareven i).1)
      have this : ∃n, ∃ ρ_p : Stream' M.State,
                  (M.FinRunStart n (fun _ ↦ a) ρ_p (ρ_w (subset_wb_f_pair ρ_w_run ρ_w_pareven i).2).1
                  ∧ ρ_p n = (ρ_w (subset_wb_f_pair ρ_w_run ρ_w_pareven (i+1)).2).1) := by sorry

      -- Hier misschien de kleinste kiezen...
      -- let n := Nat.find ex
      ---...
      -- let n_h

      let n := this.choose
      let n_h := this.choose_spec
      let ss_fin :=  n_h.choose
      (n, ss_fin)
    -- have dec: Decidable ((ss (subset_wb_f_pair hss heven (i+1)).2).1 ∈
    --           (M.next (ss (subset_wb_f_pair hss heven i).2).1 ((subset_wb_f_pair hss heven i).1)))
    --           := by sorry
    -- -- Finset.decidableMem
    -- if (ss (subset_wb_f_pair hss heven (i+1)).2).1 ∈
    --    (M.next (ss (subset_wb_f_pair hss heven i).2).1 ((subset_wb_f_pair hss heven i).1)) then
    --   (0, fun k ↦ if k = 1 then (ss (subset_wb_f_pair hss heven (k+1)).2).1 else (ss 0 ).1)
    -- else
    --   let a := ((subset_wb_f_pair hss heven i).1)
    --   have this : ∃n, ∃ ss' : Stream' M.State,
    --               (M.FinRunStart n (fun _ ↦ a) ss' (ss (subset_wb_f_pair hss heven i).2).1
    --               ∧ ss' n = (ss (subset_wb_f_pair hss heven (i+1)).2).1) := by sorry

    --   -- Hier misschien de kleinste kiezen...
    --   -- let n := Nat.find ex
    --   ---...
    --   -- let n_h

    --   let n := this.choose
    --   let n_h := this.choose_spec
    --   let ss_fin :=  n_h.choose
    --   (n, ss_fin)
  else
    (0, fun k ↦if k = 1 then (ρ_w (subset_wb_f_pair ρ_w_run ρ_w_pareven (k+1)).2).1 else (ρ_w 0).1)

noncomputable def subset_f' {M : NPA A} {w : Stream' A}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                  (f : Stream' ℕ) : Stream' ℕ
| i => (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven f i).1

noncomputable def subset_rhow' {M : NPA A} {w : Stream' A}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                  (f : Stream' ℕ) : Stream' M.State
| 0 => (ρ_w 0).1
| i =>
  let f' := subset_f' ρ_w_run ρ_w_pareven f
  let k_b : ℕ :=  Nat.find (kexists i f')
  let i := (∑ m∈ Finset.range k_b, (f' m + 1)) - i
  (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven f i).2 i

-- Claim 4.2.4 (approximately)
lemma subset_stutequiv_w_w' {A : Type} {M : NPA A} {w : Stream' A}
        {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
        (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) :
      let wb := subset_wb ρ_w_run ρ_w_pareven;
      let f := subset_f ρ_w_run ρ_w_pareven ;
      let f' := subset_f' ρ_w_run ρ_w_pareven f;
      StutterEquivalent w (functiononword wb f') := by
  intro wb f f'
  unfold StutterEquivalent
  use wb
  use f
  use f'
  simp only [and_true]
  unfold functiononword

  simp only
  apply funext
  intro x
  unfold wb
  unfold subset_wb
  unfold subset_wb_f_pair
  simp only


  if hn: (Nat.find (kexists x f)) = 0 then

    rw [Nat.find_eq_zero] at hn
    unfold n_lt_sumk at hn
    sorry
    -- simp [hn]
    -- rw [Nat.find_eq_zero] at hn
    -- unfold n_lt_sumk at hn
    -- simp at hn
    -- unfold f at hn
    -- unfold subset_f at hn
    -- simp at hn
    -- unfold subset_wb_f_pair at hn
    -- let i := 0
    -- simp only [i] at hn
    -- simp only [↓reduceIte] at hn


    -- rw [i] at hn
    -- obtain ⟨h, hh⟩ := hn

    -- simp only [↓reduceIte]
    -- simp only [gt_iff_lt, zero_add]

    -- simp at hn


    -- split

    -- expose_names
    -- · simp only [↓reduceIte]
    --   simp at hn
    --   unfold wb_struct_of_w_and_ss at hn
    --   simp [heq] at hn
    --   rw [hn]
    -- · expose_names
    --   simp only [Bool.false_eq_true, ↓reduceIte]
    --   simp at hn
    --   unfold wb_struct_of_w_and_ss at hn
    --   simp only [↓reduceIte,  Bool.false_eq_true] at hn
    --   have notloopinletterstate : ∃ n, (n>0∧ (ss n) matches (b, Sum.inr c)) := by sorry

    --   have findgezero : (Nat.find notloopinletterstate) > 0 := by
    --     -- exact [(Nat.find_spec notloopinletterstate).1]
    --     sorry
    --   -- simp only [findgezero] at hn
    --   rw [Nat.lt_addadd_one_le_iff] at findgezero

    --   simp only [ Bool.false_eq_true, gt_iff_lt, exists_prop, Nat.le_find_iff,
    --     Nat.lt_one_iff, not_and, Bool.not_eq_true, forall_eq, lt_self_iff_false, IsEmpty.forall_iff,
    --     Nat.sub_add_cancel, Nat.lt_find_iff] at hn



    --   rw [← tsub_lt_iff_left] at hn

    --   sorry

  else
    sorry

-- Claim 4.2.4
lemma subset_rhow'_run {A : Type} {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
      (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
      (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) :
      let wb := subset_wb ρ_w_run ρ_w_pareven;
      let f := subset_f ρ_w_run ρ_w_pareven;
      let f' := subset_f' ρ_w_run ρ_w_pareven f;
      M.InfRun (functiononword wb f') (subset_rhow' ρ_w_run ρ_w_pareven f) := by
  intro wb f f'
  unfold NA.InfRun
  obtain ⟨ssinit, ssnext⟩ := ρ_w_run
  constructor
  · unfold subset_rhow'
    simp only
    unfold NA.init NPA.toNA NPA.StutterClosed at ssinit
    simp at ssinit
    obtain ⟨s0, hs0⟩:=ssinit
    rw [← hs0.2]
    simp only
    exact hs0.1
  · intro k

    unfold subset_rhow'
    simp only
    unfold subset_f'_rhow'_pair

    simp only


    sorry

-- Claim 4.2.5
lemma subset_rhow'_pareven {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
      (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
      (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) :
      let wb := subset_wb ρ_w_run ρ_w_pareven;
      let f := subset_f ρ_w_run ρ_w_pareven;
      let f' := subset_f' ρ_w_run ρ_w_pareven f;
      Even <| sSup <| M.parityMap '' (InfOcc <| subset_rhow' ρ_w_run ρ_w_pareven f) := by

  sorry

-- Proof Supset
-- Definitions:
-- Definition 4.2.6
noncomputable def supset_rhowb {M : NPA A} (ρ_w' : Stream' M.State) (f : Stream' ℕ) :
                  Stream' (M.StutterClosed).State
| k =>
    if k = 0 then
      (ρ_w' 0 , Sum.inr ⟨(M.parityMap (ρ_w' 0)), inrange (ρ_w' 0)⟩)
    else if f (k - 1) = 0 then
      let q : M.State := ρ_w' ((∑ m ∈ Finset.range k, (f m + 1)))
      (q, Sum.inr ⟨(M.parityMap q), inrange q⟩)
    else
      let start : ℕ := ∑ m ∈ Finset.range (k-1), (f m + 1)
      let maxp : ℕ := sSup (M.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + f (k - 1) + 1))}))
      ( ρ_w' (start + f (k - 1) + 1)
      , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ρ_w' start (f (k - 1) + 1) (by simp)) (inpfinite ρ_w' start (f (k- 1) + 1))⟩)

noncomputable def parmap_sup_decidable (M : NPA A) (ss : Stream' M.State) (n: ℕ) : Decidable  (∀ a ∈ (M.parityMap '' InfOcc ss), a ≤ n) := by
  have := @Fintype.decidableForallFintype (M.parityMap '' InfOcc ss) (· ≤ n) _
  have inpfin : Fintype ↑(NPA.parityMap '' InfOcc ss) := by
    expose_names
    have infoccfinite : Fintype (InfOcc ss) := by
      unfold InfOcc
      exact @Fintype.ofFinite {x | ∃ᶠ (k : ℕ) in Filter.atTop, ss k = x} <|
        Set.Finite.subset (@Set.finite_univ M.State M.FinState) (fun ⦃a⦄ a ↦ trivial)


    refine (InfOcc ss).fintypeImage NPA.parityMap
  simp only [Subtype.forall] at this
  apply this

-- Definition 4.2.9
-- Here the pattern matching apperently does not work to show termination
-- Setting: w = wb[f], w' = wb[f']. Dan ss is run op wb en ss' is run op w'
noncomputable def supset_rhow {A : Type} {M : NPA A} (ρ_wb : Stream' (M.StutterClosed).State)
                  (ρ_w' : Stream' M.State) (w : Stream' A) (f f' : Stream' ℕ) (k : ℕ)
                  : (M.StutterClosed).State :=
  if k = 0 then
    ρ_wb 0
  else
    let k_b : ℕ :=  Nat.find (kexists (k-1) f)
    if fkb_zero : f k_b = 0 then
      ρ_wb (k_b + 1)
    else
      let i := k - ∑ m∈ Finset.range (k_b), (f m + 1) + 1 -- denk niet +1
      have dec: Decidable (((ρ_wb (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (supset_rhow ρ_wb ρ_w' w f f' (k - 1)) (w k))) := by sorry
      if h: ((ρ_wb (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (supset_rhow ρ_wb ρ_w' w f f' (k - 1)) (w k)) then
        if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
          ((ρ_wb (k_b + 1)).1, Sum.inr ⟨M.parityMap (ρ_wb (k_b + 1)).1, by simp only [Set.mem_range,
            exists_apply_eq_apply]⟩)
        else
          ((ρ_wb (k_b + 1)).1, Sum.inl (w k))
      else
        if hdiff1: f k_b ≤ f' k_b then
          if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
            if hdiff2: f k_b = f' k_b then
              (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1), Sum.inr ⟨M.parityMap (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1)), by simp⟩)
            else
              let start := i + ∑ m∈ Finset.range (k_b), (f' m + 1)
              let diff := f' k_b - f k_b
              let maxp : ℕ := sSup (M.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + diff))}))
              ((ρ_w' (start + diff))
              , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ρ_w' start diff (by omega)) (inpfinite  ρ_w' start diff)⟩)
          else
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
        else
          if hi: i <= f' k_b then
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
          else
            -- by exfalso
            -- sorry
            -- bewijs hier dat dat niet gebeurt
            if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
              ((ρ_wb (k_b + 1)).1, Sum.inr ⟨M.parityMap (ρ_wb (k_b + 1)).1, by simp only [Set.mem_range,
                exists_apply_eq_apply]⟩)
            else
              ((ρ_wb (k_b + 1)).1, Sum.inl (w k))

-- Lemmas for claim 4.2.7
lemma sumcorrect_of_wbrun {A : Type} (M : NPA A) (f' : Stream' ℕ) :
  ∀ (ss : Stream' (NA.State A)),
    Even (sSup (NPA.parityMap '' InfOcc ss)) →
          ∀ (k : ℕ), (supset_rhowb ss f' k).1 = ss (∑ m ∈ Finset.range k, (f' m + 1)) := by
  intro Ms ss k
  cases' k with n
  · unfold supset_rhowb
    simp only [↓reduceIte, Finset.range_zero, Finset.sum_empty]
  · simp only [supset_rhowb, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1]
    else
      simp only [↓reduceIte, h1]
      apply congrArg
      rw [Finset.sum_range_succ, add_assoc]

lemma ss'numstate_of_wbrun {A : Type} {M : NPA A} (f' : Stream' ℕ) (ss : Stream' (NA.State A)) (k : ℕ) :
                           let ss' := supset_rhowb ss f'; (ss' k).1 = ss (∑ m ∈ Finset.range k, (f' m + 1)) →
                           ∃ p, (ss' k).2 = Sum.inr p := by
  intro ss' hk
  cases' k with n
  · unfold ss' supset_rhowb
    simp only [↓reduceIte, Sum.inr.injEq, exists_eq']
  · unfold ss' supset_rhowb
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      Subtype.exists, Set.mem_range]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right',
        exists_apply_eq_apply]
    else
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right']
      refine @ssupinrange A M ((ss '' {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1})) ?_ ?_
      · simp only [Set.image_nonempty]
        refine Set.nonempty_of_mem (x:= (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)) ?_
        · apply Set.mem_setOf.2
          simp only [add_assoc, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, le_refl,
            and_self]
      · apply Set.Finite.image ss
        refine' Set.Finite.subset (s:= {l | l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1}) ?_ ?_
        · exact (Set.finite_le_nat (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1))
        · exact (Set.sep_subset_setOf (∑ m ∈ Finset.range n, (f' m + 1)).succ.le fun x ↦
              x ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)

lemma inpsame_of_specific {A : Type} (M : NPA A) (f' : Stream' ℕ)  (ss : Stream' (NA.State A)) (k: ℕ) :
      ss '' {l | ∑ m ∈ Finset.range k, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range k, (f' m + 1) + f' k + 1} =
        Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ss '' {k_1 | k_1 > 0 ∧ k_1 ≤ f' k + 1} := by
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
    · rw [add_assoc, add_comm] at ha
      apply Set.mem_setOf.2
      simp only [gt_iff_lt, tsub_pos_iff_lt, tsub_le_iff_right]
      exact ha
    · simp only
      rw [add_comm, Nat.add_sub_cancel' (le_of_lt ha.1)]
      exact ssax
  · intro h
    obtain ⟨a, ⟨ha, ssax⟩⟩:=h
    use (a + ∑ m ∈ Finset.range k, (f' m + 1))
    constructor
    · rw [Set.mem_setOf]
      apply Set.mem_setOf.1 at ha
      simp only [lt_add_iff_pos_left]
      rw [add_assoc, add_comm]
      simp only [add_le_add_iff_left]
      exact ha
    · simp only [ssax]

-- Claim 4.2.7
lemma supset_rhowb_run {A : Type} {M : NPA A} (wb : Stream' A) (f' : Stream' ℕ) {w' : Stream' A} {ρ_w' : Stream' M.State}
                       (ρ_w'_run : M.InfRun w' ρ_w') (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w')))
                       (w'_wbf : w' = functiononword wb f') :
                       let ρ_wb := supset_rhowb ρ_w' f';
                       (M.StutterClosed).InfRun wb ρ_wb := by
  intro ρ_wb
  rw [NA.InfRun]
  obtain ⟨ρ_w'_init, ρ_w'_next⟩ := ρ_w'_run

  constructor
  · exact Set.mem_setOf.2 ⟨ρ_w' 0, ρ_w'_init, rfl⟩
  · intro k

    conv =>
      rhs
      simp only [ρ_wb, supset_rhowb]
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one]
    if h1 : (f' k) = 0  then
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (sumcorrect_of_wbrun M f' ρ_w' (ρ_w'_pareven))]
      rcases ss'numstate_of_wbrun f' ρ_w' k (sumcorrect_of_wbrun M f' ρ_w' ρ_w'_pareven k) with ⟨p, hp⟩
      rw [hp, Finset.sum_range_succ, h1, zero_add]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      refine Or.inl (Or.inl ?_)
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, existsAndEq,
        and_self, and_true]
      rw [← functiononword_eq_base_word (b:=0) w'_wbf k (by linarith), zero_add]
      exact ρ_w'_next (∑ m ∈ Finset.range k, (f' m + 1))

    else
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (sumcorrect_of_wbrun M f' ρ_w' ρ_w'_pareven)]
      rcases ss'numstate_of_wbrun f' ρ_w' k (sumcorrect_of_wbrun M f' ρ_w' ρ_w'_pareven k) with ⟨p, hp⟩
      rw [hp]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      right
      nth_rewrite 1 [add_assoc]
      apply Set.mem_setOf.2
      use (f' k + 1)
      use Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ρ_w'
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
      · unfold NA.FinRunStart
        refine ⟨?_, ?_⟩
        · unfold Stream'.drop Stream'.get
          simp only [zero_add]
        · intro b hb
          unfold Stream'.drop Stream'.get
          simp only
          rw [← functiononword_eq_base_word w'_wbf k hb, add_right_comm]
          exact ρ_w'_next  (b + ∑ m ∈ Finset.range k, (f' m + 1))
      · simp only [gt_iff_lt, Sum.inr.injEq, Subtype.mk.injEq]
        constructor
        · exact congrArg sSup (congrArg (Set.image M.parityMap) (inpsame_of_specific M f' ρ_w' k))
        · exact Eq.symm Stream'.get_drop'

-- Lemmas for claim 4.2.8
lemma par_map_inf_occ_of_ss_has_sup {A : Type} (M : NPA A) (ss' : Stream' M.State) :
              ∃ n, ∀ a ∈ NPA.parityMap '' InfOcc ss', a ≤ n := by
      have htest : ∃ n∈ (InfOcc ss'), ∀ a ∈ (InfOcc ss'), (M.parityMap a) ≤ (M.parityMap n) := by
        apply Set.exists_max_image (InfOcc ss') (M.parityMap)
        · unfold InfOcc
          exact Set.Finite.subset (@Set.finite_univ M.State M.FinState) (fun ⦃a⦄ a ↦ trivial)
        · unfold InfOcc
          rw [Set.nonempty_def]
          apply by_contradiction
          intro hneg
          apply forall_not_of_not_exists at hneg
          have forallxfinite : ∀ (x: M.State), (¬{ k:ℕ | ss' k = x}.Infinite) := by
            intro x
            have xnotinfilter : x∉ {x | ∃ᶠ (k : ℕ) in Filter.atTop, ss' k = x} := hneg x
            apply Set.notMem_setOf_iff.1 at xnotinfilter
            contrapose! xnotinfilter
            exact Nat.frequently_atTop_iff_infinite.2 xnotinfilter
          have union : Set.iUnion (fun (x : M.State)↦ { k:ℕ | ss' k = x}) = Set.univ := by
            rw [Set.iUnion_eq_univ_iff]
            intro k
            use ss' k
            simp only [Set.mem_setOf_eq]
          simp only [Set.not_infinite] at forallxfinite
          have unionfinite: (⋃ x, {k | ss' k = x}).Finite := @Set.finite_iUnion _ _ M.FinState _ forallxfinite
          rw [union] at unionfinite

          exact Set.infinite_univ unionfinite

      obtain ⟨n, hn⟩:= htest

      use (M.parityMap n)
      intro a ha
      rw [Set.mem_image] at ha
      obtain ⟨xa, hxa⟩ := ha
      rw [← hxa.2]
      apply hn.2
      exact hxa.1

-- Claim 4.2.8
open Classical in
lemma supset_rhowb_pareven {A : Type} {M : NPA A} (w : Stream' A) (f : Stream' ℕ) {f' : Stream' ℕ} {w' wb: Stream' A} {ρ_w' : Stream' M.State}
                       (ρ_w'_run : M.InfRun w' ρ_w') (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w')))
                       (w'_wbf : w' = functiononword wb f') :
                       let ρ_wb := supset_rhowb ρ_w' f';
                       Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)) := by
  intro ρ_wb
  let Ms := (M.StutterClosed)

  have samesup : sSup (M.parityMap '' InfOcc ρ_w') + 2 = sSup ((M.StutterClosed).parityMap '' InfOcc (supset_rhowb ρ_w' f')) := by
    have hMs : ∃ n, (∀ a ∈ (Ms.parityMap '' InfOcc ρ_wb), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup Ms ρ_wb

    rw [Nat.sSup_def hMs]
    have hM : ∃ n, (∀ a ∈ (M.parityMap '' InfOcc ρ_w'), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup M ρ_w'

    rw [Nat.sSup_def hM]

    -- Iets met +2 aanpassen
    --- goed hierover nadenken nog...
    rw [le_antisymm_iff]
    constructor
    · simp

      intro m hm
      rw [← tsub_lt_iff_right] at hm
      rw [Nat.lt_find_iff] at hm
      simp at hm
      unfold NPA.parityMap
      unfold Ms
      unfold NPA.StutterClosed

      simp only [decide_eq_true_eq, Prod.exists, Sum.exists, Sum.elim_inl, Nat.lt_one_iff,
        exists_and_right, Sum.elim_inr, Subtype.exists, Set.mem_range]
      specialize hm (m-2)
      simp at hm
      obtain ⟨x, hx⟩ := hm
      use x
      right
      use M.parityMap x
      constructor
      · sorry
      · rw [← tsub_lt_iff_right]
        exact hx.2
        sorry


      sorry
    · sorry

  rw [← samesup]
  apply Even.add ρ_w'_pareven even_two


-- Lemmas for waccepted
-- Claim 4.2.10
lemma supset_rhow_run {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ}
  {ρ_wb : Stream' (M.StutterClosed).State} {ρ_w' : Stream' M.State} (hw : w = functiononword wb f)
  (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)))
  (ρ_wb_run : M.StutterClosed.InfRun wb ρ_wb)
  (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w')))
  (ρ_w'run : M.InfRun w' ρ_w') : M.StutterClosed.InfRun w (supset_rhow ρ_wb ρ_w' w f f') := by
  unfold NA.InfRun
  obtain ⟨ρ_wb_init, ρ_wb_next⟩ := ρ_wb_run
  constructor
  · unfold supset_rhow
    simp only [↓reduceIte]
    exact ρ_wb_init
  · intro k

    unfold supset_rhow

    cases k
    ·
      -- zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]



      -- , zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]

      sorry
    · sorry

-- Claim 4.2.11
lemma supset_rhow_pareven {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ}
      {ρ_wb : Stream' (M.StutterClosed).State} {ρ_w' : Stream' M.State} (hw : w = functiononword wb f)
      (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)))
      (ρ_wb_run : M.StutterClosed.InfRun wb ρ_wb)
      (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w'))) (ρ_w'_run : M.InfRun w' ρ_w') :
      Even (sSup ((M.StutterClosed).parityMap '' InfOcc (supset_rhow ρ_wb ρ_w' w f f'))) := by sorry

-- Full theorem
theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
  let Ms : NPA A := M.StutterClosed
  ext w
  constructor
  · intro hwinlang
    rw [NPA.AcceptedOmegaLang] at hwinlang ⊢
    rw [Set.mem_setOf, NPA.ParityAccept] at hwinlang
    rw [StutterClosure, Set.mem_setOf]
    obtain ⟨ρ_w, ⟨ρ_w_run, ρ_w_pareven⟩⟩ := hwinlang
    let wb := subset_wb ρ_w_run ρ_w_pareven
    let f := subset_f ρ_w_run ρ_w_pareven
    let f' := subset_f' ρ_w_run ρ_w_pareven f
    use (functiononword wb f')
    rw [Set.mem_setOf]
    let ρ_w' := subset_rhow' ρ_w_run ρ_w_pareven f
    unfold NPA.ParityAccept
    constructor
    · use ρ_w'
      exact ⟨subset_rhow'_run ρ_w_run ρ_w_pareven, subset_rhow'_pareven ρ_w_run ρ_w_pareven⟩
    · exact subset_stutequiv_w_w' ρ_w_run ρ_w_pareven
  · intro hwinlang
    rw [StutterClosure] at hwinlang
    apply Membership.mem.out at hwinlang
    obtain ⟨w', ⟨hw'inlang, ⟨wb, f, f', hwb⟩⟩⟩ := hwinlang
    rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
    obtain ⟨ρ_w', ⟨ρ_w'_run , ρ_w'_pareven⟩⟩ := hw'inlang
    let ρ_wb := supset_rhowb ρ_w' f';
    obtain ρ_wb_run := supset_rhowb_run wb f' ρ_w'_run ρ_w'_pareven hwb.2
    obtain ρ_wb_pareven := supset_rhowb_pareven w f  ρ_w'_run ρ_w'_pareven hwb.2
    use supset_rhow ρ_wb ρ_w' w f f'
    exact ⟨supset_rhow_run hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run,
          supset_rhow_pareven hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run⟩

    -- Meer BFS approach, eerst bewijs uittypen, sorrys niet zo erg maar in het midden Voor volgende week deze sorry weg
    -- In abstract eerlijk zijn
    -- 17 november eerste deadline voor hoofdstuk 5

end Automata

#eval let f : Stream' ℕ := (fun i ↦ if i = 1 then 0 else if i = 0 then 0 else if i = 2 then 2 else 0); ∑ m∈ Finset.range 5, (f m + 1)
