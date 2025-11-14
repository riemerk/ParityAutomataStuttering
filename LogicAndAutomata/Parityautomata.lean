import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc
import AutomataTheory.Sequences.Basic
import Mathlib
import Mathlib.Probability.Distributions.Fernique
import LogicAndAutomata.NPA
import LogicAndAutomata.Stuttering

-- set_option diagnostics true

-- Vragen: hoe document op te splitsen?
-- Vragen: meer swap alloceren misschien?
namespace Automata
variable {A : Type}

-- Is this implementation efficient?
-- And is this proof efficient?? (leesbaarheid verbeteren en probeer met omega en linarith)
-- En gebruik simp alleen maar simp only als tussenstap
-- Indentatie, := by maar kan ook · voor andere goals

---- Bewijs van links naar Rechts
-- Definities
def wb_struct_of_w_and_ss {M: NPA A} {w: Stream' A} {ss : Stream' (M.StutterClosed).State}
    (hss: (M.StutterClosed).InfRun w ss) (k:ℕ) : A × ℕ :=
  match k with
  | 0 =>
    if (ss (1) matches (b, Sum.inr c)) then
      (w 0, 1)
    else
      have notloopinletterstate : ∃n, (ss n) matches (b, Sum.inr c) := by sorry
      let m := Nat.find notloopinletterstate
      (w 0, m)
  | k+1 =>
    let l := (wb_struct_of_w_and_ss hss k).2
    if (ss (l+1) matches (b, Sum.inr c)) then
      (w l, l+1)
    else
      have notloopinletterstate : ∃n, ss (l+n) matches (b, Sum.inr c) := by sorry
      let m := Nat.find notloopinletterstate
      (w l, l + m)

def wb_of_wb_struct {M: NPA A} {w: Stream' A} {ss : Stream' (M.StutterClosed).State}
    (hss: (M.StutterClosed).InfRun w ss) : Stream' A
| k => (wb_struct_of_w_and_ss hss k).1

def f_of_wb_struct {M: NPA A} {w: Stream' A} {ss : Stream' (M.StutterClosed).State}
    (hss: (M.StutterClosed).InfRun w ss) : Stream' ℕ
| 0 => (wb_struct_of_w_and_ss hss 0).2 - 1
| k => (wb_struct_of_w_and_ss hss (k)).2 -  (wb_struct_of_w_and_ss hss (k-1)).2 - 1

-- ss is run op w
noncomputable def w'_struct_of_wb_struct_and_f {M : NPA A} {w: Stream' A}
                  {ss : Stream' (M.StutterClosed).State} (hss : (M.StutterClosed).InfRun w ss)
                  (f: Stream' ℕ) (k : ℕ) : ℕ × (Stream' M.State) :=
  if f k = 0 then
    have dec: Decidable ((ss (wb_struct_of_w_and_ss hss (k+1)).2).1 ∈ (M.next (ss (wb_struct_of_w_and_ss hss k).2).1 ((wb_struct_of_w_and_ss hss k).1))) := by sorry
    -- Finset.decidableMem
    if (ss (wb_struct_of_w_and_ss hss (k+1)).2).1 ∈ (M.next (ss (wb_struct_of_w_and_ss hss k).2).1 ((wb_struct_of_w_and_ss hss k).1)) then
      (0, fun k ↦ if k = 1 then (ss (wb_struct_of_w_and_ss hss (k+1)).2).1 else (ss 0 ).1)
    else
      let a := ((wb_struct_of_w_and_ss hss k).1)
      have : ∃n, ∃ ss' : Stream' M.State, (M.FinRunStart n (fun _ ↦ a) ss' (ss (wb_struct_of_w_and_ss hss k).2).1
              ∧ ss' n = (ss (wb_struct_of_w_and_ss hss (k+1)).2).1) := by sorry

      let n := this.choose
      let n_h := this.choose_spec
      let ss_fin :=  n_h.choose
      (n, ss_fin)
  else
    (0, fun k ↦if k = 1 then (ss (wb_struct_of_w_and_ss hss (k+1)).2).1 else (ss 0).1)

noncomputable def f'_of_w_struct_of_wb_struct_and_f {M : NPA A} {w: Stream' A}
                  {ss : Stream' (M.StutterClosed).State} (hss : (M.StutterClosed).InfRun w ss)
                  (f: Stream' ℕ) (k : ℕ) : ℕ :=
  (w'_struct_of_wb_struct_and_f hss f k).1

noncomputable def w'run_of_w_struct_of_wb_struct_and_f {M : NPA A} {w: Stream' A}
                  {ss : Stream' (M.StutterClosed).State} (hss : (M.StutterClosed).InfRun w ss)
                  (f: Stream' ℕ) : Stream' M.State
| 0 => (ss 0).1
| k =>
  let f' := f'_of_w_struct_of_wb_struct_and_f hss f
  let k_b : ℕ :=  Nat.find (kexists k f')
  let i := (∑ m∈ Finset.range k_b, (f' m + 1)) - k
  (w'_struct_of_wb_struct_and_f hss f k).2 i

lemma w'run_infrun {A : Type} (M : NPA A) (w : Stream' A) (ss) (ssinfrun : M.StutterClosed.InfRun w ss)
    (heven: Even (sSup ((M.StutterClosed).parityMap '' InfOcc ss))) :
      let wb := wb_of_wb_struct ssinfrun;
      let f := f_of_wb_struct ssinfrun;
      let f' := f'_of_w_struct_of_wb_struct_and_f ssinfrun f;
      M.InfRun (functiononword wb f') (w'run_of_w_struct_of_wb_struct_and_f ssinfrun f) := by

  intro wb f f'
  unfold NA.InfRun
  obtain ⟨ssinit, ssnext⟩ := ssinfrun
  constructor
  · unfold w'run_of_w_struct_of_wb_struct_and_f
    simp only
    unfold NA.init NPA.toNA NPA.StutterClosed at ssinit
    simp at ssinit
    obtain ⟨s0, hs0⟩:=ssinit
    rw [← hs0.2]
    simp only
    exact hs0.1
  · intro k

    unfold w'run_of_w_struct_of_wb_struct_and_f
    simp only
    unfold w'_struct_of_wb_struct_and_f

    simp only

    sorry


lemma w'run_inf_par_even (M : NPA A) (w : Stream' A) (ss) (ssinfrun : M.StutterClosed.InfRun w ss)
    (heven: Even (sSup ((M.StutterClosed).parityMap '' InfOcc ss))) :
      let wb := wb_of_wb_struct ssinfrun;
      let f := f_of_wb_struct ssinfrun;
      let f' := f'_of_w_struct_of_wb_struct_and_f ssinfrun f;
      Even <| sSup <| M.parityMap '' (InfOcc <| w'run_of_w_struct_of_wb_struct_and_f ssinfrun f) := by

  sorry

-- Proofs
theorem w'accepted {A : Type} (M : NPA A) (w : Stream' A) (ss) (ssinfrun : M.StutterClosed.InfRun w ss)
    (heven: Even (sSup ((M.StutterClosed).parityMap '' InfOcc ss))) :
      let wb := wb_of_wb_struct ssinfrun;
      let f := f_of_wb_struct ssinfrun;
      let f' := f'_of_w_struct_of_wb_struct_and_f ssinfrun f;
      M.ParityAccept (functiononword wb f') := by
      intro wb f f'
      unfold NPA.ParityAccept
      let ss' := w'run_of_w_struct_of_wb_struct_and_f ssinfrun f
      use ss'
      exact ⟨w'run_infrun M w ss ssinfrun heven, w'run_inf_par_even M w ss ssinfrun heven⟩

theorem stutequiv_w_w' {A : Type} (M : NPA A) (w : Stream' A) (ss) (ssinfrun : M.StutterClosed.InfRun w ss)
    (heven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ss))) :
      let wb := wb_of_wb_struct ssinfrun;
      let f := f_of_wb_struct ssinfrun;
      let f' := f'_of_w_struct_of_wb_struct_and_f ssinfrun f;
      StutterEquivalent w (functiononword wb f') := by
  intro wb f f'
  unfold StutterEquivalent
  use wb
  use f
  use f'
  simp only [and_true]
  unfold functiononword

  simp only

  sorry


-- Bewijs van rechts naar links
-- Lemma:
theorem inrange {A : Type} {M : NPA A} (q : M.State) :
  -- let q := ss (∑ m ∈ Finset.range k, (f m + 1));
  NPA.parityMap q ∈ Set.range M.parityMap := by
  simp only [Set.mem_range, exists_apply_eq_apply]

-- Definities:
-- Hier even vraag over stellen waarom gekke regel daarna niet meer werkt
noncomputable def wbrun {M: NPA A} (ss : Stream' M.State) (f: Stream' ℕ) (k:ℕ ) : (M.StutterClosed).State :=
  if k = 0 then
      (ss 0 , Sum.inr ⟨(M.parityMap (ss 0)), by simp only [Set.mem_range, exists_apply_eq_apply]⟩)
    else if f (k - 1) = 0 then
      let q : M.State := ss ((∑ m ∈ Finset.range k, (f m + 1)))
      (q, Sum.inr ⟨(M.parityMap q), by apply inrange⟩) -- hier als simp?
    else
      let start : ℕ := ∑ m ∈ Finset.range (k-1), (f m + 1)
      let maxp : ℕ := sSup (M.parityMap '' (ss '' {l | (start < l) ∧ (l ≤ (start + f (k - 1) + 1))}))
      ( ss (start + f (k - 1) + 1)
      , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ss start (f (k - 1) + 1) (by simp)) (inpfinite ss start (f (k- 1) + 1))⟩)

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

-- Setting: w = wb[f], w' = wb[f']. Dan ss is run op wb en ss' is run op w'
noncomputable def wrun_of_ss' {A: Type} (M: NPA A) (ss_b: Stream' (M.StutterClosed).State) (ss' : Stream' M.State) (w : Stream' A) (f f': Stream' ℕ) (k: ℕ) : (M.StutterClosed).State :=
if k = 0 then
   ss_b 0
else
  let k_b : ℕ :=  Nat.find (kexists k f)
  if fkb_zero : f k_b = 0 then
    ss_b (k_b + 1)
  else
    let i := ∑ m∈ Finset.range (k_b), (f m + 1) - k + 1
    have dec: Decidable (((ss_b (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (wrun_of_ss' M ss_b ss' w f f' (k - 1)) (w k))) := by sorry
    if ((ss_b (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (wrun_of_ss' M ss_b ss' w f f' (k - 1)) (w k)) then
      if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
        ((ss_b (k_b + 1)).1, Sum.inr ⟨M.parityMap (ss_b (k_b + 1)).1, by simp only [Set.mem_range,
          exists_apply_eq_apply]⟩)
      else
        ((ss_b (k_b + 1)).1, Sum.inl (w k))
    else
      if hdiff1: f k_b ≤ f' k_b then
        if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
          if hdiff2: f k_b = f' k_b then
            (ss' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1), Sum.inr ⟨M.parityMap (ss' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1)), by simp⟩)
          else
            let start := i + ∑ m∈ Finset.range (k_b), (f' m + 1)
            let diff := f' k_b - f k_b
            let maxp : ℕ := sSup (M.parityMap '' (ss' '' {l | (start < l) ∧ (l ≤ (start + diff))}))
            ((ss' (start + diff))
            , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ss' start diff (by omega)) (inpfinite  ss' start diff)⟩)
        else
          (ss' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ss' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
      else
        if i <= f' k_b then
          (ss' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ss' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
        else
          if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
            ((ss_b (k_b + 1)).1, Sum.inr ⟨M.parityMap (ss_b (k_b + 1)).1, by simp only [Set.mem_range,
              exists_apply_eq_apply]⟩)
          else
            ((ss_b (k_b + 1)).1, Sum.inl (w k))

-- Lemmas voor wb accepted
lemma sumcorrect_of_wbrun {A : Type} (M : NPA A) (f' : Stream' ℕ):
  ∀ (ss : Stream' (NA.State A)),
    Even (sSup (NPA.parityMap '' InfOcc ss)) →
          ∀ (k : ℕ), (wbrun ss f' k).1 = ss (∑ m ∈ Finset.range k, (f' m + 1)) := by
  intro Ms ss k
  cases' k with n
  · unfold wbrun
    simp only [↓reduceIte, Finset.range_zero, Finset.sum_empty]
  · simp only [wbrun, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1]
    else
      simp only [↓reduceIte, h1]
      apply congrArg
      rw [Finset.sum_range_succ, add_assoc]

lemma ss'numstate_of_wbrun {A : Type} {M : NPA A} (f' : Stream' ℕ) (ss : Stream' (NA.State A)) (k : ℕ) :
                           let ss' := wbrun ss f'; (ss' k).1 = ss (∑ m ∈ Finset.range k, (f' m + 1)) →
                           ∃ p, (ss' k).2 = Sum.inr p := by
  intro ss' hk
  cases' k with n
  · unfold ss' wbrun
    simp only [↓reduceIte, Sum.inr.injEq, exists_eq']
  · unfold ss' wbrun
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

open Classical in
lemma wbrun_same_sup_as_ss {A : Type} {M : NPA A} {w w' wb : Stream' A}
  {f f' : Stream' ℕ} (hwb : w = functiononword wb f ∧ w' = functiononword wb f')
  (ss : Stream' (M.State))
    (heven: Even (sSup (M.parityMap '' InfOcc ss)))
      (ssinit: ss 0 ∈ M.init)
        (ssnext : (∀ (k : ℕ), ss (k + 1) ∈ M.next (ss k) (w' k))) :
          sSup (M.parityMap '' InfOcc ss) + 2 = sSup ((M.StutterClosed).parityMap '' InfOcc (wbrun ss f')) := by
  let Ms := (M.StutterClosed)
  let ss' := (wbrun ss f')
  let s := (sSup (M.parityMap '' InfOcc ss))
  have hMs : ∃ n, (∀ a ∈ (Ms.parityMap '' InfOcc ss'), a ≤ n) :=
    par_map_inf_occ_of_ss_has_sup Ms ss'

  rw [Nat.sSup_def hMs]
  have hM : ∃ n, (∀ a ∈ (M.parityMap '' InfOcc ss), a ≤ n) :=
    par_map_inf_occ_of_ss_has_sup M ss

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

  -- have := @Nat.find_congr' (fun n↦  (∀ a ∈ (M.parityMap '' InfOcc ss), a ≤ n)) (fun n ↦ (∀ a ∈ (Ms.parityMap '' InfOcc ss'), a ≤ n))
  --   _ _ hM hMs
  -- apply this
  -- intro n
  -- constructor
  -- · by_contra hneg
  --   simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
  --     Classical.not_imp, not_forall, not_le] at hneg
  --   obtain ⟨forallbiggerss, ⟨x, ⟨hxinfocc, hxparbigger⟩⟩⟩ := hneg

  --   match x with
  --   | (s, Sum.inr p) =>
  --     if hp: p = ⟨(M.parityMap s), by simp⟩ then
  --       have sinfocc: s∈ InfOcc ss := by sorry
  --       unfold NPA.parityMap at hxparbigger
  --       unfold Ms at hxparbigger
  --       unfold NPA.StutterClosed at hxparbigger

  --       simp [bind_pure_comp] at hxparbigger

  --       unfold Sum.elim at hxparbigger
  --       simp only at hxparbigger


  --       sorry
  --     else
  --       sorry
  --   | (s, Sum.inlₗ k) =>  sorry


  --   -- rcases x with ⟨(s, Sum.inrₗ ⟨ M.parityMap s, by simp ⟩), (s, Sum.inlₗ k), (s, Sum.inrₗ p)⟩


  --   -- unfold InfOcc at hxinfocc
  --   -- unfold ss' at hxinfocc
  --   -- unfold wbrun at hxinfocc
  --   -- rw [Set.mem_setOf] at hxinfocc
  --   -- rw [Filter.frequently_atTop] at hxinfocc
  --   -- simp at hxinfocc
  --   -- -- simp at hxinfocc

  --   -- sorry
  -- · sorry
  -- by_contra hneg
  -- simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hneg


  -- sorry

-- Theorem wb accepted
theorem wbaccepted_of_specific_stutterequivalent {A : Type} (M : NPA A) (w w' : Stream' A) (wb : Stream' A) (f f' : Stream' ℕ):
    w' ∈ M.AcceptedOmegaLang →
        w = functiononword wb f ∧ w' = functiononword wb f' → wb ∈ M.StutterClosed.AcceptedOmegaLang := by
  intro hw'inlang hwb
  let Ms := M.StutterClosed
  rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
  obtain ⟨ss, ⟨⟨ssinit, ssnext⟩ , sspareven⟩ ⟩ := hw'inlang
  let ss' := wbrun ss f'
  use ss'
  rw [NA.InfRun]
  refine ⟨⟨Set.mem_setOf.2 ⟨ss 0, ssinit, rfl⟩, ?_⟩, ?_⟩
  · intro k
    have ss'numstate : ∃ p : ↑(Set.range M.parityMap) , (ss' k).snd = Sum.inr p :=
      ss'numstate_of_wbrun f' ss k (sumcorrect_of_wbrun M f' ss sspareven k)

    conv =>
      rhs
      simp only [ss', wbrun]
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one]
    if h1 : (f' k) = 0  then
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ss' k), (sumcorrect_of_wbrun M f' ss (sspareven))]
      rcases ss'numstate with ⟨p, hp⟩
      rw [hp, Finset.sum_range_succ, h1, zero_add]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      refine Or.inl (Or.inl ?_)
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, existsAndEq,
        and_self, and_true]
      rw [← functiononword_eq_base_word (b:=0) hwb.2 k (by linarith), zero_add]
      exact ssnext (∑ m ∈ Finset.range k, (f' m + 1))

    else
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ss' k), (sumcorrect_of_wbrun M f' ss sspareven)]
      rcases ss'numstate with ⟨p, hp⟩
      rw [hp]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      right
      nth_rewrite 1 [add_assoc]
      apply Set.mem_setOf.2
      use (f' k + 1)
      use Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ss
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
      · unfold NA.FinRunStart
        refine ⟨?_, ?_⟩
        · unfold Stream'.drop Stream'.get
          simp only [zero_add]
        · intro b hb
          unfold Stream'.drop Stream'.get
          simp only
          rw [← functiononword_eq_base_word hwb.2 k hb, add_right_comm]
          exact ssnext  (b + ∑ m ∈ Finset.range k, (f' m + 1))
      · simp only [gt_iff_lt, Sum.inr.injEq, Subtype.mk.injEq]
        constructor
        · exact congrArg sSup (congrArg (Set.image M.parityMap) (inpsame_of_specific M f' ss k))
        · exact Eq.symm Stream'.get_drop'
  · rw [← wbrun_same_sup_as_ss hwb ss sspareven ssinit ssnext]
    exact Even.add sspareven even_two


-- Lemmas for waccepted
lemma wrun_of_ss'_infrun {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ} {ssb : Stream' (M.StutterClosed).State}
  {ss' : Stream' M.State} (hw : w = functiononword wb f) (f' : Stream' ℕ)
  (ssbpareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ssb))) (ssbrun : M.StutterClosed.InfRun wb ssb)
  (ss'pareven : Even (sSup (M.parityMap '' InfOcc ss'))) (ss'run : M.InfRun w' ss') : M.StutterClosed.InfRun w (wrun_of_ss' M ssb ss' w f f') := by
  unfold NA.InfRun
  constructor
  obtain ⟨ssbinit, ssbnext⟩ := ssbrun
  · unfold wrun_of_ss'
    simp only [↓reduceIte]
    exact ssbinit
  · intro k

    unfold wrun_of_ss'

    cases k
    ·
      -- zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]



      -- , zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]

      sorry
    · sorry



lemma wrun_of_ss'_infpareven {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ} {ssb : Stream' (M.StutterClosed).State}
  {ss' : Stream' M.State} (hw : w = functiononword wb f) (f' : Stream' ℕ)
  (ssbpareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ssb))) (ssbrun : M.StutterClosed.InfRun wb ssb)
  (ss'pareven : Even (sSup (M.parityMap '' InfOcc ss'))) (ss'run : M.InfRun w' ss')  :
    Even (sSup ((M.StutterClosed).parityMap '' InfOcc (wrun_of_ss' M ssb ss' w f f'))) := by sorry



theorem w_accepted {A : Type} {w wb w': Stream' A} {M : NPA A} {f: Stream' ℕ}
                   (hw': w' ∈ M.AcceptedOmegaLang) (hw: w = functiononword wb f) (f': Stream' ℕ)
                  (hwb: wb ∈ (M.StutterClosed).AcceptedOmegaLang) :
        w ∈ M.StutterClosed.AcceptedOmegaLang := by
  rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hwb ⊢
  obtain ⟨ssb, ⟨ssbrun , ssbpareven⟩ ⟩ := hwb
  obtain ⟨ss', ⟨ss'run , ss'pareven⟩ ⟩ := hw'

  let Ms := M.StutterClosed
  use wrun_of_ss' M ssb ss' w f f'
  exact ⟨wrun_of_ss'_infrun hw f' ssbpareven ssbrun ss'pareven ss'run, wrun_of_ss'_infpareven hw f' ssbpareven ssbrun ss'pareven ss'run⟩

-- Full theorem
theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
  let Ms : NPA A := M.StutterClosed
  ext w
  constructor
  · intro h
    rw [NPA.AcceptedOmegaLang] at h ⊢
    rw [Set.mem_setOf, NPA.ParityAccept] at h
    rw [StutterClosure, Set.mem_setOf]
    obtain ⟨ss, ⟨ssinfrun, sspareven⟩⟩ := h
    let wb := wb_of_wb_struct ssinfrun
    let f := f_of_wb_struct ssinfrun
    let f' := f'_of_w_struct_of_wb_struct_and_f ssinfrun f
    use (functiononword wb f')
    rw [Set.mem_setOf]
    exact ⟨w'accepted M w ss ssinfrun sspareven, stutequiv_w_w' M w ss ssinfrun sspareven⟩
  · intro h
    rw [StutterClosure] at h
    apply Membership.mem.out at h
    obtain ⟨w', ⟨hw'inlang, ⟨wb, f, f', hwb⟩⟩⟩ := h

    -- Meer BFS approach, eerst bewijs uittypen, sorrys niet zo erg maar in het midden Voor volgende week deze sorry weg
    -- In abstract eerlijk zijn
    -- 17 november eerste deadline voor hoofdstuk 5

    exact w_accepted hw'inlang hwb.1 f'
      (wbaccepted_of_specific_stutterequivalent M w w' wb f f' hw'inlang hwb)



#eval let f : Stream' ℕ := (fun i ↦ if i = 1 then 0 else if i = 0 then 0 else if i = 2 then 2 else 0); ∑ m∈ Finset.range 5, (f m + 1)
