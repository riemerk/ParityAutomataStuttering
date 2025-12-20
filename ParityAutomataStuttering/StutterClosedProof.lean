import ParityAutomataStuttering.ParityAutomata
import ParityAutomataStuttering.Stuttering

namespace Automata
variable {Alph : Type}

theorem infOcc_comp_of_Finite {α β : Type*} {f : α → β}
    (hfin : Finite α) (xs : Stream' α) : InfOcc (f ∘ xs) = f '' InfOcc xs := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨k, -, rfl⟩ := hx.exists
    simp only [InfOcc, Function.comp_apply, Set.mem_image, Set.mem_setOf_eq,
              Nat.frequently_atTop_iff_infinite] at hx ⊢
    have union : Set.iUnion (fun (x : α) ↦ { n | xs n = x ∧ (f x = f (xs k))}) =
      { n | (f ∘ xs) n = (f ∘ xs) k} := by aesop
    have existsNotFinite : ∃ (x: α), ¬ { n | xs n = x ∧ (f x = f (xs k))}.Finite := by
      by_contra hfin
      simp [not_not] at hfin
      have unionfin: (Set.iUnion (fun (x : α) ↦ { n | xs n = x ∧ (f x = f (xs k))})).Finite :=
        Set.finite_iUnion hfin
      rw [union] at unionfin
      exact hx unionfin
    rcases existsNotFinite with ⟨x, hx⟩
    use x
    let q := Nat.nth (fun n ↦ (xs n = x ∧ (f x = f (xs k)))) 0
    have qtrue : (xs q = x ∧ (f x = f (xs k))) := by
      simpa using (Nat.nth_mem_of_infinite hx 0)
    aesop
  · rw [Set.image_subset_iff]
    intro x hx
    simp only [InfOcc, Function.comp_apply, Set.preimage_setOf_eq, Set.mem_setOf,
               Filter.frequently_atTop] at hx ⊢
    intro a
    specialize hx a
    rcases hx with ⟨b, hbge, hbomega⟩
    use b
    apply congr_arg f at hbomega
    exact ⟨hbge, hbomega⟩

/-! ### Proof subset (left to right) -/
/-! #### Definitions -/
open scoped BigOperators in
open Classical in
/-- Definition 4.2.1 -/
noncomputable def subset_wb_f_pair {A : NPA Alph} (w : Stream' Alph)
    {ρ_w : Stream' (A.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' (Alph × ℕ)
| i =>
  let l2 := ∑ m : Fin i, ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)
  have notloopinletterstate : ∃ n>0, ¬(∃q, ρ_w (l2+n) = (q, Sum.inl (w l2))) := by
    by_contra h
    simp only [gt_iff_lt, not_exists, not_and, not_forall, Decidable.not_not] at h
    have infocceqone : InfOcc ((A.StutterClosed).parityMap ∘ ρ_w) = {1} := by
      rw [InfOcc]
      have infoccnonemp : (InfOcc ((A.StutterClosed).parityMap ∘ ρ_w)).Nonempty := by
        rw [infOcc_comp_of_Finite (A.StutterClosed).FinState ρ_w, Set.image_nonempty]
        have inf_event := @inf_occ_eventually (A.StutterClosed).State (A.StutterClosed).FinState ρ_w
        rw [Filter.eventually_atTop] at inf_event
        rcases inf_event with ⟨k, hk⟩
        specialize hk k
        simp only [ge_iff_le, le_refl, forall_const] at hk
        exact Set.nonempty_of_mem hk
      rw [InfOcc] at infoccnonemp
      rw [← Set.Nonempty.subset_singleton_iff infoccnonemp, Set.subset_singleton_iff]
      by_contra h2
      simp only [Set.mem_setOf_eq, not_forall] at h2
      rcases h2 with ⟨x, ⟨hx1, hx2⟩⟩
      rw [Filter.frequently_atTop] at hx1
      specialize hx1 (l2 + 1)
      rcases hx1 with ⟨xge, ⟨hxge1, hxge2⟩⟩
      specialize h (xge - l2)
      simp only [tsub_pos_iff_lt] at h
      have hxgt : xge ≥ l2 := by omega
      apply Nat.lt_of_succ_le at hxge1
      apply h at hxge1
      rcases hxge1 with ⟨q, hxge⟩
      rw [Nat.add_sub_of_le hxgt] at hxge
      have parmapeqone : (A.StutterClosed).parityMap (ρ_w xge) = 1 := by
        rw [hxge, NPA.parityMap]
        unfold NPA.StutterClosed
        simp only [Sum.elim_inl]
      rw [← hxge2] at hx2
      exact hx2 parmapeqone
    rw [infOcc_comp_of_Finite (A.StutterClosed).FinState ρ_w] at infocceqone
    have ssupone : sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w) = 1 := by
      simp only [infocceqone, csSup_singleton]
    have ssupodd : Odd (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)) := by simp only [ssupone,
      odd_one]
    rw [← Nat.not_even_iff_odd] at ssupodd
    exact ssupodd ρ_w_pareven
  let k := Nat.find notloopinletterstate
  (w l2, k - 1)

noncomputable def subset_wb {A : NPA Alph} (w : Stream' Alph)
    {ρ_w : Stream' (A.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' Alph
| i => (subset_wb_f_pair w ρ_w_pareven i).1

noncomputable def subset_f {A : NPA Alph} (w : Stream' Alph) {ρ_w : Stream' (A.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' ℕ
| i => (subset_wb_f_pair w ρ_w_pareven i).2


open Classical in
/-- Claim 4.2.2 -/
lemma subset_w_eq_functiononword {A : NPA Alph} {w : Stream' Alph} {f : Stream' ℕ}
        {ρ_w : Stream' (A.StutterClosed).State} (ρ_w_run : A.StutterClosed.InfRun w ρ_w)
        (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
        (hf : f = subset_f w ρ_w_pareven) :
        w = functiononword (subset_wb w ρ_w_pareven) f := by
  unfold functiononword
  apply funext
  intro x
  unfold subset_wb subset_wb_f_pair
  simp only
  cases x
  case zero =>
    have hi_b : Nat.find (kexists 0 f) = 0 := by
      simp only [Nat.find_eq_zero, n_lt_sumk, zero_add, Finset.range_one, Finset.sum_singleton,
        lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
    rw [hi_b]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
  case succ n =>
    if hi_b : (Nat.find (kexists (n+1) f)) = 0 then
      unfold subset_wb_f_pair
      have hi_b2 := hi_b
      rw [Nat.find_eq_zero, n_lt_sumk, zero_add, Finset.range_one, Finset.sum_singleton, hf] at hi_b
      unfold subset_f subset_wb_f_pair at hi_b
      simp only [gt_iff_lt, Finset.univ_eq_empty, Finset.sum_empty, zero_add, not_exists,
        Nat.le_find_iff, Nat.lt_one_iff, not_and, not_forall, not_not, forall_eq, lt_self_iff_false,
        IsEmpty.forall_iff, Nat.sub_add_cancel, Nat.lt_find_iff] at hi_b
      rw [hi_b2, Finset.univ_eq_empty, Finset.sum_empty]
      specialize hi_b (n+1)
      simp only [le_refl, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        forall_const] at hi_b
      have ρ_w_next_spec : ρ_w (n+2) ∈ (A.StutterClosed).next (ρ_w (n + 1)) (w (n + 1)) :=
        ρ_w_run.2 (n+1)
      unfold NA.next NPA.StutterClosed at ρ_w_next_spec
      simp only at ρ_w_next_spec
      rcases hi_b with ⟨q, hq⟩
      simp only [hq, decide_eq_true_eq, Set.mem_ite_empty_right, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ρ_w_next_spec
      -- En hier staat precies het tweede gedeelte wat je wil hebben jippie :)
      apply Eq.symm (ρ_w_next_spec.1)
    else
      apply Nat.pos_of_ne_zero at hi_b
      rw [← Nat.add_one_le_iff] at hi_b
      have hi_b2 := hi_b
      apply Nat.le.dest at hi_b
      rcases hi_b with ⟨k, hk⟩
      rw [← hk]
      have hk := hk.symm
      rename_i hk2
      clear hk2
      rw [Nat.find_eq_iff] at hk
      rcases hk with ⟨k_spec, k_big⟩
      unfold n_lt_sumk at k_spec
      rw [Finset.sum_range_succ] at k_spec
      nth_rewrite 2 [hf] at k_spec
      unfold subset_f subset_wb_f_pair at k_spec
      simp only [gt_iff_lt, not_exists, Nat.le_find_iff, Nat.lt_one_iff, not_and, not_forall,
        not_not, forall_eq, lt_self_iff_false, add_zero, IsEmpty.forall_iff,
        Nat.sub_add_cancel] at k_spec
      unfold n_lt_sumk at k_big
      simp only [zero_add, not_lt] at k_big
      specialize k_big k
      simp only [lt_add_iff_pos_left, zero_lt_one, forall_const] at k_big
      have k_spec2 := k_spec
      rw [add_comm] at k_big
      rw [← Nat.sub_lt_iff_lt_add' k_big] at k_spec2
      apply Nat.le.dest at k_spec2
      rcases k_spec2 with ⟨k2, hk2⟩
      have hk3 := hk2.symm
      rw [Nat.find_eq_iff] at hk3
      rcases hk3 with ⟨k2_spec, k2_big⟩
      simp only [Nat.succ_eq_add_one, add_pos_iff, tsub_pos_iff_lt, zero_lt_one, or_true, true_or,
        true_and] at k2_spec
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, not_and, not_forall,
        Decidable.not_not, hk2] at k2_big
      if heq: n+1 = ∑ m ∈ Finset.range (k+1), (f m + 1) then
        rw [heq, zero_add, add_comm 1 k, Fin.sum_univ_eq_sum_range
          (fun n ↦ ((subset_wb_f_pair w ρ_w_pareven n).2 + 1)) (k+1), hf]
        exact rfl
      else
        specialize k2_big (n+1 - ∑ m ∈ Finset.range (1+k), (f m + 1))
        rw [← Nat.sub_lt_iff_lt_add' k_big] at k_spec
        apply k2_big at k_spec
        rw [add_comm] at k_big
        rw [← ne_eq] at heq
        have hge : n+1 > ∑ m ∈ Finset.range (k+1), (f m + 1) :=
          Nat.lt_iff_le_and_ne.mpr ⟨k_big, heq.symm⟩
        apply GT.gt.lt at hge
        rw [← Nat.sub_lt_sub_iff_right (c:=∑ m ∈ Finset.range (k+1), (f m + 1)) (by simp),
          tsub_self] at hge
        rw [add_comm 1 k] at k_spec
        apply k_spec at hge
        rcases hge with ⟨x, hx⟩
        rw [hf] at hx
        unfold subset_f at hx
        simp only at hx
        nth_rewrite 1 [Fin.sum_univ_eq_sum_range
            (fun n ↦ ((subset_wb_f_pair w ρ_w_pareven n).2 + 1)) (k+1)] at hx
        have k_big2 := k_big
        rw [hf] at k_big2
        unfold subset_f at k_big2
        simp only at k_big2
        rw [Nat.add_sub_cancel' k_big2] at hx
        have ρ_w_next_spec : ρ_w (n+2) ∈ (A.StutterClosed).next (ρ_w (n + 1)) (w (n + 1)) :=
          ρ_w_run.2 (n+1)
        unfold NA.next NPA.toNA NPA.StutterClosed at ρ_w_next_spec
        rw [hx] at ρ_w_next_spec
        simp only [decide_eq_true_eq, gt_iff_lt, ge_iff_le, exists_and_left, exists_and_right,
          Set.mem_ite_empty_right, Set.mem_insert_iff, Set.mem_singleton_iff] at ρ_w_next_spec
        simp only [Nat.reduceAdd] at k2_spec
        -- Hier weer tweede in de and gebruiken strakjes
        rw [zero_add, add_comm 1 k]
        apply Eq.symm (ρ_w_next_spec.1)

open Classical in
set_option pp.proofs true in
/- Definition 4.2.3 -/
noncomputable def subset_f'_rhow'_pair {A : NPA Alph} {w : Stream' Alph} {f : Stream' ℕ}
    {ρ_w : Stream' (A.StutterClosed).State} (ρ_w_run : (A.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) : Stream' (ℕ × (Stream' A.State))
| i =>
  if hfzero : f i = 0 then

    let a := subset_wb w ρ_w_pareven i -- ((subset_wb_f_pair w ρ_w_pareven i).1)
    -- let s := ∑ m : Fin i, ((subset_f w ρ_w_pareven m) + 1)
    -- let e := ∑ m : Fin i, ((subset_f w ρ_w_pareven m) + 1) + (f i + 1)
    let s := ∑ m : Fin i, (f m + 1)
    let e := ∑ m : Fin i, (f m + 1) + (f i + 1)
    -- ∑ m : Fin (i+1), ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)
    have existspartialrun : ∃ n, ∃ ρ : Stream' A.State, ∃ n_ge : n ≥1,
                (A.FinRunStart n (fun _ ↦ a) ρ (ρ_w s).1
                ∧  ((ρ_w e).2 = (Sum.inr ⟨sSup (A.parityMap '' (ρ '' {l| (l > 0) ∧ (l ≤ n)})),
                      ssupinrange (by rw [← zero_add n] ; exact (inpnonemp ρ 0 n n_ge))
                      (by rw [← zero_add n]; exact inpfinite ρ 0 n)⟩))
                ∧ ρ n = (ρ_w e).1) := by
      have ρ_w_run2 := ρ_w_run
      have hf2 := hf
      rcases ρ_w_run2 with ⟨ρ_w_init, ρ_w_next⟩
      specialize ρ_w_next s
      have hs : s = ∑ m : Fin i, (f m + 1) := rfl
      have he : e = ∑ m : Fin i, (f m + 1) + (f i + 1) := rfl
      rw [hfzero] at he
      simp only [zero_add] at he
      have he2 := he
      rw [hf] at he2
      unfold subset_f at he2
      simp only at he2
      rw [he]
      rw [hs, ← he, NA.next] at ρ_w_next
      unfold NPA.StutterClosed at ρ_w_next
      simp only at ρ_w_next
      -- Zeggen dat het een num state is want anders niet 0
      -- Dit bewijs is nog belangrijk
      have sumpointnumstate : ∃ q, ∃ n, ρ_w (∑ m : Fin i, (f ↑m + 1)) = (q, Sum.inr n) := by

        sorry
      rcases sumpointnumstate with ⟨q, ⟨n, h⟩⟩
      rw [h] at ρ_w_next
      simp only at ρ_w_next
      unfold subset_f subset_wb_f_pair at hf
      simp only at hf
      have hfzero2 := hfzero
      rw [hf] at hfzero2
      simp only at hfzero2
      apply Nat.eq_add_of_sub_eq (by sorry) at hfzero2
      rw [zero_add] at hfzero2
      rw [Nat.find_eq_iff (by sorry)] at hfzero2

      rcases hfzero2.1 with ⟨-, hq⟩
      rw! [← he2] at hq
      simp only [Set.mem_union, Set.mem_setOf_eq] at ρ_w_next
      cases ρ_w_next
      case inl hloop =>
        by_contra
        rcases hloop with ⟨q2, hq2⟩
        have hqcontra : ∃ q, (ρ_w e) = (q, Sum.inl (w (∑ m : Fin i, (f ↑m + 1)))) := by
          use q2
          exact Eq.symm hq2.2
        rw [hf2] at hqcontra
        exact hq hqcontra
      case inr hnum =>
        rcases hnum with ⟨n, ⟨ρfin, ⟨hn, hfinrunstart⟩⟩⟩
        use n, ρfin, hn
        rw! [he] at hfinrunstart
        have ha : a = subset_wb w ρ_w_pareven i := by rfl
        have w_wb := subset_w_eq_functiononword ρ_w_run ρ_w_pareven hf2
        have wword := functiononword_eq_base_word w_wb i (b:=0) (by omega)
        rw [zero_add] at wword
        rw [Finset.sum_range] at wword
        rw [wword, ← ha] at hfinrunstart
        rw [← hs] at h
        rw [Prod.eq_iff_fst_eq_snd_eq] at h
        simp only at h
        rw [← h.1] at hfinrunstart
        refine ⟨hfinrunstart.1, ⟨hfinrunstart.2.1, by apply Eq.symm hfinrunstart.2.2⟩⟩
    let n := existspartialrun.choose
    have hn := existspartialrun.choose_spec
    let ρ_fin :=  hn.choose
    -- have hss := n_h.choose_spec
    (n - 1, ρ_fin)
  else
    (0, fun k↦ if k = 1 then (ρ_w (∑ m ∈ Finset.range (i + 1), (f m + 1))).1 else (ρ_w 0).1)

noncomputable def subset_f' {A : NPA Alph} {w : Stream' Alph} {f : Stream' ℕ}
    {ρ_w : Stream' (A.StutterClosed).State} (ρ_w_run : (A.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) : Stream' ℕ
| i => (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven hf i).1

noncomputable def subset_rhow' {A : NPA Alph} {w : Stream' Alph} {f : Stream' ℕ}
    {ρ_w : Stream' (A.StutterClosed).State} (ρ_w_run : (A.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) : Stream' A.State
| i =>
  let f' := subset_f' ρ_w_run ρ_w_pareven hf
  let i_b : ℕ :=  Nat.find (kexists (i - 1) f')
  let j := i - (∑ m ∈ Finset.range i_b, (f' m + 1))
  (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven hf i_b).2 j


-- Dit bewijs is nog niet af
-- Deze is moeilijk met Malvin samen doen
set_option pp.proofs true in
-- This proof is not finished yet
/-- Claim 4.2.4 -/
lemma subset_rhow'_run {A : NPA Alph} {w wb : Stream' Alph} {f f' : Stream' ℕ}
    {ρ_w : Stream' (A.StutterClosed).State} (ρ_w_run : A.StutterClosed.InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hwb : wb = subset_wb w ρ_w_pareven) (hf : f = subset_f w ρ_w_pareven)
    (hf' : f' = subset_f' ρ_w_run ρ_w_pareven hf) :
    A.InfRun (functiononword wb f') (subset_rhow' ρ_w_run ρ_w_pareven hf) := by
  unfold NA.InfRun
  constructor
  · unfold subset_rhow' subset_f'_rhow'_pair
    simp only
    split
    case isTrue hf0zero =>
      let h1 := subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven hf (Nat.find
          (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf 0)) (Eq.mpr_prop (Eq.refl
          (f (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf 0)) = 0)) hf0zero)
      -- let h1 := subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven
      --   (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf 0)) (Eq.mpr_prop (Eq.refl
      --   (f (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf 0)) = 0)) hf0zero)
      let n := h1.choose
      have hn : n = h1.choose := by rfl
      let h2 := h1.choose_spec
      let ρ_fin := h2.choose
      have hρfin : ρ_fin = h2.choose := by rfl
      obtain ⟨-, ⟨hinit, -⟩, -, -⟩ := h2.choose_spec
      rw! [←hn, ← hρfin] at hinit ⊢
      simp only [zero_tsub]
      have mzero : (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf 0)) = 0 := by
        rw [Nat.find_eq_zero]
        unfold n_lt_sumk
        simp
      rw [mzero] at hinit
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hinit
      rw [hinit]
      unfold NA.InfRun NA.init at ρ_w_run
      rcases ρ_w_run with ⟨ρ_w_init, -⟩
      unfold NPA.StutterClosed at ρ_w_init
      simp only [Set.mem_setOf_eq] at ρ_w_init
      rcases ρ_w_init with ⟨s, hsinit, hsρw0⟩
      rw [Prod.eq_iff_fst_eq_snd_eq] at hsρw0
      rw [← hsρw0.1]
      simpa only using hsinit
    case isFalse hf0nonzero =>
      simp only [zero_tsub, zero_ne_one, ↓reduceIte]
      rcases ρ_w_run with ⟨ρ_w_init, ρ_w_next⟩
      simp only [NA.init, NPA.StutterClosed, Set.mem_setOf_eq] at ρ_w_init
      rcases ρ_w_init with ⟨s, ⟨hsinit, hs⟩⟩
      simp [Prod.eq_iff_fst_eq_snd_eq] at hs
      rw [← hs.1]
      exact hsinit
  · intro i
    let i_b := Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1))
    have hib : i_b = Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1)) := rfl
    conv =>
      rhs
      unfold subset_rhow' subset_f'_rhow'_pair
    simp only
    let j := (i + 1 - ∑ m ∈ Finset.range i_b, (subset_f' ρ_w_run ρ_w_pareven hf m + 1))
    let hj : j = (i + 1 - ∑ m ∈ Finset.range i_b, (subset_f' ρ_w_run ρ_w_pareven hf m + 1)) := rfl
    rw [← hj]
    -- follows from ibbigger
    have jgezero : j > 0 := by sorry
    have hibnatfind := hib
    rw [Nat.find_eq_iff] at hibnatfind
    rcases hibnatfind with ⟨ibspec, ibbigger⟩
    unfold n_lt_sumk at ibspec
    rw [Finset.sum_range_succ] at ibspec
    rw [← hib] at ibspec
    simp only [add_tsub_cancel_right] at ibspec

    split
    case isTrue hfzero =>
      let h1 := subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven hf
          (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1))) (Eq.mpr_prop (Eq.refl
          (f (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1))) = 0)) hfzero)
      -- let h1 := subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven (Nat.find
      --   (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1))) (Eq.mpr_prop (Eq.refl
      --   (f (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (i + 1))) = 0)) hfzero)
      let n := h1.choose
      have hn : n = h1.choose := by rfl
      let h2 := h1.choose_spec
      let ρ_fin := h2.choose
      have hρfin : ρ_fin = h2.choose := by rfl
      obtain ⟨hn_ge, hfinrunstart, -, hend⟩:= h2.choose_spec
      rw! [←hn, ← hρfin] at hfinrunstart hend ⊢
      rw! [← hn] at hn_ge
      simp only
      rw! [← hib] at hfzero
      -- By unfolding the definition of subset_rhow', also if j=1 then by definition of ρ_fin the
      -- start is the previous. Otherwise it is just the same
      have subset_rhow'_eq_ρfin : (subset_rhow' ρ_w_run ρ_w_pareven hf i) = ρ_fin (j-1) := by sorry
      rw [subset_rhow'_eq_ρfin]
      rcases hfinrunstart with ⟨ρfinstart,ρfinnext⟩
      specialize ρfinnext (j-1)
      -- Since in ibspec we see f' i_b = n
      have j_lt_n : j-1 < n := by sorry
      apply ρfinnext at j_lt_n
      rw [Nat.sub_add_cancel (n:=j) (jgezero)] at j_lt_n
      unfold subset_wb subset_wb_f_pair at j_lt_n
      simp only at j_lt_n
      unfold functiononword
      rw! [Nat.add_sub_cancel (n:=i)] at j_lt_n hib
      rw! [← hib] at j_lt_n
      -- By rewriting some terms and applying functiononword_eq_base_word
      -- rw [← subset_w_eq_functiononword _ _ _] at j_lt_n
      have letterseq : (w (∑ m : Fin i_b, ((subset_wb_f_pair w ρ_w_pareven ↑m).2 + 1)))
        = wb (Nat.find (kexists i f')) := by sorry
      rw [letterseq] at j_lt_n
      exact j_lt_n
    case isFalse hfnonzero =>
      have jeqone : j = 1 := by sorry
      apply Nat.pos_of_ne_zero at hfnonzero
      apply Nat.succ_le_of_lt at hfnonzero
      rw [Nat.succ_eq_add_one, zero_add] at hfnonzero
      rw [jeqone]
      simp only [↓reduceIte]
      rw! [Nat.add_sub_cancel (n:=i), ← hib]
      -- This follows by unfolding subset_rhow' and performing case distinction
      have preveq : (subset_rhow' ρ_w_run ρ_w_pareven hf i) =
        (ρ_w ( ∑ m∈ Finset.range (i_b), (f m + 1))).1 := by sorry
      rw [preveq]
      -- Now the proof follows from the fact that f i_b > 0 so that means that the loop state is
      -- in it so then also the normal state
      sorry

/-- #### Lemmas for claim 4.2.5 -/
lemma infoccnonemp {A : NPA Alph} {ρ : Stream' A.State} : (InfOcc ρ).Nonempty := by
  unfold InfOcc
  rw [Set.nonempty_def]
  by_contra hneg
  apply forall_not_of_not_exists at hneg
  have forallxfinite : ∀ (x: A.State), (¬{ k:ℕ | ρ k = x}.Infinite) := by
    intro x
    have xnotinfilter : x∉ {x | ∃ᶠ (k : ℕ) in Filter.atTop, ρ k = x} := hneg x
    apply Set.notMem_setOf_iff.1 at xnotinfilter
    contrapose! xnotinfilter
    exact Nat.frequently_atTop_iff_infinite.2 xnotinfilter
  have union : Set.iUnion (fun (x : A.State)↦ { k:ℕ | ρ k = x}) = Set.univ := by
    rw [Set.iUnion_eq_univ_iff]
    intro k
    use ρ k
    simp only [Set.mem_setOf_eq]
  simp only [Set.not_infinite] at forallxfinite
  have unionfinite: (⋃ x, {k | ρ k = x}).Finite := @Set.finite_iUnion _ _ A.FinState _ forallxfinite
  rw [union] at unionfinite
  exact Set.infinite_univ unionfinite

lemma par_map_inf_occ_of_ss_has_sup (A : NPA Alph) (ss' : Stream' A.State) :
    ∃ n, ∀ m ∈ NPA.parityMap '' InfOcc ss', m ≤ n := by
  have htest : ∃ n∈ (InfOcc ss'), ∀ a ∈ (InfOcc ss'), (A.parityMap a) ≤ (A.parityMap n) := by
    apply Set.exists_max_image (InfOcc ss') (A.parityMap)
    · unfold InfOcc
      exact Set.Finite.subset (@Set.finite_univ A.State A.FinState) (fun ⦃a⦄ a ↦ trivial)
    · exact infoccnonemp
  obtain ⟨n, hn⟩:= htest
  use (A.parityMap n)
  intro a ha
  rw [Set.mem_image] at ha
  rcases ha with ⟨xa, hxa⟩
  rw [← hxa.2]
  exact hn.2 _ hxa.1

open Classical in
lemma sumpointseqnumstate {A : NPA Alph} {w : Stream' Alph} {ρ_w : Stream' (A.StutterClosed).State}
    (f : Stream' ℕ) (ρ_w_run : A.StutterClosed.InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) (i : ℕ) (hfi : f i > 0) :
    ∃ q, (ρ_w (∑ m ∈ Finset.range (i + 1), (f m + 1)) = (q, Sum.inr (⟨A.parityMap q, by simp⟩)))
    := by
  rw [hf]
  have k_spec : n_lt_sumk (∑ m ∈ Finset.range (i), (f m + 1)) f (i) := by
    unfold n_lt_sumk
    rw [Finset.sum_range_succ, add_comm]
    simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
  unfold n_lt_sumk at k_spec
  rw [Finset.sum_range_succ] at k_spec
  have k_spec2 := k_spec
  nth_rewrite 3 [hf] at k_spec
  unfold subset_f subset_wb_f_pair at k_spec
  simp only at k_spec
  rw [Nat.sub_add_cancel (by simp), ← Nat.sub_lt_iff_lt_add' (by simp), Nat.sub_self] at k_spec
  apply Nat.le.dest at k_spec
  simp only [Nat.succ_eq_add_one, zero_add] at k_spec
  rcases k_spec with ⟨k2, hk2⟩
  have hk2b := hk2.symm
  rw [Nat.find_eq_iff] at hk2b
  rcases hk2b with ⟨k2_spec, k2_big⟩
  simp only [gt_iff_lt, add_pos_iff, zero_lt_one, true_or, not_exists, true_and] at k2_spec
  simp only [hk2] at k2_big
  rw [hf] at hfi
  unfold subset_f subset_wb_f_pair at hfi
  specialize k2_big ((Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (i))) - 1)
  have nat_find_lt: (((Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (i))) - 1)) <
    (Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (i))) := by omega
  apply k2_big at nat_find_lt
  simp only [not_and] at nat_find_lt
  apply nat_find_lt at hfi
  simp only [not_not] at hfi
  rcases hfi with ⟨q, hq⟩
  clear nat_find_lt k2_big
  have ρ_w_next_spec : ρ_w ((∑ x ∈ Finset.range (i + 1), (f x + 1))) ∈
      (A.StutterClosed).next (ρ_w ((∑ x ∈ Finset.range (i + 1), (f x + 1)) -1))
      (w ((∑ x ∈ Finset.range (i + 1), (f x + 1)) - 1)) := by
    have run := ρ_w_run.2 ((∑ x ∈ Finset.range (i + 1), (f x + 1)) - 1)
    rw [Nat.sub_add_cancel (by rw [Finset.sum_range_succ]; omega)] at run
    exact run
  unfold NA.next NPA.toNA NPA.StutterClosed at ρ_w_next_spec
  simp only at ρ_w_next_spec
  have finsetrangesucc_eqfinsum : (∑ m : Fin i, ((subset_wb_f_pair w ρ_w_pareven ↑m).2 + 1)
      + (Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven i) - 1)) =
      (∑ x ∈ Finset.range (i+1), (f x + 1) - 1) := by
    nth_rewrite 1 [Fin.sum_univ_eq_sum_range
        (fun m ↦ ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)) i]
    rw [Finset.sum_range_succ, hf]
    unfold subset_f
    simp only
    conv =>
      rhs
      unfold subset_wb_f_pair
      simp only
    conv =>
      lhs
      lhs
      unfold subset_wb_f_pair
      simp only
    rw [Nat.add_sub_assoc (by omega), Nat.add_right_inj, Nat.add_sub_cancel]
  rw [← finsetrangesucc_eqfinsum, hq] at ρ_w_next_spec
  simp only [gt_iff_lt, not_exists, decide_eq_true_eq, Set.mem_ite_empty_right, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ρ_w_next_spec
  specialize  k2_spec q
  use q
  rcases ρ_w_next_spec with ⟨_, state⟩
  rw [← Nat.add_sub_assoc (k:=1) (by rw [← hk2]; omega), ← Nat.add_left_inj (n:=1),
    Nat.sub_add_cancel (by rw [← hk2]; omega),
    Nat.sub_add_cancel (by rw [Finset.sum_range_succ]; omega)] at finsetrangesucc_eqfinsum
  rw [hk2, finsetrangesucc_eqfinsum] at k2_spec
  nth_rewrite 2 [hf] at state
  exact Or.resolve_left state k2_spec

set_option pp.proofs true in
set_option pp.showLetValues true in
open Classical in
/-- Claim 4.2.5 -/
lemma subset_rhow'_pareven {A : NPA Alph} {w : Stream' Alph} {ρ_w : Stream' (A.StutterClosed).State}
    (ρ_w_run : A.StutterClosed.InfRun w ρ_w) {f f' : Stream' ℕ}
    (ρ_w_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) (hf' : f' = subset_f' ρ_w_run ρ_w_pareven hf) :
    let wb := subset_wb w ρ_w_pareven;
    Even (sSup (A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) := by
  intro wb
  have hM : ∃ n, (∀ a ∈ (A.parityMap '' InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup A (subset_rhow' ρ_w_run ρ_w_pareven hf)
  have hMs : ∃ n, (∀ a ∈ ((A.StutterClosed).parityMap '' InfOcc ρ_w), a ≤ n) :=
    par_map_inf_occ_of_ss_has_sup A.StutterClosed ρ_w
  have ssuple: (sSup (A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 ≤
       (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)) := by
    rw [Nat.sSup_def hM]
    let sl := Nat.find hM
    have sl_spec : (∀ a ∈ (A.parityMap '' InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)), a ≤ sl) :=
      Nat.find_spec hM

    have slinrange : sl ∈ A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)) := by
      unfold sl
      rw [← Nat.sSup_def hM]
      exact Nat.sSup_mem (Set.image_nonempty.mpr infoccnonemp) (bddAbove_def.mp hM)

    simp only [Set.mem_image] at slinrange
    rcases slinrange with ⟨x, ⟨hxinf, hxsup⟩⟩
    have hxevent := @inf_occ_eventually (A.State) (A.FinState) (subset_rhow' ρ_w_run ρ_w_pareven hf)
    rw [Filter.eventually_atTop] at hxevent
    rcases hxevent with ⟨idw', hidw'⟩
    unfold InfOcc at hxinf
    rw [Set.mem_setOf, Filter.frequently_atTop] at hxinf
    have hslininfoc : (sl + 2) ∈ (InfOcc ((A.StutterClosed.parityMap) ∘ ρ_w)) := by
      unfold InfOcc
      rw [Set.mem_setOf, Filter.frequently_atTop]
      intro iwmin
      let ib := (Nat.find (kexists iwmin f))
      let iw'sum := ∑ m ∈ Finset.range (ib + 1), (f' m + 1)
      let idw'_b := (Nat.find (kexists idw' f'))
      let idw'_bsum := ∑ m ∈ Finset.range (idw'_b + 1), (f' m + 1)
      let iw'min := max iw'sum idw'_bsum
      -- Hier nog net iets verder specialiseren
      specialize hxinf (iw'min + 1)
      rcases hxinf with ⟨iw', ⟨iw'ge, hiw'⟩⟩
      let iw'_b := (Nat.find (kexists (iw'-1) f'))
      have hiw'_b : iw'_b = (Nat.find (kexists (iw'-1) f')) := rfl
      have hiw'2 := hiw'
      unfold subset_rhow' at hiw'
      simp only at hiw'
      unfold subset_f'_rhow'_pair at hiw'
      simp only at hiw'
      rw [hf'] at hiw'_b
      rw [← hiw'_b] at hiw'
      rw [← hf'] at hiw'_b
      split at hiw'
      case isTrue hfiwzero =>
        use (∑ m ∈ Finset.range (iw'_b+1), (f m + 1))
        constructor
        · -- ?? TODO
          sorry
        · let h1 := subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven hf iw'_b (Eq.mpr_prop (Eq.refl (f iw'_b = 0)) hfiwzero)
          -- let h1 := (subset_f'_rhow'_pair._proof_2 ρ_w_run ρ_w_pareven iw'_b
          --     (Eq.mpr_prop (Eq.refl (f iw'_b = 0)) hfiwzero))
          let n := h1.choose
          have hn : n = h1.choose := by rfl
          -- unfold h1 at hn
          rw! [← hn] at hiw'
          let h2 := h1.choose_spec
          let ρ_fin := h2.choose
          have hρ_fin : ρ_fin = h2.choose := by rfl
          rw! [← hρ_fin] at hiw'
          simp at hiw'
          have ρ_fin_spec := h2.choose_spec
          rw! [← hρ_fin] at ρ_fin_spec
          rcases ρ_fin_spec with ⟨n_ge, finrunstart, max, e⟩
          rw! [Fin.sum_univ_eq_sum_range (fun n ↦ f n + 1) iw'_b] at e
          simp only [Function.comp_apply]
          unfold NPA.parityMap NPA.StutterClosed
          simp only
          rw! [Fin.sum_univ_eq_sum_range (fun n ↦ f n + 1) iw'_b, ← Finset.sum_range_succ] at max
          rw! [max, Sum.elim_inr]
          simp only
          -- Follows from the fact that every ρ_fin is also a subset_rhow' with b≥idw' and then use
          -- hidw'
          have slmaxρfin : (∀ a ∈ NPA.parityMap '' (ρ_fin '' {l |  l > 0 ∧ l ≤
              (Eq.symm (Finset.sum_range_succ (fun i ↦ f i + 1) iw'_b) ▸
            Fin.sum_univ_eq_sum_range (fun n ↦ f n + 1) iw'_b ▸ h1).choose}), a ≤ sl) := by
            sorry

          have hslρfin : ∃ n, ∀ a ∈ NPA.parityMap '' (ρ_fin '' {l | l > 0 ∧ l ≤
              (Eq.symm (Finset.sum_range_succ (fun i ↦ f i + 1) iw'_b) ▸
              Fin.sum_univ_eq_sum_range (fun n ↦ f n + 1) iw'_b ▸ h1).choose}), a ≤ n := by use sl

          -- Follows from hiw'
          have slinρfin : sl ∈  NPA.parityMap '' (ρ_fin '' {l | l > 0 ∧ l ≤
              (Eq.symm (Finset.sum_range_succ (fun i ↦ f i + 1) iw'_b) ▸
              Fin.sum_univ_eq_sum_range (fun n ↦ f n + 1) iw'_b ▸ h1).choose}) := by
            sorry

          rw [Nat.sSup_def hslρfin, Nat.add_left_inj, Nat.find_eq_iff]
          constructor
          · exact slmaxρfin
          · intro n hn
            apply not_forall_of_exists_not
            use sl
            intro hsl
            apply hsl at slinρfin
            apply Nat.not_lt_of_le at slinρfin
            exact slinρfin hn

      case isFalse hfiwnonzero =>
        simp at hiw'
        have fzero : f' iw'_b = 0 := by
          rw [hf']
          unfold subset_f' subset_f'_rhow'_pair
          simp only [hfiwnonzero, ↓reduceDIte]
        have hone : iw' -  ∑ m ∈ Finset.range (iw'_b),
            (f' m + 1) = 1 := by
          have hiw'_b2 := hiw'_b
          rw [Nat.find_eq_iff] at hiw'_b
          unfold n_lt_sumk at hiw'_b
          rcases hiw'_b with ⟨hiw'_b, right⟩
          rw [Finset.sum_range_succ, ← hiw'_b2, fzero, zero_add, add_comm,
            ← Nat.sub_lt_iff_lt_add (by sorry), Nat.lt_one_iff, Nat.sub_right_comm,
            ← Nat.add_right_cancel_iff (n:=1)] at hiw'_b
          rw [← hiw'_b2] at right
          specialize right (iw'_b-1)
          simp only [tsub_lt_self_iff, zero_lt_one, and_true, not_lt] at right
          rw [Nat.sub_add_cancel (by sorry)] at hiw'_b
          exact hiw'_b
        rw [← hf', hone] at hiw'
        simp only [↓reduceIte] at hiw'
        use (∑ m ∈ Finset.range (iw'_b + 1), (f m + 1))
        -- Nu laten zien dat dat die toestand is, dat is moeilijk maar gaan we regelen
        -- Nu laten zien met de nat.find dat je in een (q, omega(q)) toestand zit
        have hfiwnonzero2 : f iw'_b ≥ 1 := by omega
        rw [hf] at hfiwnonzero2
        unfold subset_f at hfiwnonzero2
        simp only [ge_iff_le] at hfiwnonzero2
        unfold subset_wb_f_pair at hfiwnonzero2
        simp only at hfiwnonzero2
        rw [Nat.le_sub_one_iff_lt (by omega), ← Nat.add_one_le_iff] at hfiwnonzero2
        simp only [Nat.reduceAdd] at hfiwnonzero2
        simp only [gt_iff_lt, not_exists, Nat.le_find_iff, not_and, not_forall,
          Decidable.not_not] at hfiwnonzero2
        specialize hfiwnonzero2 1
        simp only [Nat.one_lt_ofNat, zero_lt_one, forall_const] at hfiwnonzero2
        obtain ⟨q, hq⟩ := sumpointseqnumstate f ρ_w_run ρ_w_pareven hf iw'_b
          (by apply Nat.pos_iff_ne_zero.mpr hfiwnonzero)
        have stateone : (ρ_w (∑ m ∈ Finset.range (iw'_b + 1), (f m + 1))).1 = q := by
          simp only [hq]
        rw [hiw'_b] at stateone
        rw [← stateone] at hq
        constructor
        · have basebig : iw'_b + 1 ≥ ib + 1:= by
            refine Nat.add_le_add (c:= 1) (d:= 1) ?_ (by rfl)
            have iw'big : iw' - 1 ≥ iw'sum := by omega
            unfold iw'sum at iw'big
            unfold iw'_b n_lt_sumk
            simp only [Nat.le_find_iff, not_lt]
            intro m hm
            have sumgt : (∑ m ∈ Finset.range (m + 1), (f' m + 1)) ≤
                (∑ m ∈ Finset.range (ib + 1), (f' m + 1))  := by
              rw [lt_iff_exists_add] at hm
              rcases hm with ⟨c, hcge, hcib⟩
              rw [hcib, add_assoc, add_comm c 1, ← add_assoc]
              nth_rewrite 2 [Finset.sum_range_add]
              omega
            exact ge_trans iw'big sumgt
          rw [← Nat.sub_add_cancel basebig, add_comm, Finset.sum_range_add]
          have hib : ib = Nat.find (kexists (iwmin) f) := by unfold ib; exact rfl
          have hib2 := hib
          rw [Nat.find_eq_iff, ← hib2] at hib
          unfold n_lt_sumk at hib
          exact Nat.le_add_right_of_le (Nat.le_of_lt hib.1)
        · simp only [Function.comp_apply]
          unfold NPA.parityMap NPA.StutterClosed
          simp only [hq, Sum.elim_inr, Nat.add_right_cancel_iff]
          rw [hiw']
          exact hxsup

    rw [infOcc_comp_of_Finite ((A.StutterClosed).FinState), Set.mem_image] at hslininfoc
    rcases hslininfoc with ⟨q, ⟨hqinf, hqomega⟩⟩
    rw [Nat.sSup_def hMs, Nat.le_find_iff]
    intro m hm
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall,
          not_le]
    use q
    unfold sl at hqomega
    rw [hqomega]
    exact ⟨hqinf, hm⟩

  have ssupge: (sSup (A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 ≥
       (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)) := by
    rw [Nat.sSup_def hMs]
    let sr := Nat.find hMs
    let sr_spec := Nat.find_spec hMs
    have srinrange : sr ∈ (A.StutterClosed).parityMap '' (InfOcc ρ_w) := by
      unfold sr
      rw [← Nat.sSup_def hMs]
      exact Nat.sSup_mem (Set.image_nonempty.mpr infoccnonemp) (bddAbove_def.mp hMs)
    simp only [Set.mem_image] at srinrange
    rcases srinrange with ⟨x, ⟨hxinf, hxsup⟩⟩
    have hxevent := @inf_occ_eventually ((A.StutterClosed).State) ((A.StutterClosed).FinState) ρ_w
    rw [Filter.eventually_atTop] at hxevent
    rcases hxevent with ⟨idw, hidw⟩
    unfold InfOcc at hxinf
    rw [Set.mem_setOf, Filter.frequently_atTop] at hxinf
    have srininfocc : (sr-2) ∈ (InfOcc (A.parityMap ∘ (subset_rhow' ρ_w_run ρ_w_pareven hf))) := by
      -- Hier nog even wat uitwerken
      unfold InfOcc
      rw [Set.mem_setOf, Filter.frequently_atTop]
      intro iw'min
      let ib := (Nat.find (kexists iw'min f'))
      let iwsum := ∑ m ∈ Finset.range (ib + 1), (f m + 1)
      let idw_b := (Nat.find (kexists idw f))
      let idw_bsum := ∑ m ∈ Finset.range (idw_b + 1), (f m + 1)
      let iwmin := max iwsum idw_bsum
      specialize hxinf (iwmin+1)
      rcases hxinf with ⟨iw, ⟨iwge, hiw⟩⟩
      let iw_b := (Nat.find (kexists (iw - 1) f))
      have hiw_b : iw_b = (Nat.find (kexists (iw - 1) f)) := rfl
      rw [← hiw] at hxsup
      clear hiw
      if hfzero : f iw_b = 0 then
        unfold subset_rhow' subset_f'_rhow'_pair
        simp only
        -- Volgt uit het feit dat f iw_b =0
        have iweqsum : iw = ∑ m : Fin iw_b, (f m + 1)  + (f iw_b + 1):= by sorry
--         theorem Set.exists_upper_bound_image {α : Type u} {β : Type v} [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β) (h : s.Finite) :
-- ∃ (a : α), ∀ b ∈ s, f b ≤ f a


        simp only [Function.comp_apply]
        let a := subset_wb w ρ_w_pareven iw_b
        let s := ∑ m : Fin iw_b, (f m + 1)
        let e := ∑ m : Fin iw_b, (f m + 1) + (f iw_b + 1)
        have he : e = ∑ m : Fin iw_b, (f m + 1) + (f iw_b + 1) := by rfl
        rw [← Finset.sum_range (fun i ↦ (f i + 1)), ← Finset.sum_range_succ] at he
        have h1 := @subset_f'_rhow'_pair._proof_2 Alph A w f ρ_w ρ_w_run ρ_w_pareven hf iw_b hfzero
        let n := h1.choose
        have hn : n = h1.choose := rfl
        have h2 := h1.choose_spec
        let ρfin := h2.choose
        have hρfin : ρfin = h2.choose := rfl
        obtain ⟨hnge, ⟨hfinrunstart, ⟨hsup, hend⟩⟩⟩ := h2.choose_spec
        rw! [← hn] at hnge
        rw! [← hn, ← hρfin] at hfinrunstart hsup hend
        rw! [← iweqsum] at hsup
        unfold NPA.StutterClosed at hxsup
        simp only at hxsup
        rw [Prod.snd_eq_iff] at hsup
        rw [hsup] at hxsup
        simp only [gt_iff_lt, Sum.elim_inr] at hxsup
        have hupperbound : ∃ s, ∀ a ∈ NPA.parityMap '' (ρfin '' {l | 0 < l ∧ l ≤ n}), a ≤ s := by
          sorry
        rw [Nat.sSup_def hupperbound] at hxsup
        -- apply Eq.symm at hxsup
        have hxsup2 := hxsup.symm
        apply Nat.sub_eq_of_eq_add at hxsup2
        have hxsup := hxsup2.symm
        clear hxsup2
        rw [Nat.find_eq_iff] at hxsup
        rcases hxsup with ⟨min, max⟩
        specialize max ((sr-2)-1)
        have srmin : sr -2 - 1 < sr - 2 := by
          apply Nat.sub_one_lt
          -- als dit wel nul is dan is dit gewoon even een andere case
          sorry
        apply max at srmin
        simp at srmin
        rcases srmin with ⟨x, hx⟩
        specialize min (NPA.parityMap (ρfin x))
        simp at min
        specialize min x
        rcases hx with ⟨hx1,hx2,hx3⟩
        apply min at hx1
        apply hx1 at hx2
        simp at hx2
        apply Nat.succ_le_of_lt at hx3
        simp at hx3
        rw [Nat.sub_add_cancel (n:=sr-2) (m:=1) (by sorry)] at hx3
        have sreq := Nat.le_antisymm hx3 hx2
        let startw' :=  ∑ m : Fin iw_b, (f' m + 1)
        have hstartw' : startw' =  ∑ m : Fin iw_b, (f' m + 1) := rfl
        use startw' + x
        constructor
        · -- TODO
          sorry
        · have ibeq : Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf (startw' + x))
            = iw_b := by sorry
          rw! [ibeq, ← hρfin, ← hn, hfzero]
          simp only [↓reduceDIte]
          rw [hstartw', Finset.sum_range, ← hf']
          simpa only [add_tsub_cancel_left] using sreq.symm
      else
        use ∑ m ∈ Finset.range (iw_b), (f' m + 1) + 1
        constructor
        ·  -- TODO
          -- Follows from definition of all the i's

          sorry
        · unfold subset_rhow' subset_f'_rhow'_pair
          simp only [Function.comp_apply]
          have natfindiwb : (Nat.find (subset_rhow'._proof_1 ρ_w_run ρ_w_pareven hf
              (∑ m ∈ Finset.range iw_b, (f' m + 1) + 1))) = iw_b := by
            sorry
          rw! [natfindiwb]
          simp only [hfzero, ↓reduceDIte]
          rw [hf']
          simp only [add_tsub_cancel_left, ↓reduceIte]
          -- Follows from the fact that npa.paritymap ρw_iw = sr and that is even and the rest of
          -- the ρw are loop states so odd parity
          have iweqsum : iw = ∑ m ∈ Finset.range (iw_b + 1), (f m + 1) := by sorry
          -- rw [← iweqsum]
          unfold NPA.parityMap NPA.StutterClosed at hxsup
          simp only at hxsup
          have fgtzero :  f iw_b > 0 := by omega
          obtain ⟨q, hq⟩ := sumpointseqnumstate f ρ_w_run ρ_w_pareven hf iw_b fgtzero
          rw [← iweqsum] at hq ⊢
          rw [Prod.eq_iff_fst_eq_snd_eq] at hq
          rw [hq.2] at hxsup
          simp at hxsup
          rw [hq.1]
          simp only
          exact Nat.eq_sub_of_add_eq hxsup
    rw [infOcc_comp_of_Finite (A.FinState), Set.mem_image] at srininfocc
    rcases srininfocc with ⟨q, ⟨hqinf, hqomega⟩⟩
    apply LE.le.ge
    rw [Nat.sSup_def hM, Nat.find_le_iff]
    use sr
    constructor
    · apply Nat.le_add_of_sub_le
      rw [Nat.le_find_iff]
      intro m hm
      simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall,
            not_le]
      use q
      unfold sr at hqomega
      rw [hqomega]
      exact ⟨hqinf, hm⟩
    · intro a ha
      specialize sr_spec a
      apply sr_spec at ha
      unfold sr
      exact ha
  have ssupsame: (sSup (A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 =
       (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_w)) := le_antisymm_iff.2 ⟨ssuple, ssupge⟩
  by_contra hypo
  simp only [Nat.not_even_iff_odd] at hypo
  have ssupodd: Odd ((sSup (A.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2) :=
    Odd.add_even hypo even_two
  rw [ssupsame, ← Nat.not_even_iff_odd] at ssupodd
  exact ssupodd ρ_w_pareven

/-! ### Proof Supset (right to left)  -/
/-! #### Definitions-/
/-- Definition 4.2.6 -/
noncomputable def supset_rhowb {A : NPA Alph} (ρ_w' : Stream' A.State) (f : Stream' ℕ) :
    Stream' (A.StutterClosed).State
| k =>
    if k = 0 then
      (ρ_w' 0 , Sum.inr ⟨(A.parityMap (ρ_w' 0)), inrange (ρ_w' 0)⟩)
    else if f (k - 1) = 0 then
      let q : A.State := ρ_w' ((∑ m ∈ Finset.range k, (f m + 1)))
      (q, Sum.inr ⟨(A.parityMap q), inrange q⟩)
    else
      let start : ℕ := ∑ m ∈ Finset.range (k-1), (f m + 1)
      let maxp : ℕ :=
           sSup (A.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + f (k - 1) + 1))}))
      (ρ_w' (start + f (k - 1) + 1), Sum.inr ⟨maxp, ssupinrange
      (inpnonemp ρ_w' start (f (k - 1) + 1) (by simp)) (inpfinite ρ_w' start (f (k- 1) + 1))⟩)


-- Here the pattern matching apperently does not work to show termination
-- Setting: w = wb[f], w' = wb[f']. Dan ss is run op wb en ss' is run op w'
open Classical in
/-- Definition 4.2.9 -/
noncomputable def supset_rhow {A : NPA Alph} (ρ_wb : Stream' (A.StutterClosed).State)
    (ρ_w' : Stream' A.State) (w : Stream' Alph) (f f' : Stream' ℕ) (k : ℕ) :
    (A.StutterClosed).State :=
  if k = 0 then
    ρ_wb 0
  else
    let k_b : ℕ :=  Nat.find (kexists (k-1) f)
    if fkb_zero : f k_b = 0 then
      ρ_wb (k_b + 1)
    else
      let i := k - ∑ m∈ Finset.range (k_b), (f m + 1) + 1 -- denk niet +1
      if h : ((ρ_wb (k_b + 1)).1, Sum.inl (w k)) ∈
          ((A.StutterClosed).next (supset_rhow ρ_wb ρ_w' w f f' (k - 1)) (w k)) then
        if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
          ((ρ_wb (k_b + 1)).1, Sum.inr ⟨A.parityMap (ρ_wb (k_b + 1)).1, by simp only [Set.mem_range,
            exists_apply_eq_apply]⟩)
        else
          ((ρ_wb (k_b + 1)).1, Sum.inl (w k))
      else
        if hdiff1: f k_b ≤ f' k_b then
          if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
            if hdiff2: f k_b = f' k_b then
              (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1),
              Sum.inr ⟨A.parityMap (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1)), by simp⟩)
            else
              let start := i + ∑ m∈ Finset.range (k_b), (f' m + 1)
              let diff := f' k_b - f k_b
              let maxp := sSup (A.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + diff))}))
              ((ρ_w' (start + diff)) , Sum.inr ⟨maxp, (ssupinrange
              (inpnonemp ρ_w' start diff (by omega)) (inpfinite  ρ_w' start diff))⟩)
          else
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)),
            Sum.inr ⟨A.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
        else
          if hi: i <= f' k_b then
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)),
            Sum.inr ⟨A.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
          else
            if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
              ((ρ_wb (k_b + 1)).1, Sum.inr ⟨A.parityMap (ρ_wb (k_b + 1)).1, by simp only
              [Set.mem_range, exists_apply_eq_apply]⟩)
            else
              ((ρ_wb (k_b + 1)).1, Sum.inl (w k))

/-! ### Lemmas for claim 4.2.7 -/
lemma rhowb_sumcorrect {A : NPA Alph} (f' : Stream' ℕ) (ρ_w' : Stream' (A.State)) :
    ∀ (k : ℕ), (supset_rhowb ρ_w' f' k).1 = ρ_w' (∑ m ∈ Finset.range k, (f' m + 1)) := by
  intro k
  cases k
  case zero =>
    unfold supset_rhowb
    simp only [↓reduceIte, Finset.range_zero, Finset.sum_empty]
  case succ n =>
    simp only [supset_rhowb, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
               add_tsub_cancel_right]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1]
    else
      simp only [↓reduceIte, h1]
      apply congrArg
      rw [Finset.sum_range_succ, add_assoc]

lemma rhowb_numstate {A : NPA Alph} (f' : Stream' ℕ) (ρ_w' : Stream' (A.State)) (k : ℕ) :
    let ρ_wb := supset_rhowb ρ_w' f'; (ρ_wb k).1 = ρ_w' (∑ m ∈ Finset.range k, (f' m + 1)) →
    ∃ p, (ρ_wb k).2 = Sum.inr p := by
  intro ρ_wb hk
  cases k
  case zero =>
    unfold ρ_wb supset_rhowb
    simp only [↓reduceIte, Sum.inr.injEq, exists_eq']
  case succ n =>
    unfold ρ_wb supset_rhowb
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      Subtype.exists, Set.mem_range]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right',
        exists_apply_eq_apply]
    else
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right']
      apply @ssupinrange Alph A
        ((ρ_w' '' {l | ∑ m ∈ Finset.range n, (f' m + 1) < l
                     ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1}))
      · simp only [Set.image_nonempty]
        refine Set.nonempty_of_mem (x:= (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)) ?_
        · simp only [add_assoc, Set.mem_setOf_eq, lt_add_iff_pos_right, add_pos_iff, zero_lt_one,
          or_true, le_refl, and_self]
      · apply Set.Finite.image ρ_w'
        refine Set.Finite.subset (s:= {l | l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1}) ?_ ?_
        · exact (Set.finite_le_nat (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1))
        · exact (Set.sep_subset_setOf (∑ m ∈ Finset.range n, (f' m + 1)).succ.le fun x ↦
              x ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)

lemma inpsame {A : NPA Alph} (f' : Stream' ℕ) (ρ_w' : Stream' (A.State)) (k : ℕ) : ρ_w' ''
    {l | ∑ m ∈ Finset.range k, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range k, (f' m + 1) + f' k + 1} =
    Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ρ_w' '' {k_1 | k_1 > 0 ∧ k_1 ≤ f' k + 1} := by
  unfold Stream'.drop Stream'.get Set.image
  apply Set.ext_iff.2
  intro x
  rw [Set.mem_setOf]
  refine ⟨?_,?_⟩
  · intro h
    obtain ⟨a, ⟨ha, ssax⟩⟩:=h
    rw [Set.mem_setOf] at ha
    use a - ∑ m ∈ Finset.range k, (f' m + 1)
    constructor
    · rw [add_assoc, add_comm] at ha
      apply Set.mem_setOf.2
      simpa only [gt_iff_lt, tsub_pos_iff_lt, tsub_le_iff_right] using ha
    · simpa only [add_comm, Nat.add_sub_cancel' (le_of_lt ha.1)] using ssax
  · intro h
    obtain ⟨a, ⟨ha, ssax⟩⟩:=h
    use (a + ∑ m ∈ Finset.range k, (f' m + 1))
    constructor
    · apply Set.mem_setOf.1 at ha
      rw [Set.mem_setOf, lt_add_iff_pos_left, add_assoc, add_comm, add_le_add_iff_left]
      exact ha
    · simp only [ssax]

/-- Claim 4.2.7 -/
lemma supset_rhowb_run {A : NPA Alph} {w' wb : Stream' Alph} {ρ_w' : Stream' A.State}
    {f' : Stream' ℕ} (ρ_w'_run : A.InfRun w' ρ_w') (w'_wbf : w' = functiononword wb f') :
    let ρ_wb := supset_rhowb ρ_w' f'; (A.StutterClosed).InfRun wb ρ_wb := by
  intro ρ_wb
  rw [NA.InfRun]
  rcases ρ_w'_run with ⟨ρ_w'_init, ρ_w'_next⟩
  constructor
  · exact Set.mem_setOf.2 ⟨ρ_w' 0, ρ_w'_init, rfl⟩
  · intro k
    conv =>
      rhs
      simp only [ρ_wb, supset_rhowb]
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one]
    if h1 : (f' k) = 0  then
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (rhowb_sumcorrect f' ρ_w' )]
      rcases rhowb_numstate f' ρ_w' k (rhowb_sumcorrect f' ρ_w' k) with ⟨p, hp⟩
      rw [hp, Finset.sum_range_succ, h1, zero_add]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, reduceCtorEq, and_false, exists_false, gt_iff_lt,
        ge_iff_le, exists_and_left, exists_and_right, Sum.inr.injEq, Subtype.mk.injEq, exists_prop,
        false_or]
      let ρfin := fun i ↦ if i = 0 then (ρ_w' (∑ m ∈ Finset.range k, (f' m + 1))) else
        (ρ_w' (∑ m ∈ Finset.range k, (f' m + 1)+1))
      use 1, ρfin
      constructor
      · unfold NA.FinRunStart
        constructor
        · unfold ρfin
          simp only [↓reduceIte]
        · unfold ρfin
          simp only [Nat.lt_one_iff, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, forall_eq]
          specialize ρ_w'_next (∑ m ∈ Finset.range k, (f' m + 1))
          rw [← Nat.zero_add (∑ m ∈ Finset.range k, (f' m + 1)),
              functiononword_eq_base_word w'_wbf k (by omega), Nat.zero_add] at ρ_w'_next
          exact ρ_w'_next
      · constructor
        · constructor
          · omega
          · have singleton : {l | 0 < l ∧ l ≤ 1} = {1} := by
              sorry
            rw [singleton]
            unfold ρfin
            simp only [Set.image_singleton, one_ne_zero, ↓reduceIte, csSup_singleton]

        · unfold ρfin
          simp only [one_ne_zero, ↓reduceIte]



      -- refine Or.inl (Or.inl ?_)
      -- simp only [Set.mem_setOf_eq, Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, existsAndEq,
      --   and_self, and_true]
      -- rw [← functiononword_eq_base_word (b:=0) w'_wbf k (by linarith), zero_add]
      -- exact ρ_w'_next (∑ m ∈ Finset.range k, (f' m + 1))
    else
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (rhowb_sumcorrect f' ρ_w' )]
      rcases rhowb_numstate f' ρ_w' k (rhowb_sumcorrect f' ρ_w' k) with ⟨p, hp⟩
      rw [hp]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      right
      nth_rewrite 1 [add_assoc]
      apply Set.mem_setOf.2
      use (f' k + 1), Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ρ_w'
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
      · unfold NA.FinRunStart
        refine ⟨?_, ?_⟩
        · unfold Stream'.drop Stream'.get
          simp only [zero_add]
        · intro b hb
          unfold Stream'.drop Stream'.get
          rw [← functiononword_eq_base_word w'_wbf k hb, add_right_comm]
          exact ρ_w'_next  (b + ∑ m ∈ Finset.range k, (f' m + 1))
      · simp only [gt_iff_lt, Sum.inr.injEq, Subtype.mk.injEq]
        exact ⟨congrArg sSup (congrArg (Set.image A.parityMap) (inpsame f' ρ_w' k)),
               Eq.symm Stream'.get_drop'⟩

-- Lemmas for claim 4.2.8


open Classical in
/-- Claim 4.2.8 -/
lemma supset_rhowb_pareven {A : NPA Alph} (w : Stream' Alph) (f : Stream' ℕ) {f' : Stream' ℕ}
    {w' wb : Stream' Alph} {ρ_w' : Stream' A.State} (ρ_w'_run : A.InfRun w' ρ_w')
    (ρ_w'_pareven : Even (sSup (A.parityMap '' InfOcc ρ_w'))) (w'_wbf : w' = functiononword wb f') :
    let ρ_wb := supset_rhowb ρ_w' f'; Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_wb)) := by
  intro ρ_wb
  let Ms := (A.StutterClosed)
  have samesup : sSup (A.parityMap '' InfOcc ρ_w') + 2 =
      sSup ((A.StutterClosed).parityMap '' InfOcc (supset_rhowb ρ_w' f')) := by
    have hMs : ∃ n, (∀ a ∈ (Ms.parityMap '' InfOcc ρ_wb), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup Ms ρ_wb
    rw [Nat.sSup_def hMs]
    have hM : ∃ n, (∀ a ∈ (A.parityMap '' InfOcc ρ_w'), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup A ρ_w'
    rw [Nat.sSup_def hM]
    -- Iets met +2 aanpassen
    --- goed hierover nadenken nog...
    rw [le_antisymm_iff]
    constructor
    · simp
      intro m hm
      rw [← tsub_lt_iff_right, Nat.lt_find_iff] at hm
      simp only [not_forall, not_le] at hm
      unfold NPA.parityMap Ms NPA.StutterClosed
      simp only [Prod.exists, Sum.exists, Sum.elim_inl, Nat.lt_one_iff,
        exists_and_right, Sum.elim_inr, Subtype.exists, Set.mem_range]
      specialize hm (m-2)
      simp at hm
      rcases hm with ⟨x, hx⟩
      use x
      right
      use A.parityMap x
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
/-- Claim 4.2.10 -/
lemma supset_rhow_run {w wb w' : Stream' Alph} {A : NPA Alph} {f : Stream' ℕ}
    {ρ_wb : Stream' (A.StutterClosed).State} {ρ_w' : Stream' A.State} (hw : w = functiononword wb f)
    (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_wb)))
    (ρ_wb_run : A.StutterClosed.InfRun wb ρ_wb)
    (ρ_w'_pareven : Even (sSup (A.parityMap '' InfOcc ρ_w')))
    (ρ_w'run : A.InfRun w' ρ_w') : A.StutterClosed.InfRun w (supset_rhow ρ_wb ρ_w' w f f') := by
  unfold NA.InfRun
  rcases ρ_wb_run with ⟨ρ_wb_init, ρ_wb_next⟩
  constructor
  · unfold supset_rhow
    simpa only [↓reduceIte] using ρ_wb_init
  · intro k
    unfold supset_rhow
    cases k
    · sorry
      -- zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]
      -- , zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]
    · sorry

/-- Claim 4.2.11 -/
lemma supset_rhow_pareven {w wb w' : Stream' Alph} {A : NPA Alph} {f : Stream' ℕ}
    {ρ_wb : Stream' (A.StutterClosed).State} {ρ_w' : Stream' A.State} (hw : w = functiononword wb f)
    (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((A.StutterClosed).parityMap '' InfOcc ρ_wb)))
    (ρ_wb_run : A.StutterClosed.InfRun wb ρ_wb)
    (ρ_w'_pareven : Even (sSup (A.parityMap '' InfOcc ρ_w'))) (ρ_w'_run : A.InfRun w' ρ_w') :
    Even (sSup ((A.StutterClosed).parityMap '' InfOcc (supset_rhow ρ_wb ρ_w' w f f'))) := by sorry

/-- Full theorem -/
theorem NPA.StutterClosed.AcceptsStutterClosure (A : NPA Alph) :
    (A.StutterClosed).AcceptedOmegaLang = StutterClosure (A.AcceptedOmegaLang) := by
  ext w
  constructor
  · intro hwinlang
    unfold NPA.AcceptedOmegaLang at hwinlang ⊢
    rw [Set.mem_setOf, NPA.ParityAccept] at hwinlang
    rw [StutterClosure, Set.mem_setOf]
    rcases hwinlang with ⟨ρ_w, ⟨ρ_w_run, ρ_w_pareven⟩⟩
    let wb := subset_wb w ρ_w_pareven
    let f := subset_f w ρ_w_pareven
    let f' := subset_f' ρ_w_run ρ_w_pareven (f:=f) rfl
    let ρ_w' := subset_rhow' ρ_w_run ρ_w_pareven (f:=f) rfl
    use (functiononword wb f')
    rw [Set.mem_setOf, NPA.ParityAccept]
    constructor
    · use ρ_w'
      exact ⟨subset_rhow'_run ρ_w_run ρ_w_pareven rfl rfl rfl,
        subset_rhow'_pareven ρ_w_run ρ_w_pareven rfl rfl⟩
    · unfold StutterEquivalent
      use wb, f, f'
      exact ⟨subset_w_eq_functiononword ρ_w_run ρ_w_pareven rfl, rfl⟩
  · intro hwinlang
    rw [StutterClosure] at hwinlang
    apply Membership.mem.out at hwinlang
    rcases hwinlang with ⟨w', ⟨hw'inlang, ⟨wb, f, f', hwb⟩⟩⟩
    rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
    rcases hw'inlang with ⟨ρ_w', ⟨ρ_w'_run , ρ_w'_pareven⟩⟩
    let ρ_wb := supset_rhowb ρ_w' f';
    have ρ_wb_run := supset_rhowb_run ρ_w'_run hwb.2
    have ρ_wb_pareven := supset_rhowb_pareven w f  ρ_w'_run ρ_w'_pareven hwb.2
    use supset_rhow ρ_wb ρ_w' w f f'
    exact ⟨supset_rhow_run hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run,
          supset_rhow_pareven hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run⟩

end Automata
