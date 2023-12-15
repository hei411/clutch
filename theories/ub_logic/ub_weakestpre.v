From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext NNRbar.
From clutch.prob Require Export couplings distribution union_bounds.
From clutch.program_logic Require Export exec language.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.


Import uPred.

Local Open Scope NNR_scope.

(** [irisGS] specifies the interface for the resource algebras implementing the
    [state] and [cfg] of a [language] [Λ]. For the purposes of defining the
    weakest precondition, we only need [irisGS] to give meaning to invariants,
    and provide predicates describing valid states via [state_interp].
    Here [err_interp] is a resource tracking an upper bound on the probability of
    error (i.e. terminating in a state that does not satisfy the postcondition)
 *)
Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(* TODO: upstream? *)
Lemma least_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)) n :
  (∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2,
  x1 ≡{n}≡ x2 → bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2.
Proof.
  intros HF x1 x2 Hx. rewrite /bi_least_fixpoint /=.
  do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
Qed.



(** * The union bound modality [exec_ub]  *)
Section exec_ub.
  Context `{!irisGS Λ Σ}.


  Definition exec_ub_pre (Z : nonnegreal -> cfg Λ → iProp Σ) (Φ : nonnegreal * cfg Λ → iProp Σ) :=
    (λ (x : nonnegreal * cfg Λ),
      let '(ε, (e1, σ1)) := x in
      (* [prim_step] *)
      (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ε2 ρ2 ) ∨
      (* [prim_step] with adv composition *)
      (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2) ρ2 ) ∨
      (* [state_step]  *)
      ([∨ list] α ∈ get_active σ1,
      (* We allow an explicit weakening of the grading, but maybe it is not needed *)
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ ub_lift (state_step σ1 α) R ε1 ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ Φ (ε2,((e1, σ2)))))
    )%I.

  (* TODO: Define this globally, it appears in error credits too *)
  Canonical Structure NNRO := leibnizO nonnegreal.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (exec_ub_pre Z Φ).
  Proof.
    rewrite /exec_ub_pre.
    intros n (?&(?&?)) (?&(?&?)) [ [=] [[=] [=]]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_ub_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_ub_pre.
    iIntros ((ε&(e1 & σ1))) "Hexec".
    iDestruct "Hexec" as "[H | [H | H]]".
    - by iLeft.
    - by iRight; iLeft.
    - iRight; iRight.
      iInduction (get_active σ1) as [| l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[(% & % & % & %Hsum & Hlift & HΦ) | H]".
      + iLeft. iExists R2.
        iExists ε1. iExists _.
        iSplit; [try done|].
        iSplit; [try done|].
        iIntros. iApply "Hwand". by iApply "HΦ".
      + iRight. by iApply "IH".
  Qed.

  Definition exec_ub' Z := bi_least_fixpoint (exec_ub_pre Z).
  Definition exec_ub e σ Z ε := exec_ub' Z (ε, (e, σ)).

  Lemma exec_ub_unfold e1 σ1 Z ε :
    exec_ub e1 σ1 Z ε ≡
      ((∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ε2 ρ2 ) ∨
      (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2) ρ2 ) ∨
      ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ ub_lift (state_step σ1 α) R ε1 ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_ub e1 σ2 Z ε2 )))%I.
  Proof. rewrite /exec_ub/exec_ub' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).


  Lemma exec_ub_mono_grading e1 σ1 (Z : nonnegreal -> cfg Λ → iProp Σ) (ε ε' : nonnegreal) :
    ⌜(ε <= ε')%R⌝ -∗
    exec_ub e1 σ1 Z ε -∗ exec_ub e1 σ1 Z ε'.
  Proof.
    iIntros "Hleq H_ub". iRevert "Hleq".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, ∀ (ε'' : nonnegreal), ((⌜(x.1 <= ε'' )%R⌝ -∗ (bi_least_fixpoint (exec_ub_pre Z) (ε'', x.2)))))%I : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [ [=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (exec_ub_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([ε'' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & % & H) | [ (% & % & % & % & % & % & H) | H] ] %ε3 %Hleq' /="; simpl in Hleq'.
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _,_,_.
      iSplit; [|done].
      iPureIntro; etrans; done.
    - rewrite least_fixpoint_unfold.
      iRight;iLeft. iExists _,_,_.
      iSplit; [|iSplit; [| iSplit]].
      1,3,4:done.
      iPureIntro; etrans; done.
    - rewrite least_fixpoint_unfold.
      iRight; iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq2 & %Hub & H)) | Ht]".
      + iLeft.
        iExists R2. iExists ε1. iExists ε2.
        iSplit; [ iPureIntro; lra | ].
        iSplit; [ done | ].
        iIntros.
        iApply ("H" with "[//]").
        iPureIntro. simpl; lra.
      + iRight. by iApply ("IH" with "Ht").
  Qed.


  Lemma exec_ub_strong_mono e1 σ1 (Z1 Z2 : nonnegreal -> cfg Λ → iProp Σ) (ε ε' : nonnegreal) :
    ⌜(ε <= ε')%R⌝ -∗
    (∀ e2 σ2 ε'', (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 ε'' (e2, σ2) -∗ Z2 ε'' (e2, σ2))) -∗
    exec_ub e1 σ1 Z1 ε -∗ exec_ub e1 σ1 Z2 ε'.
  Proof.
    iIntros "%Hleq HZ H_ub".
    iApply exec_ub_mono_grading; auto.
    iRevert "HZ".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x,(∀ e2 σ2 ε'', ⌜∃ σ, (prim_step x.2.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 ε'' (e2, σ2) -∗ Z2 ε'' (e2, σ2)) -∗
                  (bi_least_fixpoint (exec_ub_pre Z2) x ))%I : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([ε'' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & % & % & H) | [ (% & % & % & % & % & % & H) | H] ] HZ /=".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _,_,_.
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        by apply ub_lift_pos_R. }
      iIntros ([] (?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight; iLeft.
      iExists _,_,_.
      iSplit; [done|].
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        by apply ub_lift_pos_R. }
      iIntros ([] (?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight; iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (% & % & H)) | Ht]".
      + iLeft. iExists R2. iExists ε1. iExists ε2.
        iSplit; [iPureIntro; lra | ].
        iSplit; [done | ].
        iIntros.
        by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_mono (Z1 Z2 : nonnegreal -> cfg Λ → iProp Σ) e1 σ1 (ε1 ε2 : nonnegreal) :
    ⌜(ε1 <= ε2)%R⌝ -∗ (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ exec_ub e1 σ1 Z1 ε1 -∗ exec_ub e1 σ1 Z2 ε2.
  Proof.
    iIntros "%Hleq HZ". iApply exec_ub_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_mono_pred (Z1 Z2 : nonnegreal -> cfg Λ → iProp Σ) e1 σ1 (ε : nonnegreal) :
    (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ exec_ub e1 σ1 Z1 ε -∗ exec_ub e1 σ1 Z2 ε.
  Proof.
    iIntros "HZ". iApply exec_ub_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_strengthen e1 σ1 (Z : nonnegreal -> cfg Λ → iProp Σ) (ε : nonnegreal) :
    exec_ub e1 σ1 Z ε -∗
    exec_ub e1 σ1 (λ ε' '(e2, σ2), ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z ε' (e2, σ2)) ε.
  Proof.
    iApply exec_ub_strong_mono; [iPureIntro; lra | ].
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma exec_ub_bind K `{!LanguageCtx K} e1 σ1 (Z : nonnegreal -> cfg Λ → iProp Σ) (ε : nonnegreal) :
    to_val e1 = None →
    exec_ub e1 σ1 (λ ε' '(e2, σ2), Z ε' (K e2, σ2)) ε -∗ exec_ub (K e1) σ1 Z ε.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, ⌜to_val x.2.1 = None⌝ -∗
                     bi_least_fixpoint (exec_ub_pre Z) (x.1, (K x.2.1, x.2.2)))%I
           : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_ub_pre (λ ε' '(e2, σ2), Z ε' (K e2, σ2))) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (_, (_, _)) with "Hub [//]"). }
    iIntros "!#" ([ε' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & % & % & H) | [ (% & % & % & (%r & %Hr) & % & % & H) | H]] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. simpl.
      iExists (λ '(e2, σ2), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2)),_,_.
      iSplit; [done|].
      rewrite fill_dmap //=.
      iSplit.
      { iPureIntro.
        rewrite <- Rplus_0_r.
        eapply (ub_lift_dbind _ _ R2).
        - eapply ub_nonneg_grad; eauto.
        - lra.
        - intros [] ?? =>/=.
          apply ub_lift_dret.
          eauto.
        - auto.
       }
      iIntros ([] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold.
      iRight; iLeft. simpl.
      destruct (partial_inv_fun K) as (Kinv & HKinv).
      assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
      assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
      assert (forall e, Kinv (K e) = Some e) as HKinv3.
      { intro e.
        destruct (Kinv (K e)) eqn:H3.
        - apply HKinv1 in H3. f_equal. by apply fill_inj.
        - eapply (HKinv2 _ e) in H3. done. }
      set (ε3 := (λ '(e,σ), from_option (λ e', ε2 (e',σ)) nnreal_zero (Kinv e))).
      assert (forall e2 σ2, ε3 (K e2, σ2) = ε2 (e2, σ2)) as Haux.
      {
        intros e2 σ2.
        rewrite /ε3 HKinv3 //.
      }
      iExists (λ '(e2, σ2), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2)),_,ε3.
      iSplit.
      {
        iPureIntro. exists r. intros (e&σ). rewrite /ε3.
        destruct (Kinv e); simpl; try real_solver.
        etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
      }
      iSplit; [ | iSplit].
      2:{ iPureIntro.
        rewrite <- Rplus_0_r.
        rewrite fill_dmap //=.
        eapply (ub_lift_dbind _ _ R2).
        - eapply ub_nonneg_grad; eauto.
        - lra.
        - intros [] ?? =>/=.
          apply ub_lift_dret.
          eauto.
        - auto.
       }
      + iPureIntro.
        etrans; [ | apply H0].
        apply Rplus_le_compat_l.
        transitivity (SeriesC (λ '(e,σ), (prim_step (K o) σ' (K e, σ) * ε3 (K e, σ))%R)).
        * etrans; [ | eapply (SeriesC_le_inj _ (λ '(e,σ), (Kinv e ≫= (λ e', Some (e',σ)))))].
          ** apply SeriesC_le.
             *** intros (e & σ); simpl; split.
                 **** apply Rmult_le_pos; auto.
                      apply cond_nonneg.
                 **** destruct (Kinv e) eqn:He; simpl.
                      ***** rewrite (HKinv1 _ _ He).
                            rewrite He /from_option //.
                      ***** destruct (decide (prim_step (K o) σ' (e, σ) > 0)%R) as [Hgt | Hngt].
                            -- epose proof (fill_step_inv _ _ _ _ _ Hgt) as (e2' & (H3&?)).
                               by destruct (HKinv2 e e2' He).
                            --  apply Rnot_gt_le in Hngt.
                                assert (prim_step (K o) σ' (e, σ) = 0); [by apply Rle_antisym | ].
                                lra.
            *** apply (ex_seriesC_le _ (λ '(e, σ), (prim_step (K o) σ' (e, σ) * ε3 (e, σ))%R)).
                **** intros (e & σ); simpl; split.
                     ***** destruct (Kinv e); simpl; try lra.
                           apply Rmult_le_pos; auto.
                           destruct (Kinv _); simpl; try lra.
                           apply cond_nonneg.
                     ***** destruct (Kinv e) eqn:He; simpl; try real_solver.
                           rewrite HKinv3 /= (HKinv1 _ _ He) //.
                **** apply (ex_seriesC_le _ (λ ρ, ((prim_step (K o) σ' ρ ) * r)%R)); [ | apply ex_seriesC_scal_r; auto].
                     intros (e&σ); split.
                     ***** apply Rmult_le_pos; auto.
                           apply cond_nonneg.
                     ***** rewrite /ε3. destruct (Kinv e); simpl; try real_solver.
                           apply Rmult_le_compat_l; auto.
                           etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
         ** intros [].
            apply Rmult_le_pos; auto.
            apply cond_nonneg.
         ** intros (e3&σ3) (e4&σ4) (e5&σ5) ? ?.
            destruct (Kinv e3) eqn:He3; destruct (Kinv e4) eqn:He4; simpl in *; simplify_eq.
            f_equal; auto.
            rewrite -(HKinv1 _ _ He3).
            by rewrite -(HKinv1 _ _ He4).
         ** apply (ex_seriesC_le _ (λ '(e, σ), ((prim_step (K o) σ' (K e, σ)) * r)%R)).
            *** intros (e&σ); split.
                **** apply Rmult_le_pos; auto.
                     apply cond_nonneg.
                **** rewrite /ε3 HKinv3 /=. real_solver.
            *** apply (ex_seriesC_ext (λ ρ, ((prim_step o σ' ρ) * r)%R)); auto.
                **** intros []. apply Rmult_eq_compat_r. by apply fill_step_prob.
                **** by apply ex_seriesC_scal_r.
        * right. apply SeriesC_ext.
          intros (e&σ).
          rewrite Haux.
          f_equal; auto.
          symmetry; by apply fill_step_prob.
      + iIntros ([] (? & -> & ?)).
        iMod ("H" with "[//]").
        by rewrite Haux.
       Unshelve. auto.
    - rewrite least_fixpoint_unfold /=.
      iRight; iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq & %Hub & H)) | Ht]".
      + iLeft.
        iExists _,_,_.
        iSplit; [done|].
        iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_prim_step e1 σ1 Z (ε : nonnegreal) :
    (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
          ∀ ρ2 , ⌜R ρ2⌝ ={∅}=∗ Z ε2 ρ2)
    ⊢ exec_ub e1 σ1 Z ε.
  Proof.
    iIntros "(% & % & % & % & % & H)".
    rewrite {1}exec_ub_unfold.
    iLeft.
    iExists _,_,_.
    iSplit; [done|].
    iSplit; done.
  Qed.


  Lemma exec_ub_adv_comp e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2) ρ2 )
    ⊢ exec_ub e1 σ1 Z ε.
  Proof.
    iIntros "(% & % & % & % & % & % & H)".
    rewrite {1}exec_ub_unfold.
    iRight; iLeft.
    iExists _,_,_.
    iSplit; [done|].
    iSplit; [done|].
    iSplit; done.
  Qed.


  Lemma exec_ub_adv_comp' e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) = ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R nnreal_zero⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2) ρ2 )
    ⊢ exec_ub e1 σ1 Z ε.
  Proof.
    iIntros "(% & % & % & %Hε & % & H)".
    rewrite {1}exec_ub_unfold.
    iRight; iLeft.
    iExists _,nnreal_zero,_.
    iSplit; [done|].
    iSplit.
    { iPureIntro.
      simpl. rewrite Hε. lra.
    }
    iSplit; done.
  Qed.

  (* TODO: Maybe allow weakening of the grading *)
  Lemma exec_ub_state_step α e1 σ1 Z (ε ε' : nonnegreal) :
    α ∈ get_active σ1 →
    (∃ R, ⌜ub_lift (state_step σ1 α) R ε⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ exec_ub e1 σ2 Z ε')
    ⊢ exec_ub e1 σ1 Z (ε + ε').
  Proof.
    iIntros (?) "H".
    iDestruct "H" as (?) "H".
    rewrite {1}exec_ub_unfold.
    iRight; iRight.
    iApply big_orL_elem_of; eauto.
    iExists R2.
    iExists ε.
    iExists ε'.
    iFrame.
    iPureIntro.
    simpl. lra.
  Qed.
 
(*
  Lemma exec_ub_reducible e σ Z1 Z2 ε1 ε2 :
    (exec_ub e σ Z1 ε1)  ={∅}=∗ ⌜irreducible e σ⌝ -∗ (exec_ub e σ Z2 ε2).
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜irreducible x.2.1 x.2.2⌝ -∗ (exec_ub x.2.1 x.2.2 Z2 ε2))%I : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto;
    rewrite /Φ/=.
    - iModIntro.
      iIntros.
      exfalso.
      pose proof (not_reducible e1 σ1) as (H3 & H4).
      by apply H4.
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜irreducible e1 σ1⌝ -∗ exec_ub e1 σ1 Z2 ε2)%I  with "H") as "H".
      { intros.
        iIntros.
        iModIntro.
        iIntros.
        rewrite exec_ub_unfold.
        iRight.
        iApply (big_orL_elem_of _ _ y).
        - eapply elem_of_list_lookup_2; eauto.
        -
*)

(*
  Lemma exec_ub_irreducible e σ Z ε :
    ⌜irreducible e σ⌝ ⊢ exec_ub e σ Z ε.
  Proof.
    iIntros "H".
    rewrite {1}exec_ub_unfold.
    iRight.
    iInduction (get_active σ) as [| l] "IH".
    { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq & %Hub & H)) | Ht]".
*)

  (* This lemma might not be true anymore *)
  (*
  Lemma exec_ub_reducible e σ Z ε :
    exec_ub e σ Z ε ={∅}=∗ ⌜reducible e σ⌝.
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜reducible x.2.1 x.2.2⌝)%I : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto.
    rewrite /Φ/=.
    Search "big_orL".
    iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? α' ?%elem_of_list_lookup_2) "(%R2 & %ε1 & %ε2 & %Hleq & %Hub & H)".
        eapply ub_lift_pos_R in Hub.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 & [] & ? & ? & ?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? [α1 α2] [? ?]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 &?&?& Hs &?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
  Qed.
  *)

  (*
  Lemma exec_coupl_det_r n e1 σ1 e1' σ1' e2' σ2' Z :
    exec n (e1', σ1') (e2', σ2') = 1 →
    exec_coupl e1 σ1 e2' σ2' Z -∗
    exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "Hcpl".
    iApply exec_coupl_exec_r.
    iExists _, n. iSplit.
    { iPureIntro. apply Rcoupl_pos_R, Rcoupl_trivial.
      - apply dret_mass.
      - rewrite Hexec; apply dret_mass. }
    iIntros (e2'' σ2'' (_ & _ & H)).
    rewrite Hexec in H. by apply dret_pos in H as [= -> ->].
  Qed.
  *)

End exec_ub.


Section exec_ub_limit.
  Context `{!irisGS Λ Σ}.

  Local Lemma inf_seq_nonnegreal_nonneg (f:nat -> nonnegreal): 0<=Inf_seq f.
  Proof.
    rewrite Inf_opp_sup Rbar_opp_real.
    apply Ropp_0_ge_le_contravar.
    apply Rle_ge.
    replace 0 with (real (Finite 0)); last done.
    apply finite_rbar_le.
    + eapply (is_finite_bounded (- (f 0%nat)) 0).
      -- eapply (Sup_seq_minor_le _ _ 0%nat).
         rewrite /nonneg. simpl. destruct (f 0%nat). done.
      -- apply upper_bound_ge_sup. intros. rewrite /nonneg.
         destruct (f n) as [x Hx].
         apply Ropp_le_contravar in Hx.
         replace (-0) with 0 in Hx; try done.
         lra.
    + apply upper_bound_ge_sup. intros. rewrite /nonneg.
      destruct (f n) as [x Hx].
      apply Ropp_le_contravar in Hx.
      replace (-0) with 0 in Hx; try done.
      lra.
  Qed.

  Program Definition Inf_seq_nnr (f : nat -> nonnegreal) := mknonnegreal (Inf_seq f) _.
  Next Obligation.
    apply inf_seq_nonnegreal_nonneg.
  Qed.

  Definition exec_ub_limit_pre (Z : nonnegreal -> cfg Λ → iProp Σ) (Φ : nonnegreal * cfg Λ → iProp Σ) :=
    (λ (x : nonnegreal * cfg Λ),
       let '(ε, (e1, σ1)) := x in
       (* [prim_step] *)
       (∃ R (ε1 ε2 : nat -> nonnegreal), ⌜ (Inf_seq_nnr ε1 + Inf_seq_nnr ε2 <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (prim_step e1 σ1) R (ε1 n)⌝ ∗ ∀ ρ2 n, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 n) ρ2 ) ∨
         (* [prim_step] with adv composition *)
         (∃ R (ε1 : nat -> nonnegreal) (ε2 : cfg Λ -> nat -> nonnegreal),
             ⌜∃ r, ∀ n ρ, (ε2 ρ n <= r)%R ⌝ ∗ ⌜ (Inf_seq_nnr ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * Inf_seq_nnr (ε2 ρ)) <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (prim_step e1 σ1) R (ε1 n)⌝ ∗
                                                                                                                                         ∀ ρ2 n, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2 n) ρ2 ) ∨
         (* [state_step]  *)
         ([∨ list] α ∈ get_active σ1,
            (* We allow an explicit weakening of the grading, but maybe it is not needed *)
            (∃ R (ε1 ε2 : nat -> nonnegreal), ⌜ (Inf_seq_nnr ε1 + Inf_seq_nnr ε2 <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (state_step σ1 α) R (ε1 n) ⌝ ∗ ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ Φ (Inf_seq_nnr ε2,((e1, σ2)))))
    )%I.

  Local Instance exec_state_ub_limit_pre_NonExpansive Z Φ :
    NonExpansive (exec_ub_limit_pre Z Φ).
  Proof.
    rewrite /exec_ub_limit_pre.
    intros n [?[??]] [?[??]] [[=][[=][=]]].
    by subst.
  Qed.

  Local Instance exec_coupl_limit_pre_mono Z : BiMonoPred (exec_ub_limit_pre Z).
  Proof.
    split; last apply _.
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_ub_limit_pre.
    iIntros ([ε[e σ]]) "Hexec".
    iDestruct "Hexec" as "[H|[H|H]]".
    - by iLeft.
    - by iRight; iLeft.
    - iRight. iRight.
      iInduction (get_active σ) as [|l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[H|H]".
      + iLeft. 
        iDestruct "H" as "[%R H]".
        iExists R.
        iDestruct "H" as "(%&%&%&%&H)".
        iExists _, _. iSplitR; [done|].
        iSplitR; [done|].
        iIntros. iApply "Hwand". by iApply "H".
      + iRight. by iApply "IH".
  Qed.

  
  Definition exec_ub_limit' Z := bi_least_fixpoint (exec_ub_limit_pre Z).
  Definition exec_ub_limit e σ Z ε := exec_ub_limit' Z (ε, (e, σ)).

  
  Lemma exec_ub_limit_unfold e1 σ1 Z ε :
    exec_ub_limit e1 σ1 Z ε ≡
      ((* [prim_step] *)
        (∃ R (ε1 ε2 : nat -> nonnegreal), ⌜ (Inf_seq_nnr ε1 + Inf_seq_nnr ε2 <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (prim_step e1 σ1) R (ε1 n)⌝ ∗ ∀ ρ2 n, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 n) ρ2 ) ∨
          (* [prim_step] with adv composition *)
          (∃ R (ε1 : nat -> nonnegreal) (ε2 : cfg Λ -> nat -> nonnegreal),
              ⌜∃ r, ∀ n ρ, (ε2 ρ n <= r)%R ⌝ ∗
                          ⌜ (Inf_seq_nnr ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * Inf_seq_nnr (ε2 ρ)) <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (prim_step e1 σ1) R (ε1 n)⌝ ∗ ∀ ρ2 n, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2 n) ρ2 ) ∨
          (* [state_step]  *)
          ([∨ list] α ∈ get_active σ1,
             (* We allow an explicit weakening of the grading, but maybe it is not needed *)
             (∃ R (ε1 ε2 : nat -> nonnegreal), ⌜ (Inf_seq_nnr ε1 + Inf_seq_nnr ε2 <= ε)%R ⌝ ∗ ⌜∀ n, ub_lift (state_step σ1 α) R (ε1 n) ⌝ ∗ ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_ub_limit e1 σ2 Z (Inf_seq_nnr ε2)  )))%I.
  Proof.  rewrite /exec_ub_limit/exec_ub_limit' least_fixpoint_unfold //. Qed.

  
  

  Local Lemma inf_seq_exists_index (f:nat -> nonnegreal) ε:
    Inf_seq (λ x : nat, f x) < ε -> ∃ n : nat, f n < ε.
  Proof.
    intros H.
    pose proof Sup_seq_minor_lt as Hexist.
    assert (exists n, Rbar_lt (-ε) ((λ x, -(f x)) n)) as H0; last first.
    { destruct H0 as [n H0]. exists n. apply Ropp_lt_cancel. apply H0. }
    rewrite -Hexist.
    apply Ropp_lt_contravar in H.
    rewrite Inf_opp_sup in H.
    rewrite Rbar_opp_real in H.
    rewrite Ropp_involutive in H.
    assert ((Sup_seq (fun n : nat => Rbar_opp (Finite (nonneg (f n))))) =
            (Sup_seq (fun n : nat => Finite (Ropp (nonneg (f n)))))) as Hr by f_equal.
    simpl.
    assert (is_finite (Sup_seq (λ n, - f n))) as Hfinite.
    { apply (is_finite_bounded (- f 0%nat) 0).
        -- etrans; last apply sup_is_upper_bound. done.
        -- apply upper_bound_ge_sup. intros. apply Ropp_le_cancel.
           rewrite Ropp_involutive. replace (-_) with 0 by lra.
           destruct (f n). eauto.
    }
    case_match; [|done|].
    - symmetry in H0. apply eq_rbar_finite in H0. subst. rewrite rbar_finite_real_eq in Hr.
      + apply H.
      + apply (is_finite_bounded (- f 0%nat) 0).
        -- etrans; last apply sup_is_upper_bound. done.
        -- apply upper_bound_ge_sup. intros. apply Ropp_le_cancel.
           rewrite Ropp_involutive. replace (-_) with 0 by lra.
           destruct (f n). eauto.
    - done.
  Qed. 
 
  
  Lemma exec_ub_limit_implies_exec_ub e σ Z ε :
    □(∀ ε1 ε2 s, ⌜ε1<ε2⌝ -∗ Z ε1 s -∗ Z ε2 s) -∗
    □(∀ ε1 s, (∀ ε2, ⌜ε1<ε2⌝ ={∅}=∗ Z ε2 s) ={∅}=∗ Z ε1 s) -∗
    exec_ub_limit e σ Z ε -∗ exec_ub e σ Z ε.
  Proof.
    rewrite /exec_ub_limit/exec_ub_limit'/exec_ub/exec_ub'.
    iIntros "#Hmonotone #Hcontinuous Hlimit".
    iApply least_fixpoint_iter; last iExact "Hlimit".
    iModIntro.
    clear e σ ε.
    iIntros ([ε [e1 σ1]]).
    iIntros "H".
    iAssert (exec_ub e1 σ1 Z ε) with "[H]" as "H".
    2: { rewrite /exec_ub/exec_ub'. done. }
    rewrite exec_ub_unfold.
    iDestruct "H" as "[H|[H|H]]".
    - iLeft. iDestruct "H" as "[%R H]".
      iExists R. iDestruct "H" as "(%ε1 & %ε2 & %Hε & %Hstep &H)".
      iExists (Inf_seq_nnr ε1), (Inf_seq_nnr ε2).
      iSplitR.
      { done. }
      iSplitR.
      { iPureIntro.
        apply ub_lift_epsilon_limit.
        + apply Rle_ge. apply inf_seq_nonnegreal_nonneg.
        + intros.
          assert (∃ n, ε1 n < ε0) as [n Hn].
          { apply inf_seq_exists_index. simpl in H. lra.  }
          eapply UB_mon_grading; [|done].
          apply Rlt_le. done.
      }
      iIntros ([??]) "%R'".
      iApply "Hcontinuous".
      iIntros (ε') "%Hbound".
      apply inf_seq_exists_index in Hbound as [n Hbound].
      iApply "Hmonotone"; [done|].
      iApply "H". done.
    - iRight; iLeft. iDestruct "H" as "[%R H]".
      iExists R. iDestruct "H" as "(%ε1 & %ε2 & %Hbound1 & %Hbound2 & %Hstep & H)".
      iExists (Inf_seq_nnr ε1), (λ s, (Inf_seq_nnr (ε2 s))).
      simpl.
      assert (∀ s, is_finite (Sup_seq (λ n : nat, Rbar_opp (ε2 s n)))) as Hfinite. 
      { intros s. apply (is_finite_bounded (-ε2 s 0%nat) (0)).
        -  by apply (Sup_seq_minor_le _ _ 0).  
        - apply upper_bound_ge_sup => n. apply Rbar_opp_le.
          rewrite Rbar_opp_involutive.
          destruct (ε2 s n) => /=.
          rewrite Ropp_0. done.
      }
      iSplitR.     
      { destruct Hbound1 as [r Hbound1]. iExists r.
        iPureIntro. intros s.
        rewrite Inf_opp_sup. apply Ropp_le_cancel.
        rewrite Rbar_opp_real.
        rewrite Ropp_involutive.
        rewrite -rbar_le_rle.
        rewrite rbar_finite_real_eq; last done.
        apply (Sup_seq_minor_le _ _ 0). simpl. apply Ropp_le_contravar. eauto. 
      }
      iSplitR.
      { done. }
      iSplitR.
      { iPureIntro. apply ub_lift_epsilon_limit.
        + apply Rle_ge. apply inf_seq_nonnegreal_nonneg.
        + intros r H.
          apply Rgt_lt in H. apply inf_seq_exists_index in H.
          destruct H as [n H].
          eapply (UB_mon_grading _ _ (ε1 n)); [lra|apply Hstep].
      }
      iIntros (s) "%Hr".
      iApply "Hcontinuous".
      iIntros (ε') "%H'".
      apply inf_seq_exists_index in H' as [n H'].
      iApply "Hmonotone"; [done|].
      by iApply "H".
    - iRight; iRight.
      iInduction (get_active σ1) as [|l ls] "IH".
      { by rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons. iDestruct "H" as "[H|H]".
      2: { iRight. by iApply "IH". }
      iLeft.
      iDestruct "H" as "(%R & %ε1 & %ε2 & %Hbound & %Hstep & H)".
      iExists R, (Inf_seq_nnr ε1), (Inf_seq_nnr ε2).
      simpl.
      iSplitR.
      { done. }
      iSplitR.
      { iPureIntro. apply ub_lift_epsilon_limit.
        + apply Rle_ge. apply inf_seq_nonnegreal_nonneg.
        + intros r H.
          apply Rgt_lt in H. apply inf_seq_exists_index in H.
          destruct H as [n H].
          eapply (UB_mon_grading _ _ (ε1 n)); [lra|apply Hstep].
      }
      iIntros (s) "%Hr".
      by iApply "H".
  Qed.
  
  Lemma exec_ub_implies_exec_ub_limit e σ Z ε :
    exec_ub e σ Z ε -∗ exec_ub_limit e σ Z ε.
  Proof.
    rewrite /exec_ub/exec_ub'/exec_ub_limit/exec_ub_limit'.
    iIntros "Hlimit".
    iApply (least_fixpoint_strong_mono with "[][$Hlimit]").
    { apply exec_coupl_pre_mono. }
    iModIntro.
    clear e σ ε.
    iIntros (Φ [ε [e1 σ1]]).
    rewrite /exec_ub_limit_pre/exec_ub_pre.
    iIntros "[H|[H|H]]".
    - iLeft. iDestruct "H" as "(%R & %ε1 & %ε2 & %Hε & %Hub & H)".
      iExists R, (λ _, ε1), (λ _, ε2).
      iSplitR.
      { iPureIntro; rewrite !Inf_opp_sup !Rbar_opp_real !sup_seq_const.
        lra.
      }
      iSplitR.
      { iPureIntro; by intros. }
      iIntros. by iApply "H".
    - iRight; iLeft. iDestruct "H" as "(%R & %ε1 & %ε2 & %Hbound & %Hε & %Hub & H)".
      iExists R, (λ _, ε1), (λ s _, ε2 s).
      iSplitR.
      { iPureIntro. destruct Hbound as [r Hbound]. exists r.
        intros. rewrite !Inf_opp_sup !Rbar_opp_real !sup_seq_const.
        replace (--_) with (nonneg (ε2 ρ)) by lra.
        eauto.
      }
      iSplitR.
      { iPureIntro. erewrite SeriesC_ext; last first.
        - intros. rewrite !Inf_opp_sup !Rbar_opp_real !sup_seq_const.
          replace (--_) with (nonneg (ε2 n)) by lra.
          done.
        - rewrite !Inf_opp_sup !Rbar_opp_real !sup_seq_const.
          lra.
      }
      iSplitR.
      { iPureIntro; eauto. }
      iIntros; by iApply "H".
    - iRight; iRight.
      iInduction (get_active σ1) as [|l] "IH".
      { by rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons. iDestruct "H" as "[H|H]".
      + iLeft. iDestruct "H" as "(%R & %ε1 & %ε2 & %Hε & %Hstate & H)".
        iExists R, (λ _, ε1), (λ _, ε2).
        iSplitR.
        { iPureIntro. rewrite !Inf_opp_sup !Rbar_opp_real !sup_seq_const.
          lra.
        }
        iSplitR.
        { iPureIntro. by intros. }
        iIntros. by iApply "H".
      + iRight. by iApply "IH".
  Qed. 
    
End exec_ub_limit.
          


(** * The weakest precondition  *)
Definition ub_wp_pre `{!irisGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ε,
      state_interp σ1 ∗ err_interp ε ={E,∅}=∗
      ⌜reducible e1 σ1⌝ ∗
      exec_ub e1 σ1 (λ ε2 '(e2, σ2),
        ▷ |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ wp E e2 Φ) ε
end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} : Contractive (ub_wp_pre).
Proof.
  rewrite /ub_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 8 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [ε' [e' σ']]. rewrite /exec_ub_pre.
  do 14 f_equiv.
  { f_contractive. do 3 f_equiv. apply Hwp. }
  { do 2 f_equiv. f_contractive. do 3 f_equiv. apply Hwp. }
Qed.


(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition ub_wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (ub_wp_pre); wp_default := () |}.
Local Definition ub_wp_aux : seal (@ub_wp_def). Proof. by eexists. Qed.
Definition ub_wp' := ub_wp_aux.(unseal).
Global Arguments ub_wp' {Λ Σ _}.
Global Existing Instance ub_wp'.
Local Lemma ub_wp_unseal `{!irisGS Λ Σ} : wp = (@ub_wp_def Λ Σ _).(wp).
Proof. rewrite -ub_wp_aux.(seal_eq) //. Qed.

Section ub_wp.
Context `{!irisGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types ε : R.

(* Weakest pre *)
Lemma ub_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ ub_wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite ub_wp_unseal. apply (fixpoint_unfold (ub_wp_pre)). Qed.

Global Instance ub_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? []]. rewrite /exec_ub_pre.
  do 14 f_equiv.
  { f_contractive. do 3 f_equiv. rewrite IH; [done|lia|].
    intros ?. eapply dist_S, HΦ. }
  { do 2 f_equiv. f_contractive. rewrite IH; [done|lia|].
    intros ?. eapply dist_S, HΦ. }
Qed.

Global Instance ub_wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ub_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance ub_wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !ub_wp_unfold /ub_wp_pre He /=.
  do 7 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? []]. rewrite /exec_ub_pre.
  do 14 f_equiv.
  { f_contractive. do 6 f_equiv. }
  { do 2 f_equiv. f_contractive. do 6 f_equiv. }
Qed.

Lemma ub_wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite ub_wp_unfold /ub_wp_pre to_of_val. auto. Qed.

Lemma ub_wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro.
  iSplit; [done | ].
  iApply (exec_ub_mono_pred with "[Hclose HΦ] H").
  iIntros (? [e2 σ2]) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_ub_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite ub_wp_unfold /ub_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ε) "Hi". iMod "H". by iApply "H".
Qed.
Lemma ub_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (ub_wp_strong_mono E with "H"); auto. Qed.

Lemma ub_wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ε) "[Hσ Hε]". iMod "H".
  iMod ("H" with "[$]") as "[$ H]".
  iModIntro.
  iDestruct (exec_ub_strengthen with "H") as "H".
  iApply (exec_ub_mono_pred with "[] H").
  iIntros (? [e2 σ2]) "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  - iDestruct "H" as ">> $". by iFrame.
  - iMod ("H" with "[$]") as "(%&H)".
    pose proof (atomic σ e2 σ2 Hstep) as H3.
    case_match.
    + rewrite /is_Some in H3.
      destruct H3.
      simplify_eq.
    + apply not_reducible in H3.
      done.
Qed.


Lemma ub_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !ub_wp_unfold /ub_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 ε) "[Hσ Hε]". iMod "HR".
  iMod ("H" with "[$Hσ $Hε]") as "[% H]".
  iModIntro.
  iSplit; [done | ].
  iApply (exec_ub_mono_pred with "[HR] H").
  iIntros (? [e2 σ2]) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iMod "HR".
  iFrame "Hσ Hρ".
  iApply (ub_wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma ub_wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_ub_wp. }
  rewrite ub_wp_unfold /ub_wp_pre fill_not_val /=; [|done].
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod ("H" with "[$Hσ $Hε]") as "(%Hs & H)".
  iModIntro.
  iSplit.
  - iPureIntro.
    apply reducible_fill; auto.
  - iApply exec_ub_bind; [done |].
    iApply (exec_ub_mono with "[] [] H").
    + iPureIntro; lra.
    + iIntros (? [e2 σ2]) "H".
      iModIntro.
      iMod "H" as "(Hσ & Hρ & H)".
      iModIntro.
      iFrame "Hσ Hρ". by iApply "IH".
Qed.

(* Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ : *)
(*   WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}. *)
(* Proof. *)
(*   iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. } *)
(*   rewrite fill_not_val //. *)
(*   iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]". *)
(*   iModIntro; iSplit. *)
(*   { destruct s; eauto using reducible_fill_inv. } *)
(*   iIntros (e2 σ2 efs Hstep) "Hcred". *)
(*   iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step. *)
(*   iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). *)
(*   iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH". *)
(* Qed. *)

(** * Derived rules *)
Lemma ub_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (ub_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma ub_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ub_wp_strong_mono with "H"); auto. Qed.
Global Instance ub_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.
Global Instance ub_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.

Lemma ub_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply ub_wp_value_fupd'. Qed.
Lemma ub_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite ub_wp_value_fupd'. auto. Qed.
Lemma ub_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply ub_wp_value'. Qed.

Lemma ub_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma ub_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma ub_wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (ub_wp_step_fupd with "Hu"); try done.
  iApply (ub_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma ub_wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply ub_wp_frame_step_l.
Qed.
Lemma ub_wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma ub_wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma ub_wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (ub_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma ub_wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma ub_wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (ub_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End ub_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_ub_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ub_wp_frame_l. apply ub_wp_mono, HR. Qed.

  Global Instance is_except_0_ub_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ub_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_ub_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic WeaklyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r ub_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_ub_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ub_wp. Qed.

  Global Instance elim_acc_ub_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic WeaklyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_ub_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply ub_wp_fupd.
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
