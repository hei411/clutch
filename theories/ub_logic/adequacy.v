From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From Coquelicot Require Import Series Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Import base Coquelicot_ext.

From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.program_logic Require Export language weakestpre.
From clutch.ub_logic Require Import error_credits ub_weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.


Section adequacy.
  Context `{!ub_clutchGS Σ}.


  Lemma ub_lift_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜ub_lift μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply ub_lift_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.


  Lemma ub_lift_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜ub_lift μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T (ε' a)⌝) -∗
    |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. eapply ub_lift_dbind_adv; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_ub_erasure (e : expr) (σ : state) (n : nat) φ (ε : nonnegreal) :
    to_val e = None →
    exec_ub e σ (λ ε' '(e2, σ2),
        |={∅}▷=>^(S n) ⌜ub_lift (exec_val n (e2, σ2)) φ ε'⌝) ε
    ⊢ |={∅}▷=>^(S n) ⌜ub_lift (exec_val (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ '(ε'', (e1, σ1)),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜ub_lift (exec_val (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    set (F := (exec_ub_pre (λ ε' '(e2, σ2),
                   |={∅}▷=>^(S n) ⌜ub_lift (exec_val n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([ε'' [e1 σ1]]). rewrite /Φ/F/exec_ub_pre.
    iIntros "[ (%R & %ε1 & %ε2 & % & %Hlift & H)| [ (%R & %ε1 & %ε2 & (%r & %Hr) & % & %Hlift & H)| H]] %Hv".
    - iApply step_fupdN_mono.
      { apply pure_mono.
        eapply UB_mon_grading; eauto. }
      rewrite exec_val_Sn_not_val; [|done].
      iApply ub_lift_dbind'.
      1,2 : iPureIntro; apply cond_nonneg.
      + done.
      + iIntros ([] ?).
        by iMod ("H"  with "[//]").
    - iApply step_fupdN_mono.
      { apply pure_mono.
        eapply UB_mon_grading; eauto. }
      rewrite exec_val_Sn_not_val; [|done].
      iApply ub_lift_dbind_adv'.
      + iPureIntro; apply cond_nonneg.
      + iPureIntro. exists r. split; auto. apply cond_nonneg.
      + done.
      + iIntros ([] ?).
        by iMod ("H"  with "[//]").
    - rewrite exec_val_Sn_not_val; [|done].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ub_lift (prim_step e1 σ1 ≫= exec_val n) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hleq & %Hlift & H)".
        rewrite -exec_val_Sn_not_val; [|done].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → ub_lift (exec_val (S n) (e1, σ2)) φ ε2 ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          apply (UB_mon_grading _ _ (ε1 + ε2)); [lra | ].
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          eapply ub_lift_dbind; eauto; [apply cond_nonneg | ].
          apply cond_nonneg.
        - iIntros (??). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (ε : nonnegreal) n φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ub_lift (exec_val n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ ε); iIntros "((Hσh & Hσt) & Hε & Hwp)".
    - rewrite /exec_val /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite ub_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        apply (UB_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply ub_lift_dret; auto.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply ub_lift_dzero,
        Rle_ge,
        cond_nonneg.
    - rewrite exec_val_Sn /prim_step_or_val /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite ub_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_val_unfold dret_id_left /=.
        apply (UB_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply ub_lift_dret; auto.
      + rewrite ub_wp_unfold /ub_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "(%Hexec_ub & Hlift)".
        iModIntro.
        iPoseProof
          (exec_ub_mono _ (λ ε' '(e2, σ2), |={∅}▷=>^(S n)
             ⌜ub_lift (exec_val n (e2, σ2)) φ ε'⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros (? []) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        rewrite -exec_val_Sn_not_val; [|done].
        iAssert
          (|={∅}▷=> |={∅}▷=>^n ⌜ub_lift (exec_val (S n) (e, σ)) φ ε⌝)%I
          with "[H]" as "Haux"; last first.
        {  iMod "Haux".
           do 2 iModIntro.
           iMod "Haux".
           iModIntro.
           iApply (step_fupdN_wand with "Haux").
           iPureIntro; done.
         }
        by iApply (exec_ub_erasure with "H").
  Qed.

End adequacy.


Class clutchGpreS Σ := ClutchGpreS {
  clutchGpreS_iris  :> invGpreS Σ;
  clutchGpreS_heap  :> ghost_mapG Σ loc val;
  clutchGpreS_tapes :> ghost_mapG Σ loc tape;
  clutchGpreS_err   :> ecGpreS Σ;
}.

Definition clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR (realUR))].
Global Instance subG_clutchGPreS {Σ} : subG clutchΣ Σ → clutchGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_union_bound Σ `{clutchGpreS Σ} (e : expr) (σ : state) n (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (exec_val n (e, σ)) φ ε.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod ec_alloc as (?) "[? ?]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  iApply Hwp.
  done.
Qed.

Lemma ub_lift_closed_lim (e : expr) (σ : state) (ε : nonnegreal) φ :
  (forall n, ub_lift (exec_val n (e, σ)) φ ε ) ->
  ub_lift (lim_exec_val (e, σ)) φ ε .
Proof.
  intros Hn P HP.
  apply lim_exec_continous_prob; auto.
  intro n.
  apply Hn; auto.
Qed.

Theorem wp_union_bound_lim Σ `{clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec_val (e, σ)) φ ε.
Proof.
  intros.
  apply ub_lift_closed_lim.
  intro n.
  apply (wp_union_bound Σ); auto.
Qed.


(*epsilon limit*)
Lemma ub_lift_epsilon_limit `{Eq: EqDecision A} `{HC:Countable A} (μ : distr A) f : (forall ε, ε>0 -> ub_lift μ f ε) -> ub_lift μ f 0.
Proof.
  intros H.
  assert (forall seq,(∀ n, 0 <= seq n <=1) -> (∀ n, ub_lift μ f (1-seq n))->ub_lift μ f (1-Sup_seq seq)) as H_limit.
  { clear H.
    rewrite /ub_lift.
    intros.
    rewrite Rcomplements.Rle_minus_r.
    rewrite Rplus_comm.
    rewrite -Rcomplements.Rle_minus_r.
    rewrite <- rbar_le_rle.
    rewrite rbar_finite_real_eq.
    + apply upper_bound_ge_sup.
      intros.
      pose proof (H0 n P H1). rewrite rbar_le_rle. lra.
    + apply (is_finite_bounded 0 1).
      -- eapply (Sup_seq_minor_le _ _ 0). destruct (H 0%nat). apply H2. 
      -- apply upper_bound_ge_sup. intros n. destruct (H n). apply H3. 
  }
  replace 0%R with (1-Sup_seq (λ x,(λ n,1-1/(S n)) x)).
  - apply H_limit.
    { intros; split.
      -- apply Rle_0_le_minus. rewrite <-Rcomplements.Rdiv_le_1.
         ++ rewrite S_INR. rewrite <- Rcomplements.Rle_minus_l.
            replace (_-_) with 0; try lra.
            apply pos_INR.
         ++ apply Rcomplements.Rlt_nat. eauto. 
      -- assert (1/S n>=0); try lra.
         apply Rle_ge.
         apply Rcomplements.Rdiv_le_0_compat; try lra.
         apply Rcomplements.Rlt_nat. eauto.
    }
    intros. apply H.
    apply Rgt_minus.
    apply Rlt_gt.
    rewrite Rcomplements.Rlt_minus_l.
    apply Rlt_gt.
    apply Rminus_gt_0_lt.
    replace (_+_-_) with (1/S n); try lra.
    apply Rdiv_lt_0_compat; try lra.
    rewrite S_INR. pose proof pos_INR.
    apply Rplus_le_lt_0_compat; try lra. done.
  - apply Rminus_diag_eq.
    apply eq_rbar_finite.
    admit. 
Admitted.
  

Lemma exec_ub_epsilon_limit `{ub_clutchGS Σ} (e : expr) σ Z:
   (∀ ε : nonnegreal, ⌜ε > 0⌝ -∗ exec_ub e σ Z ε) -∗ exec_ub e σ Z nnreal_zero.
Proof.
  iLöb as "IH" forall (e σ).
  iIntros "H".
  rewrite exec_ub_unfold.
  (* iLöb does not work*)
  Admitted. 

  

Lemma wp_epsilon_limit `{ub_clutchGS Σ} (e : expr) φ:
   (∀ ε : nonnegreal, ⌜0<ε⌝ -∗ € ε -∗ WP e {{ v, ⌜φ v⌝}}) -∗
  WP e {{v, ⌜φ v⌝}}.
Proof.
  iStartProof.
  iLöb as "IH" forall (e).
  iIntros "H".
  iEval (rewrite ub_wp_unfold /ub_wp_pre).
  case_match.
  - iAssert (∀ ε : nonnegreal, ⌜0 < ε⌝ -∗ € ε ={⊤}=∗ ⌜φ v⌝)%I with "[H]" as "H".
    { iIntros (ε) "% Hε".
      iPoseProof ("H" $! ε H1 with "[$Hε]") as "H".
      iEval (rewrite ub_wp_unfold /ub_wp_pre) in "H".
      by iEval (rewrite H0) in "H".
    }
    admit.
  - iAssert (∀ ε : nonnegreal, ⌜0 < ε⌝ -∗ € ε -∗
                              ∀ (σ1 : language.state prob_lang) (ε : nonnegreal),
              state_interp σ1 ∗ err_interp ε ={⊤,∅}=∗
              ⌜reducible e σ1⌝ ∗
              exec_ub e σ1
                (λ (ε2 : nonnegreal) '(e2, σ2),
                   ▷ (|={∅,⊤}=> state_interp σ2 ∗ err_interp ε2 ∗ WP e2 {{ v, ⌜φ v⌝ }})) ε)%I with "[H]"as "H".
    { iIntros (ε) "% Hε".
      iPoseProof ("H" $! ε H1 with "[$Hε]") as "H".
      iEval (rewrite ub_wp_unfold /ub_wp_pre) in "H".
      by rewrite H0.
    }
    iIntros (σ ε) "[Hs Hε]".
    admit. 
Admitted. 
