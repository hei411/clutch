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



Lemma exec_ub_epsilon_limit `{ub_clutchGS Σ} (e : expr) σ Z (ε':nonnegreal):
   (∀ ε : nonnegreal, ⌜ε > ε'⌝ -∗ exec_ub e σ Z ε) -∗ exec_ub e σ Z ε'.
Proof.
  rewrite /exec_ub /exec_ub'.
  iIntros "H".
  iApply least_fixpoint_unfold_2; [apply exec_coupl_pre_mono|].
  (* iLöb does not work*)
Abort.



Section Experiment_exec_ub_no_chain.

  Definition exec_ub_no_chain_case_1 `{!ub_clutchGS Σ} (Z : nonnegreal -> cfg -> iProp Σ) ε e σ :=
    (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e σ) R ε1⌝ ∗
                                    ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ε2 ρ2 )%I.
    
  Definition exec_ub_no_chain_case_2 `{!ub_clutchGS Σ} (Z : nonnegreal -> cfg -> iProp Σ) ε e σ :=
    (∃ R (ε1 : nonnegreal) (ε2 : cfg -> nonnegreal),
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
                    ⌜ (ε1 + SeriesC (λ ρ, (prim_step e σ ρ) * ε2(ρ)) <= ε)%R ⌝ ∗
                    ⌜ub_lift (prim_step e σ) R ε1⌝ ∗ ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z (ε2 ρ2) ρ2 )%I.
  
  Definition exec_ub_no_chain `{!ub_clutchGS Σ} (Z : nonnegreal -> cfg → iProp Σ) :=
    (λ (x : nonnegreal * cfg),
       let '(ε, (e1, σ1)) := x in
       (* [prim_step] *)
       exec_ub_no_chain_case_1 Z ε e1 σ1 ∨
         exec_ub_no_chain_case_2 Z ε e1 σ1)%I.

  Lemma exec_ub_no_chain_grading_mono `{!ub_clutchGS Σ} (ε ε' : nonnegreal) Z c:
    ⌜(ε <= ε')%R⌝ -∗ exec_ub_no_chain Z (ε, c) -∗ exec_ub_no_chain Z (ε', c).
  Proof.
    iIntros "%Hleq H_ub".
    rewrite /exec_ub_no_chain.
    destruct c as [e σ].
    iDestruct "H_ub" as "[H_ub|H_ub]".
    - iLeft.
      iDestruct "H_ub" as "(%R & %ε1 & %ε2 & %Hε & %Hub & H)".
      iExists R, ε1, ε2.
      iSplitR.
      { iPureIntro; lra. }
      iSplitR.
      { iPureIntro; by eapply UB_mon_grading. }
      iFrame.
    - iRight.
      iDestruct "H_ub" as "(%R & %ε1 & %ε2 & [%r %Hr] & %H & %Hub & ?)".
      iExists R, ε1, ε2.
      iFrame.
      iSplit; iPureIntro.
      + eauto.
      + split; [lra|done].
  Qed.

  Definition exec_ub_no_chain_split `{!ub_clutchGS Σ} (Z : nonnegreal -> cfg -> iProp Σ)(ε' : nonnegreal) c:
   ⊢ ((∀ ε : nonnegreal, ⌜ε'<ε⌝ -∗ exec_ub_no_chain Z (ε, c)) -∗
    let '(e1, σ1) := c in
    (∀ ε : nonnegreal, ⌜ε'<ε⌝ -∗ exec_ub_no_chain_case_1 Z ε e1 σ1) ∨
      (∀ ε : nonnegreal, ⌜ε'<ε⌝ -∗ exec_ub_no_chain_case_2 Z ε e1 σ1))%I.
  Proof.
    iStartProof.
    iIntros "H".
    destruct c as [e σ].
    Abort.
    
End Experiment_exec_ub_no_chain.




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
