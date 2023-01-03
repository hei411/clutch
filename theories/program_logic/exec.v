From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import relations fin_maps functions.
From self.prelude Require Import classical.
From self.program_logic Require Export language.
From self.prob Require Export distribution couplings.

(** Distribution for [n]-step partial evaluation *)
Section exec.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Definition prim_step_or_val (ρ : cfg Λ) : distr (cfg Λ) :=
    match to_val ρ.1 with
    | Some v => dret ρ
    | None => prim_step ρ.1 ρ.2
    end.

  Lemma prim_step_or_val_no_val e σ :
    to_val e = None → prim_step_or_val (e, σ) = prim_step e σ.
  Proof. rewrite /prim_step_or_val /=. by intros ->. Qed.

  Lemma prim_step_or_val_is_val e σ :
    is_Some (to_val e) → prim_step_or_val (e, σ) = dret (e, σ).
  Proof. rewrite /prim_step_or_val /=. by intros [? ->]. Qed.

  Definition exec (n : nat) ρ : distr (cfg Λ) := iterM n prim_step_or_val ρ.

  Lemma exec_O ρ :
    exec 0 ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_Sn ρ n :
    exec (S n) ρ = prim_step_or_val ρ ≫= exec n.
  Proof. done. Qed.

  Lemma exec_plus ρ n m :
    exec (n + m) ρ = exec n ρ ≫= exec m.
  Proof. rewrite /exec iterM_plus //.  Qed.

  Lemma exec_1 :
    exec 1 = prim_step_or_val.
  Proof.
    extensionality ρ; destruct ρ as [e σ].
    rewrite exec_Sn /exec /= dret_id_right //.
  Qed.

  Lemma exec_Sn_r e σ n :
    exec (S n) (e, σ) = exec n (e, σ) ≫= prim_step_or_val.
  Proof.
    assert (S n = n + 1)%nat as -> by lia.
    rewrite exec_plus exec_1 //.
  Qed.

  Lemma exec_det_step n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (e1, σ1) = 1 →
    exec (S n) ρ (e2, σ2) = 1.
  Proof.
    destruct ρ as [e0 σ0].
    rewrite exec_Sn_r.
    intros H ->%pmf_1_eq_dret.
    rewrite dret_id_left /=.
    case_match; [|done].
    assert (to_val e1 = None); [|simplify_eq].
    eapply val_stuck. erewrite H. lra.
  Qed.

  Lemma exec_det_step_ctx K `{!LanguageCtx K} n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (K e1, σ1) = 1 →
    exec (S n) ρ (K e2, σ2) = 1.
  Proof.
    intros. eapply exec_det_step; [|done].
    rewrite -fill_step_prob //.
    eapply (val_stuck _ σ1 (e2, σ2)). lra.
  Qed.

  Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) m n ρ e e' σ :
    P →
    PureExec P n e e' →
    exec m ρ (K e, σ) = 1 →
    exec (m + n) ρ (K e', σ) = 1.
  Proof.
    move=> HP /(_ HP).
    destruct ρ as [e0 σ0].
    revert e e' m. induction n=> e e' m.
    { rewrite -plus_n_O. by inversion 1. }
    intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
    specialize (IHn _ _ m Hsteps Hdet).
    rewrite -plus_n_Sm.
    eapply exec_det_step_ctx; [done| |done].
    apply Hpstep.
  Qed.

End exec.

Global Arguments exec {_} _ _ : simpl never.

(** Distribution for evaluation ending in a value in less than [n]-step *)
Section exec_val.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Fixpoint exec_val (n : nat) (ρ : cfg Λ) {struct n} : distr (val Λ) :=
    match to_val ρ.1, n with
      | Some v, _ => dret v
      | None, 0 => dzero
      | None, S n => prim_step ρ.1 ρ.2 ≫= exec_val n
    end.

  Lemma exec_val_unfold (n : nat) :
    exec_val n = λ ρ,
      match to_val ρ.1, n with
      | Some v, _ => dret v
      | None, 0 => dzero
      | None, S n => prim_step ρ.1 ρ.2 ≫= exec_val n
      end.
  Proof. by destruct n. Qed.

  Lemma exec_val_is_val e σ n v:
    to_val e = Some v → exec_val n (e, σ) = dret v.
  Proof. destruct n; simpl; by intros ->. Qed.

  Lemma exec_val_Sn (ρ : cfg Λ) (n: nat) :
    exec_val (S n) ρ = prim_step_or_val ρ ≫= exec_val n.
  Proof.
    destruct ρ as [e σ].
    rewrite /prim_step_or_val /=.
    destruct (to_val e) eqn:Hv=>/=; [|done].
    rewrite dret_id_left -/exec_val.
    fold exec_val.
    erewrite exec_val_is_val; eauto.
  Qed.


  Lemma exec_val_mon ρ n :
    forall a, (exec_val n ρ) a <= (exec_val (S n) ρ) a.
  Proof.
    apply refRcoupl_eq_elim.
    move : ρ.
    induction n.
    - intros.
      apply refRcoupl_from_leq; intro; auto.
      rewrite /distr_le; simpl.
      case_match; auto.
      apply Rle_refl.
    - intros; do 2 rewrite exec_val_Sn.
      apply (refRcoupl_dbind _ _ _ _ eq); [ | apply refRcoupl_eq_refl].
      intros ? ? ->; auto.
  Qed.

  Lemma exec_val_Sn_not_val e σ n :
    to_val e = None →
    exec_val (S n) (e, σ) = prim_step e σ ≫= exec_val n.
  Proof. intros ?. rewrite exec_val_Sn prim_step_or_val_no_val //. Qed.

 Lemma exec_exec_val n ρ v σ :
    exec n ρ (of_val v, σ) <=
    exec_val n ρ v.
 Admitted.

 Lemma exec_exec_val_neq n m ρ v v' σ :
    v ≠ v' ->
    exec_val m ρ v' + exec n ρ (of_val v, σ) <= 1.
  Proof.
    intros.
    eapply (Rle_trans _ (exec_val (m `max` n) ρ v' + exec_val (m `max` n) ρ v)).
    - apply Rplus_le_compat_l.
      apply exec_exec_val.

    rewrite exec

End exec_val.

(** Limit of [prim_exec]  *)
Section prim_exec_lim.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types σ : state Λ.

  Definition lim_exec_val (ρ : cfg Λ) : distr (val Λ):=
    lim_distr (λ n, exec_val n ρ) (exec_val_mon ρ).

  Lemma lim_exec_val_rw (ρ : cfg Λ) v :
    lim_exec_val ρ v = Sup_seq (λ n, (exec_val n ρ) v).
  Proof.
    rewrite lim_distr_pmf; auto.
  Qed.

  Lemma lim_exec_val_prim_step (ρ : cfg Λ) :
    lim_exec_val ρ = prim_step_or_val ρ ≫= lim_exec_val.
  Proof.
   apply distr_ext.
   intro v.
   rewrite lim_exec_val_rw/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_val_rw.
   assert
     (SeriesC (λ a : cfg Λ, prim_step_or_val ρ a * Sup_seq (λ n : nat, exec_val n a v)) =
     SeriesC (λ a : cfg Λ, Sup_seq (λ n : nat, prim_step_or_val ρ a * exec_val n a v))) as ->.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec_val n v' v))); auto.
     - rewrite <- (Sup_seq_scal_l (prim_step_or_val ρ v') (λ n : nat, exec_val n v' v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite (MCT_seriesC _ (λ n, exec_val (S n) ρ v) (lim_exec_val ρ v)); auto.
   - intros; apply Rmult_le_pos; auto.
   - intros.
     apply Rmult_le_compat; auto; [apply Rle_refl | apply exec_val_mon]; auto.
   - intro.
     exists (prim_step_or_val ρ a); intro.
     rewrite <- Rmult_1_r.
     apply Rmult_le_compat_l; auto.
   - intro n.
     rewrite exec_val_Sn.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (prim_step_or_val ρ)); auto.
     intro; split; auto.
     + apply Rmult_le_pos; auto.
     + rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; auto.
   - rewrite lim_exec_val_rw.
     rewrite mon_sup_succ.
     + rewrite (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_correct (λ n : nat, exec_val (S n) ρ v)).
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intro; apply exec_val_mon.
  Qed.

  Lemma lim_exec_val_exec n (ρ : cfg Λ) :
    lim_exec_val ρ = exec n ρ ≫= lim_exec_val.
  Proof.
    move : ρ.
    induction n; intro ρ.
    - rewrite exec_O.
      rewrite dret_id_left; auto.
    - rewrite exec_Sn -dbind_assoc/=.
      (* This is a bit slow *)
      setoid_rewrite <- IHn.
      apply lim_exec_val_prim_step.
  Qed.

  Lemma lim_exec_val_exec_det n ρ (v : val Λ) σ :
    exec n ρ (of_val v, σ) = 1 →
    lim_exec_val ρ = dret v.
  Proof.
    intro Hv.
    apply distr_ext.
    intro v'.
    rewrite lim_exec_val_rw.
    rewrite {2}/pmf/=/dret_pmf.
    assert (is_finite (Sup_seq (λ n0 : nat, exec_val n0 ρ v'))) as Haux.
    {
      apply (Rbar_le_sandwich 0 1); auto.
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
      + apply upper_bound_ge_sup; intro; simpl; auto.
    }
    case_bool_decide; simplify_eq.
    - apply Rle_antisym.
      + apply finite_rbar_le; auto.
        apply upper_bound_ge_sup.
        intro; simpl; auto.
      + apply rbar_le_finite; auto.
        apply (Sup_seq_minor_le _ _ n); simpl; auto.
        rewrite <- Hv.
        erewrite exec_exec_val; eauto.
    - rewrite <- (sup_seq_const 0).
      apply f_equal.
      apply Sup_seq_ext.
      intro m; simpl.
      f_equal.
      eapply exec_exec_val_neq; eauto.
  Qed.


  Lemma lim_exec_val_continous ρ1 v r :
    (∀ n, exec_val n ρ1 v <= r) → lim_exec_val ρ1 v <= r.
    intro Hexec.
    rewrite lim_exec_val_rw.
    assert (is_finite (Sup_seq (λ n : nat, exec_val n ρ1 v))) as Haux.
    {
      apply (Rbar_le_sandwich 0 1); auto.
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
      + apply upper_bound_ge_sup; intro; simpl; auto.
    }
    apply finite_rbar_le; auto.
    apply upper_bound_ge_sup.
    intro; simpl; auto.
  Qed.

End prim_exec_lim.
