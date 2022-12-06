From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction proofmode.
From self.prob_lang Require Import spec_rules spec_tactics tactics.
From self.logrel Require Import model rel_rules.

(** * General-purpose tactics *)
Lemma tac_rel_bind_l `{!prelogrelGS Σ} e' K ℶ E F e t A :
  e = fill K e' →
  envs_entails ℶ (REL fill K e' << t @ E ; F : A) →
  envs_entails ℶ (REL e << t @ E ; F : A).
Proof. intros. subst. assumption. Qed.

Lemma tac_rel_bind_r `{!prelogrelGS Σ} (t' : expr) K ℶ E F e t A :
  t = fill K t' →
  envs_entails ℶ (REL e << fill K t' @ E ; F : A) →
  envs_entails ℶ (REL e << t @ E ; F : A).
Proof. intros. subst. assumption. Qed.

Tactic Notation "rel_bind_l" open_constr(efoc) :=
  iStartProof;
  eapply (tac_rel_bind_l efoc);
  [ tp_bind_helper
  | (* new goal *)
  ].

Tactic Notation "rel_bind_r" open_constr(efoc) :=
  iStartProof;
  eapply (tac_rel_bind_r efoc);
  [ tp_bind_helper
  | (* new goal *)
  ].

Ltac rel_bind_ctx_l K :=
  eapply (tac_rel_bind_l _ K);
  [pm_reflexivity || tp_bind_helper
  |].

Ltac rel_bind_ctx_r K :=
  eapply (tac_rel_bind_r _ K);
  [pm_reflexivity || tp_bind_helper
  |].


(** Similar to `tp_bind_helper`, but tries tries to solve goals for a _specific_ `efoc` *)
Tactic Notation "tac_bind_helper" open_constr(efoc) :=
  lazymatch goal with
  | |- fill ?K ?e = fill _ _ =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ _ =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

(** Reshape the expression on the LHS/RHS untill you can apply `tac` to it *)
Ltac rel_reshape_cont_l tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ _ (fill ?K ?e) _ _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ ?e _ _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.

Ltac rel_reshape_cont_r tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ _ _ (fill ?K ?e) _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ _ ?e _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.


(** 1. prettify ▷s caused by [MaybeIntoLaterNEnvs]
    2. simplify the goal *)
Ltac rel_finish := pm_prettify; iSimpl.

Ltac rel_values :=
  iStartProof;
  iApply refines_ret;
  eauto with iFrame;
  (* TODO: check that we have actually succeeded in solving the previous conditions, or add rel_pure_l/r beforehand *)
  rel_finish.

Ltac rel_values_na :=
  iStartProof;
  iApply refines_ret_na;
  rel_finish.

Tactic Notation "rel_apply_l" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_l ltac:(fun K e =>
      rel_bind_ctx_l K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_l: Cannot apply" P
      end));
  try rel_finish.

Tactic Notation "rel_apply_r" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_r ltac:(fun K e =>
      rel_bind_ctx_r K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_r: Cannot apply" P
      end));
  try lazymatch goal with
  | |- _ ⊆ _ => try solve_ndisj
  end;
  try rel_finish.

(** * Symbolic execution *)

(** Pure reductions *)

Lemma tac_rel_pure_l `{!prelogrelGS Σ} K e1 ℶ ℶ' E F e e2 eres ϕ n m t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  (* The mask check is not necessary anymore  *)
  ((m = n ∧ E = ⊤) ∨ m = 0) →
  MaybeIntoLaterNEnvs m ℶ ℶ' →
  eres = fill K e2 →
  envs_entails ℶ' (REL eres << t @ E ; F : A) →
  envs_entails ℶ (REL e << t @ E ; F : A).
Proof.
  rewrite envs_entails_unseal.
  intros Hfill Hpure Hϕ Hm ?? Hp. subst.
  destruct Hm as [[-> ->] | ->]; rewrite into_laterN_env_sound /= Hp.
  - rewrite -refines_pure_l //.
  - rewrite -refines_pure_l //. apply bi.laterN_intro.
Qed.

Lemma tac_rel_pure_r `{!prelogrelGS Σ} K e1 ℶ E F (e e2 eres : expr) ϕ n t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  nclose specN ⊆ E →
  eres = fill K e2 →
  envs_entails ℶ (REL t << eres @ E ; F : A) →
  envs_entails ℶ (REL t << e @ E ; F : A).
Proof.
  intros Hfill Hpure Hϕ ?? Hp. subst.
  rewrite -refines_pure_r //.
Qed.

Tactic Notation "rel_pure_l" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_l ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_l K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureExec ϕ n e1 e2 *)
      | .. ]);
      [try prob_lang.proofmode.solve_vals_compare_safe                (** φ *)
      |first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *)
             | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *)
      |iSolveTC                                     (** IntoLaters *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)]
  || fail "rel_pure_l: cannot find the reduct".

Tactic Notation "rel_pure_l" := rel_pure_l _.

Tactic Notation "rel_pure_r" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_r ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_r K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureExec ϕ n e1 e2 *)
      |..]);
      [try prob_lang.proofmode.solve_vals_compare_safe                (** φ *)
      |solve_ndisj        || fail 1 "rel_pure_r: cannot solve ↑specN ⊆ ?"
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)]
  || fail "rel_pure_r: cannot find the reduct".

Tactic Notation "rel_pure_r" := rel_pure_r _.

(* TODO: do this in one go, without [repeat]. *)
Ltac rel_pures_l :=
  iStartProof;
  repeat (rel_pure_l _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)
Ltac rel_pures_r :=
  iStartProof;
  repeat (rel_pure_r _; []).

(** Load *)

Lemma tac_rel_load_l_simp `{!prelogrelGS Σ} K ℶ1 ℶ2 i1 p (l : loc) q v e t eres A E F :
  e = fill K (Load (# l)) →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (p, l ↦{q} v)%I →
  eres = fill K (of_val v) →
  envs_entails ℶ2 (refines E F eres t A) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ?? -> Hℶ2) "Henvs".
  iDestruct (into_laterN_env_sound with "Henvs") as "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hℶ2. iApply (refines_load_l K E F l q).
  iExists v.
  destruct p; simpl; [|by iFrame].
  iDestruct "Hl" as "#Hl". iSplitR; [by auto|].
  iIntros "!> _". by iApply "Henvs".
Qed.

Lemma tac_rel_load_r `{!prelogrelGS Σ} K ℶ1 E F i1 p (l : loc) q e t tres A v :
  t = fill K (Load (# l)) →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (p, l ↦ₛ{q} v)%I →
  tres = fill K (of_val v) →
  envs_entails ℶ1 (refines E F e tres A) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ?? -> Hg) "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hg. destruct p; simpl.
  - iDestruct "Hl" as "#Hl". iApply (refines_load_r with "Hl"); first done.
    iIntros "_". by iApply "Henvs".
  - by iApply (refines_load_r with "Hl").
Qed.

Tactic Notation "rel_load_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_l: cannot find" l "↦ ?" in
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_load_l_simp K); first reflexivity)
    |fail 1 "rel_load_l: cannot find 'Load'"];
  (* the remaining goals are from tac_lel_load_l (except for the first one, which has already been solved by this point) *)
  [iSolveTC             (** IntoLaters *)
  |solve_mapsto ()
  |reflexivity       (** eres = fill K v *)
  |rel_finish  (** new goal *)].

(* Tactic Notation "rel_load_l_atomic" := rel_apply_l refines_load_l. *)

(* The structure for the tacticals on the right hand side is a bit
different. Because there is only one type of rules, we can report
errors in a more precise way. E.g. if we are executing !#l and l ↦ₛ is
not found in the environment, then we can immediately fail with an
error *)
Tactic Notation "rel_load_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_r: cannot find" l "↦ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_load_r K); first reflexivity)
    |fail 1 "rel_load_r: cannot find 'Load'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_load_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |reflexivity
  |rel_finish  (** new goal *)].

(** Store *)
Lemma tac_rel_store_l_simpl `{!prelogrelGS Σ} K ℶ1 ℶ2 ℶ3 i1 (l : loc) v e' v' e t eres A E F :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v')) ℶ2 = Some ℶ3 →
  eres = fill K #() →
  envs_entails ℶ3 (refines E F eres t A) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  rewrite -(refines_store_l K ⊤ F l).
  rewrite -(bi.exist_intro v).
  by rewrite Hg.
Qed.

Lemma tac_rel_store_r `{!prelogrelGS Σ} K ℶ1 ℶ2 i1 E (l : loc) v e' v' e t eres F A :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v')) ℶ1 = Some ℶ2 →
  eres = fill K #() →
  envs_entails ℶ2 (refines E F t eres A) →
  envs_entails ℶ1 (refines E F t e A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_store_r E F K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_store_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
    iAssumptionCore || fail "rel_store_l: cannot find" l "↦ₛ ?" in
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_store_l_simpl K);
       [reflexivity (** e = fill K (#l <- e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_store_l: cannot find 'Store'"];
  (* the remaining goals are from tac_rel_store_l (except for the first one, which has already been solved by this point) *)
  [iSolveTC        (** IntoLaters *)
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_store_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

(* Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l. *)

Tactic Notation "rel_store_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_store_r: cannot find" l "↦ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_store_r K);
       [reflexivity|iSolveTC|idtac..])
    |fail 1 "rel_store_r: cannot find 'Store'"];
  (* the remaining goals are from tac_rel_store_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_store_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_store_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].


(** Alloc *)
(* Tactic Notation "rel_alloc_l_atomic" := rel_apply_l refines_alloc_l. *)

Lemma tac_rel_alloc_l_simpl `{!prelogrelGS Σ} K ℶ1 ℶ2 e t e' v' A E F :
  e = fill K (Alloc e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (l : loc),
     (l ↦ v' -∗ refines E F (fill K (of_val #l)) t A))) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_alloc_l _ ⊤); eauto.
  apply bi.later_mono.
Qed.

Tactic Notation "rel_alloc_l" ident(l) "as" constr(H) :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_alloc_l_simpl K);
       [reflexivity (** e = fill K (Alloc e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_l: cannot find 'Alloc'"];
  [iSolveTC        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].

Lemma tac_rel_alloc_r `{!prelogrelGS Σ} K' ℶ E t' v' e t F A :
  t = fill K' (Alloc t') →
  IntoVal t' v' →
  nclose specN ⊆ E →
  envs_entails ℶ (∀ l, l ↦ₛ v' -∗ refines E F e (fill K' #l) A) →
  envs_entails ℶ (refines E F e t A).
Proof.
  intros ????. subst t.
  rewrite -refines_alloc_r //.
Qed.

Tactic Notation "rel_alloc_r" ident(l) "as" constr(H) :=
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_alloc_r K);
       [reflexivity  (** t = K'[alloc t'] *)
       |iSolveTC     (** t' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_r: cannot find 'Alloc'"];
  [solve_ndisj || fail "rel_alloc_r: cannot prove 'nclose specN ⊆ ?'"
  |iIntros (l) H; rel_finish  (** new goal *)].

Tactic Notation "rel_alloc_r" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloc_r l as H.

Tactic Notation "rel_alloc_l" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloc_l l as H.


(** AllocTape *)
(* Tactic Notation "rel_alloctape_l_atomic" := rel_apply_l refines_alloctape_l. *)

Lemma tac_rel_alloctape_l_simpl `{!prelogrelGS Σ} K ℶ1 ℶ2 e t A E F :
  e = fill K AllocTape →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (α : loc),
     (α ↪ [] -∗ refines E F (fill K (of_val #lbl:α)) t A))) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_alloctape_l _ ⊤); eauto.
  now apply bi.later_mono.
Qed.

Tactic Notation "rel_alloctape_l" ident(l) "as" constr(H) :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_alloctape_l_simpl K);
       [reflexivity (** e = fill K (Alloc e') *)
       |idtac..])
    |fail 1 "rel_alloctape_l: cannot find 'Alloc'"];
  [iSolveTC        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].

Lemma tac_rel_alloctape_r `{!prelogrelGS Σ} K' ℶ E e t F A :
  t = fill K' AllocTape →
  nclose specN ⊆ E →
  envs_entails ℶ (∀ α, α ↪ₛ [] -∗ refines E F e (fill K' #lbl:α) A) →
  envs_entails ℶ (refines E F e t A).
Proof.
  intros ???. subst t.
  rewrite -refines_alloctape_r //.
Qed.

Tactic Notation "rel_alloctape_r" ident(l) "as" constr(H) :=
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_alloctape_r K);
       [reflexivity  (** t = K'[alloc t'] *)
       |idtac..])
    |fail 1 "rel_alloctape_r: cannot find 'Alloc'"];
  [solve_ndisj || fail "rel_alloctape_r: cannot prove 'nclose specN ⊆ ?'"
  |iIntros (l) H; rel_finish  (** new goal *)].

Tactic Notation "rel_alloctape_r" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloctape_r l as H.

Tactic Notation "rel_alloctape_l" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloctape_l l as H.

Lemma tac_rel_flip_l `{!prelogrelGS Σ} K ℶ1 ℶ2 i1 (α : loc) b bs e t tres A E F :
  t = fill K (Flip (#lbl: α)) →
  envs_lookup i1 ℶ1 = Some (false, α ↪ (b::bs))%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪ bs)) ℶ1 = Some ℶ2 →
  tres = fill K (of_val #b) →
  envs_entails ℶ2 (refines E F tres e A) →
  envs_entails ℶ1 (refines E F t e A).
Proof.
  rewrite envs_entails_unseal. iIntros (???? Hg).
  subst t tres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite Hg.
  iIntros "(Hα & Hlog)".
  rewrite -(refines_flip_l _ _ K α b bs) //.
  iFrame.
Qed.

Lemma tac_rel_flip_r `{!prelogrelGS Σ} K ℶ1 ℶ2 E i1 (α : loc) b bs e t tres F A :
  t = fill K (Flip (#lbl: α)) →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, α ↪ₛ (b::bs))%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪ₛ bs)) ℶ1 = Some ℶ2 →
  tres = fill K (of_val #b) →
  envs_entails ℶ2 (refines E F e tres A) →
  envs_entails ℶ1 (refines E F e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (????? Hg).
  subst t tres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_flip_r _ _ K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_flip_l" :=
  let solve_mapsto _ :=
    let α := match goal with |- _ = Some (_, (?α ↪ _)%I) => α end in
    iAssumptionCore || fail "rel_flip_l: cannot find" α "↪ ?" in
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_flip_l K); first reflexivity)
    |fail 1 "rel_flip_l: cannot find 'Flip"];
  (* the remaining goals are from tac_rel_flip_l (except for the first one, which has already been solved by this point) *)
  [solve_mapsto ()
  |pm_reflexivity || fail "rel_flip_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

(* Tactic Notation "rel_flip_l_atomic" := rel_apply_l refines_flip_l. *)

Tactic Notation "rel_flip_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↪ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_flip_r: cannot find" l "↪ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_flip_r K); first reflexivity)
    |fail 1 "rel_flip_r: cannot find 'Flip'"];
  (* the remaining goals are from tac_rel_flip_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_flip_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_flip_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].


(* The handling of beta-reductions is special because it also unlocks
 the locked `RecV` values. The the comments for the `wp_rec` tactic in
 the heap_lang
 proofmode.
 *)
Tactic Notation "rel_rec_l" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  rel_pure_l (App _ _);
  clear H.
Tactic Notation "rel_rec_r" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  rel_pure_r (App _ _);
  clear H.

(** For backwards compatibility *)
Tactic Notation "rel_seq_l" := rel_pure_l (App _ _).
Tactic Notation "rel_let_l" := rel_pure_l (App _ _).
Tactic Notation "rel_fst_l" := rel_pure_l (Fst _).
Tactic Notation "rel_snd_l" := rel_pure_l (Snd _).
Tactic Notation "rel_proj_l" := rel_pure_l (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_inr_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_binop_l" := rel_pure_l (BinOp _ _ _).
Tactic Notation "rel_op_l" := rel_binop_l.
Tactic Notation "rel_if_true_l" := rel_pure_l (If #true _ _).
Tactic Notation "rel_if_false_l" := rel_pure_l (If #false _ _).
Tactic Notation "rel_if_l" := rel_pure_l (If _ _ _).

Tactic Notation "rel_seq_r" := rel_pure_r (App _ _).
Tactic Notation "rel_let_r" := rel_pure_r (App _ _).
Tactic Notation "rel_fst_r" := rel_pure_r (Fst _).
Tactic Notation "rel_snd_r" := rel_pure_r (Snd _).
Tactic Notation "rel_proj_r" := rel_pure_r (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_inr_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_binop_r" := rel_pure_r (BinOp _ _ _).
Tactic Notation "rel_op_r" := rel_binop_r.
Tactic Notation "rel_if_true_r" := rel_pure_r (If #true _ _).
Tactic Notation "rel_if_false_r" := rel_pure_r (If #false _ _).
Tactic Notation "rel_if_r" := rel_pure_r (If _ _ _).

Ltac rel_arrow_val :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow_val
  || fail "rel_arrow_val: cannot apply the closure rule");
  iModIntro.

Ltac rel_arrow :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow
  || fail "rel_arrow: cannot apply the closure rule");
  iModIntro.
