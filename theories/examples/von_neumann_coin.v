(* A zoo of variants of Von Neumann's construction of a fair coin from a biased coin. *)

From stdpp Require Import namespaces.
From self.prob_lang Require Import lang notation spec_ra proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics compatibility.
From self.typing Require Import fundamental.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition coinN := nroot.@"coin".

  (* Biased coin toss: t4 = { true ⟼ 1/4, false ⟼ 3/4 } *)
  Definition t4 :=
    (λ:<>,
      let: "b0" := flip #() in
      let: "b1" := flip #() in
      if: "b1" then "b0" else #false)%V.

  (* Von Neumann coin. *)
  Definition vnc (t : expr) :=
    (rec: "f" <> :=
      let: "x" := t #() in
      let: "y" := t #() in
      if: "x" = "y" then "f" #() else "x")%V.

  (* A variant that diverges instead of recursing. Can be used in simple
  situations to prove a left-refinement because our judgement allows discarding
  mass on the left. *)
  Definition vnc_div (t : expr) :=
    (λ:<>,
      let: "x" := t #() in
      let: "y" := t #() in
      if: "x" = "y" then (rec: "f" <> := "f" #()) #() else "x")%V.

  (* We can't show this refinement since the lhs needs to couple a combination
  of flips with a single flip on the rhs and since we may need to recurse an
  unbounded number of times. *)
  Goal ⊢ REL (vnc t4) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_pures_r. rel_pures_l.
    set (vnc4 := vnc t4).
    unfold vnc in vnc4.
    fold vnc4.
    unfold t4. rel_pures_l.
  Abort.

  (* A simpler coin toss: t2 = { true ⟼ 1/2, false ⟼ 1/2 } *)
  Definition t2 := (λ:<>, flip #())%V.

  (* Still can't prove the refinement since we don't know how to recurse. *)
  Goal ⊢ REL (vnc t2) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof.
    iLöb as "HH".
    rewrite /vnc.
    rel_pures_r. rel_pures_l.

    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_rec_l.
    rel_pures_r. rel_pures_l.
    set (vnc2 := vnc t2) ; unfold vnc in vnc2 ; fold vnc2.
    unfold t2. rel_pures_l.

    rel_apply refines_couple_flips_lr.
    iIntros (b).
    rel_pures_l.
    rel_apply refines_flipU_l.
    iIntros (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    - admit.
    - rel_values.
  Abort.

  (* We can prove the refinement in case we diverge instead. *)
  Goal ⊢ REL (vnc_div t2) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc_div.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_rec_l.
    rel_pures_r. rel_pures_l.
    set (vnc2 := vnc_div t2) ; unfold vnc_div in vnc2 ; fold vnc2.
    unfold t2. rel_pures_l.
    rel_apply refines_couple_flips_lr_eq.
    iIntros (b).
    rel_pures_l.
    rel_apply refines_flipU_l.
    iIntros (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    - iLöb as "H".
      rel_rec_l.
      iExact "H".
    - rel_values.
  Qed.

  (* But unfortunately we can't even apply the divergence trick to the t4
  biased coin, since we would have to decide on coupling the rhs flip with a
  single flip on the left, but there's no single good choice. *)
  Goal ⊢ REL (vnc_div t4) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof with try rel_pures_r ; try rel_pures_l.
    rewrite /vnc_div...
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_rec_l.
    set (vnc4 := vnc_div t4) ; unfold vnc_div in vnc4 ; fold vnc4.
    unfold t4...
    rel_apply refines_couple_flips_lr.
    iIntros (b)...
    rel_apply_l refines_flipU_l.
    iIntros (b')...
    destruct b'...
    - rel_apply_l refines_flipU_l.
      iIntros (b')...
      rel_apply_l refines_flipU_l.
      iIntros (b'')...
      destruct b''...
      + case_bool_decide...
        * iLöb as "H".
          rel_rec_l.
          iExact "H".
        * rel_values.
      + case_bool_decide...
        * iLöb as "H".
          rel_rec_l.
          iExact "H".
        * rel_values.
    - rel_apply_l refines_flipU_l.
      iIntros (b')...
      rel_apply_l refines_flipU_l.
      iIntros (b'')...
      destruct b''...
      + case_bool_decide...
        * iLöb as "H".
          rel_rec_l.
          iExact "H".
        * give_up.
      + iLöb as "H".
        rel_rec_l.
        iExact "H".
  Abort.

  (* A similar problem: no single flip on the left behaves like the rhs. But we
  can pick our coupling after evaluating the first flip! *)
  Goal ⊢ REL (flip #()) = (flip #()) << flip #() : lrel_bool.
  Proof.
    rel_apply refines_flipU_l.
    iIntros (b).
    rel_apply (refines_couple_flips_lr (if b then id else negb)).
    iIntros (b').
    destruct b, b' => /=.
    all: rel_pures_l.
    all: rel_values.
    Unshelve. destruct b ; apply _.
  Qed.

  (* We can however show this refinement where the result on the left only
  depends on the outcome of one flip. *)
  Goal ⊢ REL (let: "b" := flip #() in if: "b" = (flip #()) then "b" else "b") << flip #() : lrel_bool.
  Proof.
    rel_apply refines_couple_flips_lr.
    iIntros (b).
    rel_pures_l.
    rel_apply_l refines_flipU_l.
    iIntros (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    all: rel_values.
  Qed.

  (* We can even flip separately in each branch. *)
  Goal ⊢ REL if: flip #() then flip #() else flip #() << flip #() : lrel_bool.
  Proof.
    rel_apply_l refines_flipU_l ; iIntros (b').
    destruct b' ; rel_pures_l.
    all: replace lrel_bool with (interp.interp types.TBool []) by easy ;
      rel_apply_l refines_typed ;
      apply types.TFlipU ; repeat constructor.
  Qed.

End proofs.
