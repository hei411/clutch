(* A case study of coupon collection *)
From clutch Require Export clutch.
From clutch.lib Require Export map.
From stdpp Require Export fin_maps fin_sets finite. 


Set Default Proof Using "Type*".


Definition cnt_map_helper : expr :=
    (rec: "cnt_helper" "m" "k" "n" :=
       if: "k" = "n"
       then #0
       else
         let: "k'" := "k" + #1 in
         match: get "m" "k" with
           NONE => "cnt_helper" "m" "k'" "n"
         | SOME <> =>
             "cnt_helper" "m" "k'" "n" + #1
         end
    ).

  Definition cnt_map : expr:=
    λ: "m" "n",
      cnt_map_helper "m" #0 "n".
      
  Definition coupon_helper : expr :=
    rec: "coupon_helper" "m" "n" "cnt" :=
      if: cnt_map "m" "n" = "n" then !"cnt" else
        "cnt" <- !"cnt" + #1;;
        let: "k" := rand ("n" - #1) from #() in
        set "m" "k" #();;
        "coupon_helper" "m" "n" "cnt".
        
  Definition coupon_collection : expr :=
    λ: "n",
      let: "m" := init_map #() in
      let: "cnt" := ref #0 in
      coupon_helper "m" "n" "cnt". 

  Definition spec_coupon_helper : expr :=
    rec: "spec_coupon_helper" "t" "n" "cnt" :=
      if: "n" = "t" then !"cnt" else
        "cnt" <- !"cnt" + #1;;
        let: "k" := rand ("n" - #1) from #() in
        if: ("t" ≤ "k") then "spec_coupon_helper" ("t"+#1) "n" "cnt"
        else "spec_coupon_helper" "t" "n" "cnt".
  
  Definition spec_coupon_collection : expr :=
    λ: "n",
      let: "t" := #0 in
      let: "cnt" := ref #0 in
      spec_coupon_helper "t" "n" "cnt".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition couponN := nroot.@"coupon".
  

  Definition map_set_relate (m: gmap nat val) (s:gset nat)  :=
    forall elem, elem ∈ s <-> is_Some (m !! elem).

  (* This is an invariant in the sense that it holds true for every recursive call, 
     but we do not technically allocate it as an invariant in the RA sense. 
   *)
  Definition coupon_collection_inv n lm (k:Z) (cnt cnt' : loc): iProp Σ :=
    (∃(cntv : nat) s m,
        map_list lm m ∗ ⌜map_set_relate m s⌝ ∗ cnt' ↦ₛ #cntv ∗ cnt ↦ #cntv ∗ ⌜Z.of_nat (size s) = k⌝ ∗⌜s∩set_seq 0 n = s⌝ )%I.

  
  Lemma wp_cnt_map_helper E lm m n s start:
    start <= n ->
    map_set_relate m s ->
    {{{ map_list lm m ∗ ⌜s∩set_seq 0 n = s⌝}}}
      cnt_map_helper #lm #start #n @ E
      {{{v, RET #v; map_list lm m ∗ ⌜v = size (s ∩ (set_seq start (n-start)))⌝
                                              ∗ ⌜s∩set_seq 0 n = s⌝
      }}}.
  Proof. 
    iIntros (H Hms Φ) "[(%&%&Hlm&%&Ha) %] HΦ".
    wp_pure.
    iRevert (H H0 Hms Φ) "HΦ".
    iLöb as "IH" forall (start lv vs).
    iIntros "%H %H0 %Hms %Φ HΦ".
    wp_pures.
    case_bool_decide.
    - wp_pures. iModIntro. replace 0%Z with (Z.of_nat 0) by lia.
      iApply ("HΦ" with "[Hlm Ha]").
      rewrite /map_list.
      iSplitL.
      + iExists _, _. iFrame. by iPureIntro.
      + subst. iPureIntro. rewrite /map_set_relate in Hms.
        inversion H2. rewrite Nat2Z.inj_iff in H3. subst => /=.
        assert (set_seq n (n-n) = (∅ : gset nat)).
        { rewrite elem_of_equiv_empty_L. intros. intro. rewrite elem_of_set_seq in H0.
          destruct H0. lia.
        } rewrite H0.
        assert (s∩∅ = ∅).
        { rewrite elem_of_equiv_empty_L. intros. intro.
          replace (s ∩ ∅) with (∅:gset nat) in H3.
          2: { symmetry. rewrite <- (disjoint_intersection_L). apply disjoint_empty_r. } 
          by rewrite elem_of_empty in H3.
        }
        split.
        -- rewrite H3. done.
        -- done. 
    - wp_pures. wp_bind (get _ _).
      wp_apply (wp_get with "[Hlm Ha]").
      { iExists _, _. iFrame. by iPureIntro. }
      iIntros (b) "[ (%&%&Hlm&%&Ha) %Hres]".
      subst.
      destruct (list_to_map vs !! start) eqn:Hd.
      + do 3 wp_pure.
        replace (Z.of_nat start + 1)%Z with (Z.of_nat (S start)) by lia.
        wp_bind (App _ _)%E.
        wp_apply (wp_mono with "[Hlm Ha HΦ]"); last first.
        { wp_apply ("IH" with "[$Hlm][$Ha][][][][HΦ]").
          - iPureIntro. assert (start ≠ n).
            { intro. subst. done. }
            assert (start < n) by lia.
            lia.
          - done.
          - iPureIntro. split.
            + intros H'. by apply Hms in H'.
            + intros.
              by rewrite Hms. 
          - iIntros (?) "(?&%&%)".
            instantiate (1 :=
                           (λ v': val, ∃ v0 : nat, (⌜#v0 = v'⌝∗ map_list lm (list_to_map vs) ∗ ⌜v0 =(size (s ∩ set_seq (S start) (n - S start)))⌝ ∗ ⌜s ∩ set_seq 0 n = s⌝) ∗
                           (∀ v1 : nat,
           map_list lm (list_to_map vs) ∗ ⌜v1 = size (s ∩ set_seq start (n - start))⌝ ∗
           ⌜s ∩ set_seq 0 n = s⌝ -∗ Φ #v1))%I).
            simpl. iFrame.
            iExists _.
            iSplitR; [done|].
            iPureIntro. split; try done. 
        }
        intros. simpl.
        iIntros "[%((<-&Hml&%&%)&HΦ)]".
        wp_pures.
        iModIntro.
        replace (Z.of_nat v1 + 1)%Z with (Z.of_nat (S v1)) by lia.
        iApply ("HΦ" with "[Hml]"); iFrame.
        iPureIntro.
        split; try done.
        rewrite H0.
        assert (start ∈ s).
        { rewrite Hms. rewrite Hd. done. }
        replace (_∩ set_seq start _) with ({[start]}∪(s ∩ set_seq (S start) (n - S start))).
        -- rewrite size_union.
           { rewrite size_singleton. lia. }
           rewrite disjoint_singleton_l.
           rewrite elem_of_intersection.
           intros [??].
           rewrite elem_of_set_seq in H7. lia.
        -- rewrite set_eq. intros. split; intros K.
           --- rewrite elem_of_union in K. destruct K as [K|K].
               +++ rewrite elem_of_singleton in K. subst.
                   rewrite elem_of_intersection. split; try done.
                   rewrite elem_of_set_seq. split; try lia.
                   assert (start ≠ n).
                   { intro; subst; done. }
                   lia.
               +++ rewrite elem_of_intersection in K.
                   destruct K as [K K'].
                   rewrite elem_of_intersection. split; try done.
                   rewrite elem_of_set_seq. rewrite elem_of_set_seq in K'.
                   destruct K'.
                   split; try lia.
           --- rewrite elem_of_intersection in K. destruct K as [K K'].
               rewrite elem_of_union. 
               rewrite elem_of_intersection.
               rewrite elem_of_set_seq. rewrite elem_of_set_seq in K'.
               destruct K' as [K' K''].
               destruct (decide (x=start)).
               +++ left. subst. by apply elem_of_singleton.
               +++ right.
                   split; try done.
                   split; try lia.
      + do 3 wp_pure.
        replace (Z.of_nat start + 1)%Z with (Z.of_nat (S start)) by lia.
        iApply ("IH" with "[$Hlm][$Ha]").
        -- iPureIntro. destruct H; try done. lia.
        -- by iPureIntro.
        -- iPureIntro. intro. split; intros.
           ++ by apply Hms in H0.  
           ++ rewrite Hms. destruct H0. rewrite H0. done. 
        -- iIntros (?) "(?&%&%)".
           iApply "HΦ".
           iFrame.
           iPureIntro; split; try done.
           rewrite H0.
           assert (start ∉ s).
           { intro. rewrite Hms in H5. rewrite Hd in H5. inversion H5. done. }
           f_equal.
           rewrite set_eq. intros. split; intros.
           ++ rewrite elem_of_intersection in H6. destruct H6 as [H6 H6'].
              rewrite elem_of_intersection; split; try done.
              rewrite elem_of_set_seq in H6'. destruct H6'. rewrite elem_of_set_seq.
              split; try lia.
           ++ rewrite elem_of_intersection. rewrite elem_of_intersection in H6. 
              destruct H6. split; try done.
              rewrite elem_of_set_seq in H7. rewrite elem_of_set_seq. split; try lia.
              assert (x≠start).
              { intro. subst. done. }
              lia.
Qed.            
         

  Lemma coupon_bijection n m s (k:Z):
    n>0 -> map_set_relate m s -> Z.of_nat (size s) = k -> s∩set_seq 0 n = s ->
    ∃ f: (fin (S(n-1))) -> fin (S (n-1)), Bij f /\ forall x, f x < Z.to_nat k <-> is_Some (m!! fin_to_nat x).
  Proof.
    intros H0 H1 H2 H3.
    apply subseteq_intersection_2_L in H3.
    rewrite elem_of_subseteq in H3.
    rewrite /map_set_relate in H1.
    assert (∃ f : fin (S (n - 1)) → fin (S (n - 1)),
               Bij f ∧ (∀ x : fin (S (n - 1)), f x < Z.to_nat k ↔ fin_to_nat x ∈ s)); last first.
    { destruct H as [f[??]]. exists f. split; try done. intros; split; intros.
      - rewrite <- H1. rewrite <- H4. done.
      - rewrite H4.  rewrite H1. done.
    }
    clear m H1.
    replace (S (n-1)) with n by lia.
    assert (k>=0)%Z.
    { rewrite <- H2. lia. }
    assert (∃ k', Z.of_nat k' = k) as [k' Hk].
    { eexists (Z.to_nat k). lia. }
    rewrite <- Hk in H2.
    rewrite <- Hk.
    clear k H Hk.
    apply Nat2Z.inj in H2 as H2.
    rewrite Nat2Z.id.
    pose (s' := set_seq 0 n ∖ s).
    assert (size s' = n - k').
    { rewrite /s'. rewrite size_difference.
      - f_equal; try done. apply size_set_seq.
      - intro. apply H3.
    }
    rename k' into k.
    assert (k<=n) as Hk.
    { rewrite <- H2.
      erewrite <- size_set_seq.
      apply subseteq_size.
      intro. apply H3.
    }
    pose (f' := λ x: fin n,
            let x' := fin_to_nat x in
            match list_find (λ y, y=x') (elements s) with
            | None => match list_find (λ y, y=x') (elements s') with
                     | None => 0 (* doesnt happen*)
                     | Some (i, _) => k+i
                     end
            | Some (i, _) => i
             end               
         ).
    assert (∀ x, f' x < n).
    { intros. rewrite /f'.
      case_match. 
      - destruct p. rewrite list_find_Some in H1.
        destruct H1. apply lookup_lt_Some in H1.
        assert (n0 < k); try lia.
        by replace k with (length (elements s)).
      - case_match; try lia.
        destruct p.
        rewrite list_find_Some in H4. destruct H4.
        apply lookup_lt_Some in H4.
        assert (length(elements s') = n-k); try lia.
        rewrite <- H. done.
    }
    pose (f:= λ x, nat_to_fin (H1 x)).
    exists f.
    assert (Inj eq eq f) as Hinj.
    { rewrite /Inj.
      intros.
      rewrite /f in H4.
      assert (fin_to_nat (nat_to_fin (H1 x)) = fin_to_nat (nat_to_fin (H1 y))).
      { by rewrite H4. }
      rewrite !fin_to_nat_to_fin in H5.
      rewrite /f' in H5.
      case_match.
      + (* x in s*) destruct p.
        case_match.
        -- (*y in s*)
          destruct p. 
          rewrite list_find_Some in H6. rewrite list_find_Some in H7.
          destruct H6 as [?[??]]. destruct H7 as [?[??]]. subst.
          rewrite H6 in H7. inversion H7. by apply fin_to_nat_inj in H5.
        -- (*y not in s*)
          case_match.
          ++ (*y in s'*)
            destruct p.
            exfalso.
            assert (n0 < k); try lia.
            rewrite list_find_Some in H6.
            destruct H6.
            apply lookup_lt_Some in H6. replace k with (length(elements s)).
            eauto.
          ++ assert (fin_to_nat y∈((set_seq 0 n):gset nat)).
             --- pose proof (fin_to_nat_lt y).
                 rewrite elem_of_set_seq. lia.
             --- exfalso.
                 rewrite list_find_None in H7. rewrite list_find_None in H8.
                 rewrite Forall_forall in H7. rewrite Forall_forall in H8.
                 assert (s∪s' = set_seq 0 n).
                 { apply set_eq. split; intros.
                   - rewrite elem_of_union in H10. destruct H10.
                     + eauto.
                     + rewrite /s' in H10. set_solver.
                   - rewrite /s'. rewrite elem_of_union. destruct (decide (x0∈s)).
                     + eauto.
                     + right. rewrite elem_of_difference. eauto.
                 }
                 rewrite <-H10 in H9.
                 rewrite elem_of_union in H9.
                 destruct H9; rewrite -elem_of_elements in H9.
                 +++ apply H7 in H9. done.
                 +++ apply H8 in H9. done.
      + (* x not in s*)
        case_match.
        -- (*x in s'*)
          destruct p.
          case_match.
          ++ (*y in s*) destruct p. assert (n2 < k); try lia.
             rewrite list_find_Some in H8. destruct H8.
             apply lookup_lt_Some in H8. by replace (k) with (length (elements s)).
          ++ case_match.
             --- (*y in s' *) destruct p. assert (n0=n2) by lia; subst.
                 rewrite list_find_Some in H7. rewrite list_find_Some in H9.
                 destruct H7. destruct H9.
                 rewrite H2 in H9. inversion H9.
                 subst.
                 destruct H7. destruct H10.
                 subst. by apply fin_to_nat_inj in H10.
             --- assert (fin_to_nat y∈((set_seq 0 n):gset nat)) as K.
                 { pose proof (fin_to_nat_lt y).
                   rewrite elem_of_set_seq. lia. }
                 exfalso.
                 rewrite list_find_None in H8. rewrite list_find_None in H9.
                 rewrite Forall_forall in H8. rewrite Forall_forall in H9.
                 assert (s∪s' = set_seq 0 n).
                 { apply set_eq. split; intros.
                   - rewrite elem_of_union in H10. destruct H10.
                     + eauto.
                     + rewrite /s' in H10. set_solver.
                   - rewrite /s'. rewrite elem_of_union. destruct (decide (x0∈s)).
                     + eauto.
                     + right. rewrite elem_of_difference. eauto.
                 }
                 rewrite <-H10 in K.
                 rewrite elem_of_union in K.
                 destruct K as [K|K]; rewrite -elem_of_elements in K.
                 +++ apply H8 in K. done.
                 +++ apply H9 in K. done.
        -- assert (fin_to_nat x∈((set_seq 0 n):gset nat)) as K.
           { pose proof (fin_to_nat_lt x).
             rewrite elem_of_set_seq. lia. }
           exfalso.
           rewrite list_find_None in H6. rewrite list_find_None in H7.
           rewrite Forall_forall in H6. rewrite Forall_forall in H7.
           assert (s∪s' = set_seq 0 n).
           { apply set_eq. split; intros.
             - rewrite elem_of_union in H8. destruct H8.
               + eauto.
               + rewrite /s' in H8. set_solver.
             - rewrite /s'. rewrite elem_of_union. destruct (decide (x0∈s)).
               + eauto.
               + right. rewrite elem_of_difference. eauto.
           }
           rewrite <-H8 in K.
           rewrite elem_of_union in K.
           destruct K as [K|K]; rewrite -elem_of_elements in K.
           +++ apply H6 in K. done.
           +++ apply H7 in K. done.
    }
    repeat split; try rewrite /f fin_to_nat_to_fin /f'; intros; last first.
    - case_match.
      2:{ rewrite list_find_None in H5. rewrite Forall_forall in H5.
          rewrite <-elem_of_elements in H4.
          apply H5 in H4. done.
      }
      destruct p.
      rewrite list_find_Some in H5. destruct H5.
      apply lookup_lt_Some in H5.
      rewrite <- H2. done.
    - case_match.
      2: {
        case_match.
        - destruct p. lia.
        - rewrite list_find_None in H6. rewrite list_find_None in H5.
          rewrite Forall_forall in H5. rewrite Forall_forall in H6.
          assert (fin_to_nat x ∈ ((set_seq 0 n):gset nat)).
          { rewrite elem_of_set_seq. split; try lia. simpl. apply fin_to_nat_lt. }
          exfalso.
          assert (s∪s' = set_seq 0 n).
          { apply set_eq. split; intros.
            - rewrite elem_of_union in H8. destruct H8.
              + eauto.
              + rewrite /s' in H8. set_solver.
            - rewrite /s'. rewrite elem_of_union. destruct (decide (x0∈s)).
              + eauto.
              + right. rewrite elem_of_difference. eauto.
          }
          rewrite <- H8 in H7. rewrite elem_of_union in H7. destruct H7.
          + rewrite -elem_of_elements in H7. apply H5 in H7. done.
          + rewrite -elem_of_elements in H7. apply H6 in H7. done. 
      }
      destruct p.
      rewrite list_find_Some in H5. destruct H5 as [?[??]].
      subst.
      rewrite <- elem_of_elements.
      eapply elem_of_list_lookup_2. done.
    - apply finite_inj_surj; try done.
    - done. 
      Unshelve.
      all: apply _.
Qed.

    
  Lemma coupon_collection_refines_spec_helper n lm (k:Z) cnt cnt':
    n>0->
    ⊢ coupon_collection_inv n lm k cnt cnt' -∗ REL coupon_helper #lm #n #cnt << spec_coupon_helper #k #n #cnt' : lrel_nat.
  Proof.
    intros.  
    (* iLöb as "IH" forall (k). *)
    iIntros "Inv".
    rel_pure_l.
    rel_pure_r.
    iRevert "Inv".
    iLöb as "IH" forall (k).
    iIntros "Inv".
    iDestruct "Inv" as (???) "(Hml&%Hms&Hc'&Hc&%&%)".
    do 9 rel_pure_l. 
    rewrite -!/cnt_map_helper.
    rel_pures_r.
    case_bool_decide.
    - (* finish collecting*)
      rel_pures_r. rel_load_r.
      subst.
      rel_apply_l (refines_wp_l _ _ (cnt_map_helper _ _ _)).
      replace 0%Z with (Z.of_nat 0); last done.
      wp_apply (wp_cnt_map_helper with "[$Hml][Hc' Hc]").
      { lia. }
      { done. }
      { iPureIntro. rewrite set_eq_subseteq.
        split.
        - apply intersection_subseteq_l.
        - apply intersection_greatest; try done.
          intro.
          intros.
          rewrite elem_of_set_seq.
          split; try lia.
          simpl.
          rewrite <-H1 in H0.
          rewrite elem_of_intersection in H0. destruct H0. rewrite elem_of_set_seq in H3. lia.
      }
      iModIntro. iIntros (?) "[?[%%]]". rewrite H2. rewrite H0.
      rel_pures_l. case_bool_decide; last first.
      { exfalso. apply H4. f_equal. replace (n-0) with n by lia. rewrite H3.  done. }
      rel_pures_l.
      rel_load_l.
      rel_values.
    - rel_pures_r.
      rel_load_r.
      rel_pures_r.
      rel_store_r.
      rel_pures_r.
      rel_apply_l (refines_wp_l _ _ (cnt_map_helper _ _ _)).
      replace 0%Z with (Z.of_nat 0); last done.
      wp_apply (wp_cnt_map_helper with "[$Hml][Hc' Hc]").
      { lia. }
      { done. }
      { iPureIntro. rewrite set_eq_subseteq.
        split.
        - apply intersection_subseteq_l.
        - apply intersection_greatest; try done.
          intro.
          intros.
          rewrite elem_of_set_seq.
          split; try lia.
          simpl.
          rewrite <- H1 in H3. rewrite elem_of_intersection in H3. destruct H3.
          rewrite elem_of_set_seq in H4. destruct H4. lia. 
      }
      iModIntro. iIntros (?) "[Hml [%%]]". rewrite H3.
      rel_pures_l.
      case_bool_decide.
      { replace (n-0) with n in H5 by lia. rewrite H4 in H5.
        rewrite H0 in H5. done. }
      rel_pures_l.
      rel_load_l.
      rel_pures_l.
      rel_store_l.
      rel_pures_l.
      clear H1 H2 H3. 
      destruct (coupon_bijection _ _ _ _ H  Hms H0 H4) as [f[]].
      rel_apply (refines_couple_UU _ f).
      { by replace (Z.to_nat (Z.of_nat n - 1)) with (n-1) by lia. }
      iModIntro. iIntros (r).
      rel_pures_l.
      rel_pures_r.
      rel_apply_l (refines_wp_l _ _ (set _ _ _)).
      wp_apply (wp_set with "[$Hml] [Hc' Hc]").
      iIntros "!> Hml".
      case_bool_decide.
      + (* new coupon *) rel_pure_r. rel_pure_l. rel_pure_l.
        rel_pure_r. 
        iApply ("IH" $! (k+1)%Z with "[Hc' Hc Hml]").
        iExists _, ({[fin_to_nat r]} ∪ s), _.
        replace (Z.of_nat cntv + 1)%Z with (Z.of_nat (S cntv)) by lia.
        iFrame.
        iSplit; iPureIntro. 
        -- intros. split; intros; try split.
           ++ rewrite lookup_insert_is_Some'.
              apply elem_of_union in H6 as [H6|H6].
              --- rewrite elem_of_singleton in H6. subst.
                  by left.
              --- right. apply Hms in H6. by destruct H6.
           ++ rewrite lookup_insert_is_Some' in H6.
              apply elem_of_union.
              destruct H6.
              --- left. by apply elem_of_singleton.
              --- right. rewrite Hms. done. 
        -- rewrite size_union.
           ++ rewrite size_singleton. split; first lia.
              apply subseteq_intersection_1_L.
              rewrite union_subseteq.
              split.
              --- rewrite singleton_subseteq_l.
                  rewrite elem_of_set_seq.
                  split; simpl; try lia.
                  pose proof (fin_to_nat_lt r).
                  lia.
              --- by apply subseteq_intersection_2_L in H4. 
           ++ rewrite disjoint_singleton_l. intro. rewrite Hms in H6.
              rewrite <- H2 in H6. apply Zgt_not_le in H3; lia.
      + (* old coupon *)
        do 2 rel_pure_l.
        rel_pure_r.
        iApply ("IH" with "[Hc' Hc Hml]").
        iExists _, s, _.
        replace (Z.of_nat cntv + 1)%Z with (Z.of_nat (S cntv)) by lia.
        iFrame.
        iSplit; iPureIntro.        
        -- split; intros; try split.
           ++ apply Hms in H6 as [].
              rewrite lookup_insert_is_Some'.
              by right.
           ++ rewrite Hms. 
              rewrite lookup_insert_is_Some' in H6.
              destruct H6.
              --- subst. rewrite -H2.
                  lia.
              --- done.
        -- split; try done.
 Qed. 
    
  Lemma coupon_collection_refines_spec n:
    n > 0 ->
    ⊢ REL (coupon_collection (#n)) << spec_coupon_collection (#n): lrel_nat.
  Proof.
    intros.
    rel_pures_l.
    rel_pures_r.
    rel_alloc_r cnt' as "Hcnt'". do 2 rel_pure_r.
    rel_apply_l (refines_wp_l _ _ (init_map #())).
    wp_apply (wp_init_map with "[//]").
    iIntros (m) "Hm".
    rel_pures_l.
    rel_alloc_l cnt as "Hcnt".
    do 2 rel_pure_l.
    rewrite -/coupon_helper -/spec_coupon_helper.
    iApply (coupon_collection_refines_spec_helper with "[Hcnt' Hm Hcnt]"); [done|].
    rewrite /coupon_collection_inv. iExists 0, ∅. iFrame.
    iExists _. iFrame.
    iSplit.
    - iPureIntro. intros. split; intros; [by rewrite elem_of_empty in H0|]. 
      destruct H0 as [? H']. rewrite lookup_empty in H'.
      inversion H'. 
    - iPureIntro. split; try done.
      apply disjoint_intersection_L.
      done.
  Qed. 

  
  
  
  
End proofs.
