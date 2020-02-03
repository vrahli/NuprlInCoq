Require Export substc_more.
Require Export sequents_tacs.
Require Export per_props_product.
Require Export per_props_function.
Require Export per_props_squash.
Require Export per_props_equality.
Require Export per_props_nat2.
Require Export lsubstc_vars.

Require Export rules_function.
Require Export rules_product.


Hint Rewrite remove_var_nil : list.
Hint Rewrite remove_nvars_app_r : list.


Definition rule_AC00 {o}
           (P e : @NTerm o)
           (f m n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent
         H
         (mk_concl
            (mk_exists
               (mk_nat2nat)
               f
               (mk_forall
                  mk_tnat
                  n
                  (mk_apply2 P (mk_var n) (mk_apply (mk_var f) (mk_var n)))))
            (mk_pair (mk_lam n (mk_pi1 (mk_apply e (mk_var n))))
                     (mk_lam n (mk_pi2 (mk_apply e (mk_var n)))))))
      [ mk_baresequent H (mk_concl (mk_forall mk_tnat n (mk_exists mk_tnat m (mk_apply2 P (mk_var n) (mk_var m)))) e),
        mk_baresequent H (mk_conclax (mk_member P (mk_fun mk_tnat (mk_fun mk_tnat (mk_uni i))))) ]
      [].

Lemma rule_AC00_true {p} :
  forall lib
         (P e : NTerm)
         (f m n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true3 lib (rule_AC00 P e f m n H i).
Proof.
  introv d1 d2 d3 d4 d5 wf args hyps.
  simpl in *; dLin_hyp.
  unfold mk_exists.
  apply (rule_pair_formation_true3 _ _ _ _ _ _ f i); simpl.

  { admit. }
  { admit. }

  introv wa; repndors; subst; tcsp.

  { eapply rule_lambda_equality_true.

XXXXXXXXXXX
  unfold rule_AC00, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered
            (mk_pair (mk_lam n (mk_pi1 (mk_apply e (mk_var n))))
                     (mk_lam n (mk_pi2 (mk_apply e (mk_var n))))) (nh_vars_hyps H)) as cov.
  { unfold covered; simpl; autorewrite with list slow.
    eapply subvars_trans;[|exact ce0].
    apply subvars_eq; introv xx; apply in_app_iff in xx; allrw in_remove_nvars.
    repndors; tcsp. }
  exists cov.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 _ ext s1 s2 eqh sim) as hh; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 _ ext s1 s2 eqh sim) as qq; exrepnd; clear hyp2.

  allunfold @mk_forall.
  allunfold @mk_exists.
  allunfold @mk_nat2nat.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in qq0; auto;[].
  allrw @tequality_mkc_member_sp; repnd.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.

  dands.

  - apply tequality_mkc_squash.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    apply tequality_product; dands.
    { apply type_nat2nat. }

    introv ext' eqf.
    repeat lsubstc_vars_as_mkcv.
    repeat (rw @substc_mkcv_function; auto;[]).
    autorewrite with slow.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_apply.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto;[]).
    repeat (rw @substc2_mk_cv_app_l; auto;[]).
    allrw @mkc_var_substc.

    apply tequality_function; dands; eauto 3 with slow.
    { apply tnat_type. }

    introv ext'' eqn.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @mkcv_apply_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_squash.
    apply equality_in_fun in qq0; repnd.
    applydup qq0 in eqn; eauto 3 with slow;[].
    lsubst_tac.
    apply equality_in_fun in eqn0; repnd.
    pose proof (eqn0 _ (lib_extends_refl _) (mkc_apply a a0) (mkc_apply a' a'0)) as q.
    allrw @lsubstc_mkc_tnat.
    autodimp q hyp.
    { apply equality_nat2nat_apply; eauto 3 with slow. }
    allrw <- @mkc_apply2_eq.
    apply equality_in_uni in q; auto.

  - apply equality_in_mkc_squash; dands; spcast; eauto 3 with slow.

    SearchAbout equality mkc_squash.

    pose proof (axiom_of_choice_00 lib f n m (lsubstc P wt s1 ct1)) as ac.
    repeat (autodimp ac hyp).

    + (* from qq1 *)
      introv m1 m2.
      apply equality_in_fun in qq1; repnd.
      pose proof (qq1 a a) as h.
      autodimp h hyp.
      lsubst_tac.
      allrw @lsubstc_mkc_tnat.
      apply equality_in_fun in h; repnd.
      pose proof (h b b) as q.
      autodimp q hyp.
      apply equality_in_uni in q; auto.
      allrw <- @mkc_apply2_eq; auto.

    + (* from hh1 *)
      apply equality_refl in hh1.
      exists (lsubstc e wfce1 s1 pt0).

      repeat lsubstc_vars_as_mkcv.
      auto.

    + repeat lsubstc_vars_as_mkcv.

      dands;
        [|allunfold @mkc_exists; allunfold @mkcv_forall;
          eapply inhabited_type_respects_alphaeqc;[|exact ac];
          apply alphaeqc_mkc_product1;
          apply alphaeqc_sym; apply lsubstc_mk_nat2nat].
Qed.
