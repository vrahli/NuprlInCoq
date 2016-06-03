(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Mark Bickford

*)


Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_can.
Require Export per_props_top.
Require Export per_props_squash.
Require Export integer_type.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export seq_util.
Require Export per_props_cequiv2.


(*
   H |- halts(t)

     By callbyvalueApply

     H |- halts (t a)

 *)
Definition rule_callbyvalue_apply {o}
           (H : barehypotheses)
           (t a: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_halts t) ))
    [ mk_baresequent H (mk_conclax
       (mk_halts (mk_apply t a)))
    ]
    [].


Lemma rule_callbyvalue_apply_true {o} :
  forall lib (H : barehypotheses)
         (t a: @NTerm o),
    rule_true lib (rule_callbyvalue_apply H t a).
Proof.
  unfold rule_callbyvalue_apply, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.
  lsubst_tac.
  generalize_lsubstc_terms t1.
  generalize_lsubstc_terms t2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
  rename c into hasv.
  revert hyp0.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms a2.
  introv hyp.
  assert (chaltsc lib (mkc_apply t1 a1)) as ch1 by (spcast; auto).
  assert (chaltsc lib (mkc_apply t2 a2)) as ch2 by (apply hyp; auto).
  spcast.
  apply hasvaluec_mkc_apply_implies_hasvaluec in ch1.
  apply hasvaluec_mkc_apply_implies_hasvaluec in ch2.
  split.
  - (* tequality *)
    apply tequality_mkc_halts. split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_halts; sp; spcast; auto.
Qed.

(*
   H |- (<a,b> c) approx  bottom

     By applyPair

     NoSubgoals

 *)
Definition rule_apply_pair {o}
           (H : barehypotheses)
           (a b c: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_pair a b) c) mk_bottom)))
    []
    [].

Lemma rule_apply_pair_true {o} :
  forall lib (H : barehypotheses)
         (a b c: @NTerm o),
    rule_true lib (rule_apply_pair H a b c).
Proof.
  unfold rule_apply_pair, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms x1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  generalize_lsubstc_terms x2.
  assert (approxc lib (mkc_apply (mkc_pair a1 b1) x1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_pair; auto.
    - introv hvl. apply apply_pair_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_pair a2 b2) x2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_pair; auto.
    - introv hvl. apply apply_pair_not_valuelike in hvl. inversion hvl. }

  split.
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.


(*
   H |- ((inl a) b) approx  bottom

     By applyInl

     NoSubgoals

 *)
Definition rule_apply_inl {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_inl a) b) mk_bottom)))
    []
    [].

Lemma rule_apply_inl_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_inl H a b).
Proof.
  unfold rule_apply_inl, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  assert (approxc lib (mkc_apply (mkc_inl a1) b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inl; auto.
    - introv hvl. apply apply_inl_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_inl a2) b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inl; auto.
    - introv hvl. apply apply_inl_not_valuelike in hvl. inversion hvl. }

  split.
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.



(*
   H |- ((inr a) b) approx  bottom

     By applyInr

     NoSubgoals

 *)
Definition rule_apply_inr {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_inr a) b) mk_bottom)))
    []
    [].

Lemma rule_apply_inr_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_inr H a b).
Proof.
  unfold rule_apply_inr, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  assert (approxc lib (mkc_apply (mkc_inr a1) b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl. apply apply_inr_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_inr a2) b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl. apply apply_inr_not_valuelike in hvl. inversion hvl. }

  split.
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.


(*
   H |- (z b) approx bottom

     By applyInt

     H |- z in Z

 *)
Definition rule_apply_int {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply a b) mk_bottom)))
    [mk_baresequent H (mk_conclax (mk_member a mk_int))]
    [].


Lemma rule_apply_int_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_int H a b).
Proof.
  unfold rule_apply_int, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true  in Hyp0.
  pose proof (Hyp0 s1 s2 eqh sim) as hyp. clear Hyp0. exrepnd.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  rw @equality_in_member in hyp1; exrepnd.
  apply tequality_member_int in hyp0; auto.
  dup hyp1 as aint.
  unfold equality_of_int in hyp0. exrepnd. allsimpl. spcast.

  assert (approxc lib (mkc_apply a1 b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto.
    - introv hvl; apply apply_int_not_valuelike in hvl; try apply isprog_eq; tcsp.
      exists k. unfold computes_to_valc in hyp0. allsimpl. destruct hyp0. auto.
   }
  assert( approxc lib (mkc_apply a2 b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl; apply apply_int_not_valuelike in hvl; try apply isprog_eq; tcsp.
      exists k. unfold computes_to_valc in hyp4. allsimpl. destruct hyp4. auto.
  }

  split.
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.


(*
   H |- f ~ \x.f x \/ (isect (x : Base) (z : halts(x)). isint(x;True;f x <= bot)) ext (islambda(f;btrue;bfalse)

     By CallbyvalueApplyCases a x

     H |- halts(f a)
     H |- f in Base

 *)
Definition rule_callbyvalue_apply_cases {o}
           (H : barehypotheses)
           (f a : @NTerm o)
           (x z : NVar)
  :=
    mk_rule
      (mk_baresequent H (mk_concl
                           (mk_or
                              (mk_cequiv f (mk_lam x (mk_apply f (mk_var x))))
                              (mk_isect
                                 mk_base
                                 x
                                 (mk_isect
                                    (mk_halts (mk_var x))
                                    z
                                    (mk_isint (mk_var x) mk_true (mk_approx (mk_apply f (mk_var x)) mk_bottom)))))
                           (mk_islambda f mk_btrue mk_bfalse)))
      [mk_baresequent H (mk_conclax (mk_halts (mk_apply f a))),
       mk_baresequent H (mk_conclax (mk_member f mk_base))]
      [sarg_term f].

Lemma rule_callbyvalue_apply_cases_true {o} :
  forall lib (H : barehypotheses)
         (f a : @NTerm o)
         (x z : NVar)
         (nxz : x <> z)
         (nixf : !LIn x (free_vars f))
         (nizf : !LIn z (free_vars f)),
    rule_true lib (rule_callbyvalue_apply_cases H f a x z).
Proof.
  unfold rule_callbyvalue_apply_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term f)) as argf; clear cargs; autodimp argf hyp; allsimpl.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  assert (covered (mk_islambda f mk_btrue mk_bfalse) (nh_vars_hyps H)) as cov.
  { unfold covered; simpl; autorewrite with slow in *; auto. }
  exists cov.

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as ceq; clear hyp2; exrepnd.
  lsubst_tac.
  autorewrite with slow in *.

  apply tequality_mkc_member_base in ceq0; spcast.
  clear ceq1.

  apply equality_in_halts in hyp1; repnd.
  clear hyp3 hyp1.
  clear hyp0.
  spcast.

  dands.

  - apply tequality_mkc_or; dands; auto;[|].

    + apply tequality_mkc_cequiv; split; intro comp; spcast;[|].

      * eapply cequivc_trans;[apply cequivc_sym;exact ceq0|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.

      * eapply cequivc_trans;[exact ceq0|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.
        apply cequivc_sym; auto.

    + apply tequality_isect; dands; eauto 3 with slow;[].
      introv en.
      apply equality_in_base in en; spcast.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      autorewrite with slow in *.

      apply tequality_isect; dands; eauto 3 with slow;[|].

      { eapply tequality_respects_cequivc_left;
        [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
        apply tequality_mkc_halts; auto. }

      introv enh.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      autorewrite with slow in *.

      apply equality_in_halts in enh; repnd.
      clear dependent a1.
      clear dependent a'0.
      spcast.

      eapply tequality_respects_cequivc_right;
        [apply implies_cequivc_isint;
          [exact en
          |apply cequivc_refl
          |apply cequivc_decomp_approx;dands;
           [apply implies_cequivc_apply;
             [exact ceq0
             |exact en
             ]
           |apply cequivc_refl]
          ]
         |].

      rw @fold_type; eauto 3 with slow.

      apply (hasvaluec_implies_cequivc_mkc_isint
               _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
        in enh0; repndors;
      eapply type_respects_cequivc;
      try (complete (apply cequivc_sym;exact enh0));
      eauto 3 with slow.

  - eapply equality_respects_cequivc_right;
    [apply implies_cequivc_islambda;
      [exact ceq0
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

    clear dependent s2.
    rw @member_eq.

    applydup @hasvaluec_mkc_apply_implies_hasvaluec in hyp2 as hv.
    apply hasvaluec_mkc_apply2 in hyp2.
    repndors; exrepnd; spcast.

    + eapply member_respects_cequivc;
        [apply implies_cequivc_islambda;
          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp1
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply member_respects_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_islambda_mkc_lam|].
      apply member_mkc_or_inl; dands; eauto 3 with slow.

      * apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
        introv en.
        apply equality_in_base in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply tequality_isect; dands; eauto 3 with slow;[|].

        { eapply tequality_respects_cequivc_left;
          [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
          apply tequality_mkc_halts; auto. }

        introv enh.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply equality_in_halts in enh; repnd.
        clear dependent a1.
        clear dependent a'0.
        spcast.

        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_isint;
            [exact en
            |apply cequivc_refl
            |apply cequivc_decomp_approx;dands;
             [apply implies_cequivc_apply;
               [apply cequivc_refl
               |exact en
               ]
             |apply cequivc_refl]
            ]
          |].

        rw @fold_type; eauto 3 with slow.

        apply (hasvaluec_implies_cequivc_mkc_isint
                 _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
          in enh0; repndors;
        eapply type_respects_cequivc;
        try (complete (apply cequivc_sym;exact enh0));
        eauto 3 with slow.

      * apply member_cequiv.
        eapply cequivc_trans;
          [apply computes_to_valc_implies_cequivc;eauto|].

        apply implies_cequivc_lam2; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        eapply cequivc_trans;
          [|apply sp_implies_cequivc_apply;
             apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;eauto].
        eapply cequivc_trans;
          [|apply cequivc_sym;apply cequivc_beta]; auto.

    + eapply member_respects_cequivc;
        [apply implies_cequivc_islambda;
          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp0
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply member_respects_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_islambda_mkc_nseq|].
      apply member_mkc_or_inr; dands; eauto 3 with slow.

      * apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
        introv en.
        apply equality_in_base in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply tequality_isect; dands; eauto 3 with slow;[|].

        { eapply tequality_respects_cequivc_left;
          [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
          apply tequality_mkc_halts; auto. }

        introv enh.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply equality_in_halts in enh; repnd.
        clear dependent a1.
        clear dependent a'0.
        spcast.

        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_isint;
            [exact en
            |apply cequivc_refl
            |apply cequivc_decomp_approx;dands;
             [apply implies_cequivc_apply;
               [apply cequivc_refl
               |exact en
               ]
             |apply cequivc_refl]
            ]
          |].

        rw @fold_type; eauto 3 with slow.

        apply (hasvaluec_implies_cequivc_mkc_isint
                 _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
          in enh0; repndors;
        eapply type_respects_cequivc;
        try (complete (apply cequivc_sym;exact enh0));
        eauto 3 with slow.

      * apply member_in_isect; dands; eauto 3 with slow.
        introv en.
        apply equality_in_base in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.
        dands.

        { apply member_in_isect; dands; eauto 3 with slow.
          introv enh.
          apply equality_in_halts in enh; repnd.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          clear dependent a1.
          clear dependent a'0.
          spcast.

          dands.

          { eapply member_respects_cequivc_type;
            [apply implies_cequivc_isint;
              [apply cequivc_refl
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply cequivc_sym;apply sp_implies_cequivc_apply;
                apply computes_to_valc_implies_cequivc;eauto
               |apply cequivc_refl]
              ]
            |].

            apply (hasvaluec_implies_cequivc_mkc_isint2
                     _ _ mkc_true (mkc_approx (mkc_apply (mkc_nseq n) a0) mkc_bottom))
              in enh0; repndors; exrepnd;
            eapply member_respects_cequivc_type;
            try (complete (apply cequivc_sym;exact enh1));
            eauto 3 with slow.

            - apply equality_in_true; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

            - apply member_approx.
              eapply cequivc_approxc_trans;
                [apply implies_cequivc_apply;
                  [apply cequivc_refl
                  |apply computes_to_valc_implies_cequivc;eauto]
                |].
              apply approxc_assume_hasvalue; introv hvl; provefalse.

              apply hasvalue_likec_apply_nseq_implies_integer in hvl; tcsp.
              rw @computes_to_valc_iff_reduces_toc in enh0; tcsp. }

          { rw @fold_type; eauto 3 with slow.

            apply (hasvaluec_implies_cequivc_mkc_isint
                     _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
              in enh0; repndors;
            eapply type_respects_cequivc;
            try (complete (apply cequivc_sym;exact enh0));
            eauto 3 with slow. }
        }

        { apply tequality_isect; dands; eauto 3 with slow;[|].

          { eapply tequality_respects_cequivc_left;
            [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
            apply tequality_mkc_halts; auto. }

          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          eapply tequality_respects_cequivc_right;
            [apply implies_cequivc_isint;
              [exact en
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply implies_cequivc_apply;
                 [apply cequivc_refl
                 |exact en
                 ]
               |apply cequivc_refl]
              ]
            |].

          rw @fold_type; eauto 3 with slow.

          apply (hasvaluec_implies_cequivc_mkc_isint
                   _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
            in enh0; repndors;
          eapply type_respects_cequivc;
          try (complete (apply cequivc_sym;exact enh0));
          eauto 3 with slow. }

    + eapply member_respects_cequivc;
        [apply implies_cequivc_islambda;
          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp0
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply member_respects_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_islambda_mkc_ntseq|].
      apply member_mkc_or_inr; dands; eauto 3 with slow.

      * apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
        introv en.
        apply equality_in_base in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply tequality_isect; dands; eauto 3 with slow;[|].

        { eapply tequality_respects_cequivc_left;
          [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
          apply tequality_mkc_halts; auto. }

        introv enh.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply equality_in_halts in enh; repnd.
        clear dependent a1.
        clear dependent a'0.
        spcast.

        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_isint;
            [exact en
            |apply cequivc_refl
            |apply cequivc_decomp_approx;dands;
             [apply implies_cequivc_apply;
               [apply cequivc_refl
               |exact en
               ]
             |apply cequivc_refl]
            ]
          |].

        rw @fold_type; eauto 3 with slow.

        apply (hasvaluec_implies_cequivc_mkc_isint
                 _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
          in enh0; repndors;
        eapply type_respects_cequivc;
        try (complete (apply cequivc_sym;exact enh0));
        eauto 3 with slow.

      * apply member_in_isect; dands; eauto 3 with slow.
        introv en.
        apply equality_in_base in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.
        dands.

        { apply member_in_isect; dands; eauto 3 with slow.
          introv enh.
          apply equality_in_halts in enh; repnd.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          clear dependent a1.
          clear dependent a'0.
          spcast.

          dands.

          { eapply member_respects_cequivc_type;
            [apply implies_cequivc_isint;
              [apply cequivc_refl
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply cequivc_sym;apply sp_implies_cequivc_apply;
                apply computes_to_valc_implies_cequivc;eauto
               |apply cequivc_refl]
              ]
            |].

            apply (hasvaluec_implies_cequivc_mkc_isint2
                     _ _ mkc_true (mkc_approx (mkc_apply (computation_seq.mkc_ntseq n) a0) mkc_bottom))
              in enh0; repndors; exrepnd;
            eapply member_respects_cequivc_type;
            try (complete (apply cequivc_sym;exact enh1));
            eauto 3 with slow.

            - apply equality_in_true; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

            - apply member_approx.
              eapply cequivc_approxc_trans;
                [apply implies_cequivc_apply;
                  [apply cequivc_refl
                  |apply computes_to_valc_implies_cequivc;eauto]
                |].
              apply approxc_assume_hasvalue; introv hvl; provefalse.

              apply hasvalue_likec_apply_ntseq_implies_integer in hvl; tcsp.
              rw @computes_to_valc_iff_reduces_toc in enh0; tcsp. }

          { rw @fold_type; eauto 3 with slow.

            apply (hasvaluec_implies_cequivc_mkc_isint
                     _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
              in enh0; repndors;
            eapply type_respects_cequivc;
            try (complete (apply cequivc_sym;exact enh0));
            eauto 3 with slow. }
        }

        { apply tequality_isect; dands; eauto 3 with slow;[|].

          { eapply tequality_respects_cequivc_left;
            [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
            apply tequality_mkc_halts; auto. }

          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          eapply tequality_respects_cequivc_right;
            [apply implies_cequivc_isint;
              [exact en
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply implies_cequivc_apply;
                 [apply cequivc_refl
                 |exact en
                 ]
               |apply cequivc_refl]
              ]
            |].

          rw @fold_type; eauto 3 with slow.

          apply (hasvaluec_implies_cequivc_mkc_isint
                   _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
            in enh0; repndors;
          eapply type_respects_cequivc;
          try (complete (apply cequivc_sym;exact enh0));
          eauto 3 with slow. }
Qed.


(*
   H |- f ~ \x.f x

     By squiggleLambda

     H |- f <= \y.a
     H |- halts(f)

 *)
Definition rule_squiggle_lambda {o}
           (H : barehypotheses)
           (f a : @NTerm o)
           (x y : NVar)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_cequiv f (mk_lam x (mk_apply f (mk_var x))))))
      [mk_baresequent H (mk_conclax (mk_approx f (mk_lam y a))),
       mk_baresequent H (mk_conclax (mk_halts f))]
      [].

Lemma rule_squiggle_lambda_true {o} :
  forall lib (H : barehypotheses)
         (f a : @NTerm o)
         (x y : NVar)
         (nixf : !LIn x (free_vars f)),
    rule_true lib (rule_squiggle_lambda H f a x y).
Proof.
  unfold rule_squiggle_lambda, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as ceq; clear hyp2; exrepnd.
  lsubst_tac.

  allrw <- @member_cequiv_iff.
  allrw <- @member_approx_iff.
  allrw <- @member_halts_iff.
  allrw @tequality_mkc_halts.
  allrw @tequality_mkc_approx.
  allrw @tequality_mkc_cequiv.
  applydup ceq0 in ceq1; clear ceq0.
  applydup hyp0 in hyp1; clear hyp0.
  spcast.

  apply (hasvaluec_approxc_lam_implies_cequivc _ _ x) in hyp1; auto;[].
  apply (hasvaluec_approxc_lam_implies_cequivc _ _ x) in hyp2; auto;[].

  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow.
  dands; spcast; auto;[].
  split; intro h; spcast; auto.
Qed.


(*
   H |- squash(f ~ \x.f x \/ isexc(f) \/ (isect (x : Base) (z : halts(x)). isint(x;True;f x <= bot)))

     By CallbyvalueApplyCases a x

     H |- isexc(f a)
     H |- f in Base

 *)
Definition rule_isexc_apply_cases {o}
           (H : barehypotheses)
           (f a : @NTerm o)
           (x z : NVar)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax
                           (mk_squash
                              (mk_or
                                 (mk_or
                                    (mk_cequiv f (mk_lam x (mk_apply f (mk_var x))))
                                    (mk_isexc f))
                                 (mk_isect
                                    mk_base
                                    x
                                    (mk_isect
                                       (mk_halts (mk_var x))
                                       z
                                    (mk_isint (mk_var x) mk_true (mk_approx (mk_apply f (mk_var x)) mk_bottom))))))))
      [mk_baresequent H (mk_conclax (mk_isexc (mk_apply f a))),
       mk_baresequent H (mk_conclax (mk_member f mk_base))]
      [].

Lemma rule_isexc_apply_cases_true {o} :
  forall lib (H : barehypotheses)
         (f a : @NTerm o)
         (x z : NVar)
         (nxz : x <> z)
         (nixf : !LIn x (free_vars f))
         (nizf : !LIn z (free_vars f)),
    rule_true lib (rule_isexc_apply_cases H f a x z).
Proof.
  unfold rule_isexc_apply_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as ceq; clear hyp2; exrepnd.
  lsubst_tac.
  autorewrite with slow in *.

  apply tequality_mkc_member_base in ceq0; spcast.
  clear ceq1.

  rw <- @member_isexc_iff in hyp1.
  apply tequality_mkc_isexc in hyp0.
  applydup hyp0 in hyp1; clear hyp0.
  spcast.

  apply implies_tequality_equality_mkc_squash.

  - repeat (rw @tequality_mkc_or).
    rw @tequality_mkc_cequiv.
    rw @tequality_mkc_isexc.
    rw @tequality_isect.
    dands; eauto 3 with slow.

    + split; intro ceq; spcast.

      * eapply cequivc_trans;[apply cequivc_sym;exact ceq0|].
        eapply cequivc_trans;[exact ceq|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.

      * eapply cequivc_trans;[exact ceq0|].
        eapply cequivc_trans;[exact ceq|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply cequivc_sym.
        apply sp_implies_cequivc_apply; auto.

    + split; intro rexc.

      * eapply raises_exceptionc_preserves_cequivc;[exact ceq0|]; auto.

      * eapply raises_exceptionc_preserves_cequivc;[apply cequivc_sym; exact ceq0|]; auto.

    + introv en.
      apply equality_in_base_iff in en; spcast.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      autorewrite with slow in *.

      apply tequality_isect; dands; eauto 3 with slow;[|].

      { eapply tequality_respects_cequivc_left;
        [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
        apply tequality_mkc_halts; auto. }

      introv enh.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      autorewrite with slow in *.

      apply equality_in_halts in enh; repnd.
      clear dependent a1.
      clear dependent a'0.
      spcast.

      eapply tequality_respects_cequivc_right;
        [apply implies_cequivc_isint;
          [exact en
          |apply cequivc_refl
          |apply cequivc_decomp_approx;dands;
           [apply implies_cequivc_apply;
             [exact ceq0
             |exact en
             ]
           |apply cequivc_refl]
          ]
        |].

      rw @fold_type; eauto 3 with slow.

      apply (hasvaluec_implies_cequivc_mkc_isint
               _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
        in enh0; repndors;
      eapply type_respects_cequivc;
      try (complete (apply cequivc_sym;exact enh0));
      eauto 3 with slow.

  - clear dependent s2.
    apply if_raises_exceptionc_apply2 in hyp1.
    repndors.

    + rw @inhabited_type_or.
      left; dands; eauto 3 with slow.

      * rw @inhabited_type_or.
        right; dands; eauto 3 with slow;[].

        exists (@mkc_axiom o).
        apply member_isexc_iff; auto.

      * apply tequality_isect; dands; eauto 3 with slow;[].
        introv en.
        apply equality_in_base_iff in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply tequality_isect; dands; eauto 3 with slow;[|].

        { eapply tequality_respects_cequivc_left;
          [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
          apply tequality_mkc_halts; auto. }

        introv enh.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply equality_in_halts in enh; repnd.
        clear dependent a1.
        clear dependent a'0.
        spcast.

        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_isint;
            [exact en
            |apply cequivc_refl
            |apply cequivc_decomp_approx;dands;
             [apply implies_cequivc_apply;
               [apply cequivc_refl
               |exact en
               ]
             |apply cequivc_refl]
            ]
          |].

        rw @fold_type; eauto 3 with slow.

        apply (hasvaluec_implies_cequivc_mkc_isint
                 _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
          in enh0; repndors;
        eapply type_respects_cequivc;
        try (complete (apply cequivc_sym;exact enh0));
        eauto 3 with slow.

    + exrepnd.
      rw @inhabited_type_or.
      left; dands; eauto 3 with slow.

      * rw @inhabited_type_or.
        left; dands; eauto 3 with slow;[|].

        { exists (@mkc_axiom o).
          apply member_cequiv.

          repeat lsubstc_vars_as_mkcv.
          autorewrite with slow.
          apply (hasvaluec_approxc_lam_implies_cequivc _ _ _ v b); auto;[|].

          - apply computes_to_valc_implies_approxc in hyp1; tcsp.

          - eapply computes_to_valc_implies_hasvaluec; eauto. }

        { apply tequality_mkc_isexc; tcsp. }

      * apply tequality_isect; dands; eauto 3 with slow;[].
        introv en.
        apply equality_in_base_iff in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply tequality_isect; dands; eauto 3 with slow;[|].

        { eapply tequality_respects_cequivc_left;
          [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
          apply tequality_mkc_halts; auto. }

        introv enh.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        apply equality_in_halts in enh; repnd.
        clear dependent a1.
        clear dependent a'0.
        spcast.

        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_isint;
            [exact en
            |apply cequivc_refl
            |apply cequivc_decomp_approx;dands;
             [apply implies_cequivc_apply;
               [apply cequivc_refl
               |exact en
               ]
             |apply cequivc_refl]
            ]
          |].

        rw @fold_type; eauto 3 with slow.

        apply (hasvaluec_implies_cequivc_mkc_isint
                 _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
          in enh0; repndors;
        eapply type_respects_cequivc;
        try (complete (apply cequivc_sym;exact enh0));
        eauto 3 with slow.

    + exrepnd.
      rw @inhabited_type_or.
      right; dands; eauto 3 with slow.

      * exists (@mkc_axiom o).
        apply member_in_isect; dands; eauto 3 with slow.

        introv en.
        apply equality_in_base_iff in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        dands.

        { apply member_in_isect; dands; eauto 3 with slow.
          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          dands.

          { eapply member_respects_cequivc_type;
            [apply implies_cequivc_isint;
              [apply cequivc_refl
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply cequivc_sym;apply sp_implies_cequivc_apply;
                apply computes_to_valc_implies_cequivc;eauto
               |apply cequivc_refl]
              ]
            |].

            apply (hasvaluec_implies_cequivc_mkc_isint2
                     _ _ mkc_true (mkc_approx (mkc_apply (mkc_nseq n) a0) mkc_bottom))
              in enh0; repndors; exrepnd;
            eapply member_respects_cequivc_type;
            try (complete (apply cequivc_sym;exact enh1));
            eauto 3 with slow.

            - apply equality_in_true; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

            - apply member_approx.
              eapply cequivc_approxc_trans;
                [apply implies_cequivc_apply;
                  [apply cequivc_refl
                  |apply computes_to_valc_implies_cequivc;eauto]
                |].
              apply approxc_assume_hasvalue; introv hvl; provefalse.

              apply hasvalue_likec_apply_nseq_implies_integer in hvl; tcsp.
              rw @computes_to_valc_iff_reduces_toc in enh0; tcsp. }

          { rw @fold_type; eauto 3 with slow.

            apply (hasvaluec_implies_cequivc_mkc_isint
                     _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
              in enh0; repndors;
            eapply type_respects_cequivc;
            try (complete (apply cequivc_sym;exact enh0));
            eauto 3 with slow. }
        }

        { apply tequality_isect; dands; eauto 3 with slow;[|].

          { eapply tequality_respects_cequivc_left;
            [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
            apply tequality_mkc_halts; auto. }

          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          eapply tequality_respects_cequivc_right;
            [apply implies_cequivc_isint;
              [exact en
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply implies_cequivc_apply;
                 [apply cequivc_refl
                 |exact en
                 ]
               |apply cequivc_refl]
              ]
            |].

          rw @fold_type; eauto 3 with slow.

          apply (hasvaluec_implies_cequivc_mkc_isint
                   _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
            in enh0; repndors;
          eapply type_respects_cequivc;
          try (complete (apply cequivc_sym;exact enh0));
          eauto 3 with slow.
        }

      * apply tequality_mkc_or; dands; try (rw @fold_type); eauto 3 with slow.
        apply tequality_mkc_isexc; tcsp.

    + exrepnd.
      rw @inhabited_type_or.
      right; dands; eauto 3 with slow.

      * exists (@mkc_axiom o).
        apply member_in_isect; dands; eauto 3 with slow.

        introv en.
        apply equality_in_base_iff in en; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        autorewrite with slow in *.

        dands.

        { apply member_in_isect; dands; eauto 3 with slow.
          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          dands.

          { eapply member_respects_cequivc_type;
            [apply implies_cequivc_isint;
              [apply cequivc_refl
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply cequivc_sym;apply sp_implies_cequivc_apply;
                apply computes_to_valc_implies_cequivc;eauto
               |apply cequivc_refl]
              ]
            |].

            apply (hasvaluec_implies_cequivc_mkc_isint2
                     _ _ mkc_true (mkc_approx (mkc_apply (computation_seq.mkc_ntseq n) a0) mkc_bottom))
              in enh0; repndors; exrepnd;
            eapply member_respects_cequivc_type;
            try (complete (apply cequivc_sym;exact enh1));
            eauto 3 with slow.

            - apply equality_in_true; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

            - apply member_approx.
              eapply cequivc_approxc_trans;
                [apply implies_cequivc_apply;
                  [apply cequivc_refl
                  |apply computes_to_valc_implies_cequivc;eauto]
                |].
              apply approxc_assume_hasvalue; introv hvl; provefalse.

              apply hasvalue_likec_apply_ntseq_implies_integer in hvl; tcsp.
              rw @computes_to_valc_iff_reduces_toc in enh0; tcsp. }

          { rw @fold_type; eauto 3 with slow.

            apply (hasvaluec_implies_cequivc_mkc_isint
                     _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
              in enh0; repndors;
            eapply type_respects_cequivc;
            try (complete (apply cequivc_sym;exact enh0));
            eauto 3 with slow. }
        }

        { apply tequality_isect; dands; eauto 3 with slow;[|].

          { eapply tequality_respects_cequivc_left;
            [apply implies_cequivc_halts;apply cequivc_sym;eauto|].
            apply tequality_mkc_halts; auto. }

          introv enh.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          autorewrite with slow in *.

          apply equality_in_halts in enh; repnd.
          clear dependent a1.
          clear dependent a'0.
          spcast.

          eapply tequality_respects_cequivc_right;
            [apply implies_cequivc_isint;
              [exact en
              |apply cequivc_refl
              |apply cequivc_decomp_approx;dands;
               [apply implies_cequivc_apply;
                 [apply cequivc_refl
                 |exact en
                 ]
               |apply cequivc_refl]
              ]
            |].

          rw @fold_type; eauto 3 with slow.

          apply (hasvaluec_implies_cequivc_mkc_isint
                   _ _ mkc_true (mkc_approx (mkc_apply (lsubstc f wt s1 ct1) a0) mkc_bottom))
            in enh0; repndors;
          eapply type_respects_cequivc;
          try (complete (apply cequivc_sym;exact enh0));
          eauto 3 with slow.
        }

      * apply tequality_mkc_or; dands; try (rw @fold_type); eauto 3 with slow.
        apply tequality_mkc_isexc; tcsp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
