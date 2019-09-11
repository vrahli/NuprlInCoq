(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
           Abhishek Anand

*)


Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export subst_tacs3.
Require Export cequiv_tacs.
Require Export cequiv_props3.
Require Export per_props_equality.
Require Export per_props_product.
Require Export per_props_nat.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export sequents_util.
Require Export rules_tyfam.
Require Export lsubst_hyps.
Require Export terms_pi.




(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)

(* begin hide *)


(* end hide *)

(* [24] ============ PRODUCT EQUALITY ============ *)

(**
<<
   H |- x1:a1 * b1 = x2:a2 * b2 in Type(i)

     By productEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_product_equality {p}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_product a1 x1 b1)
                      (mk_product a2 x2 b2)
                      (mk_uni i))))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality a1 a2 (mk_uni i))),
      mk_baresequent
        (snoc H (mk_hyp y a1))
        (mk_conclax (mk_equality
                       (subst b1 x1 (mk_var y))
                       (subst b2 x2 (mk_var y))
                       (mk_uni i)))
    ]
    [ sarg_var y ].

Lemma rule_product_equality_true {pp} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses pp,
    rule_true lib (rule_product_equality
                     a1 a2 b1 b2
                     x1 x2 y
                     i
                     H).
Proof.
  intros.
  apply (rule_tyfam_equality_true _ _ mkc_product); auto.

  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.

  - introv; apply lsubstc_mk_product_ex.

  - introv x; apply equality_product.
Qed.

(* begin hide *)

Lemma rule_product_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H,
    @rule_true_if o lib (rule_product_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_product_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Inductive cequiv_ext_subst {p} (lib : @library p) : @CSub p -> @CSub p -> Type :=
  | ceq_ext_sub_nil : cequiv_ext_subst lib [] []
  | ceq_ext_sub_cons :
    forall v t1 t2 s1 s2,
      ccequivc_ext lib t1 t2
      -> cequiv_ext_subst lib s1 s2
      -> cequiv_ext_subst lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors cequiv_ext_subst.

Lemma cequiv_ext_subst_implies_cequiv_subst {o} :
  forall lib lib' (sub1 sub2 : @CSub o),
    lib_extends lib' lib
    -> cequiv_ext_subst lib sub1 sub2
    -> cequiv_subst lib' (csub2sub sub1) (csub2sub sub2).
Proof.
  induction sub1; introv ext ceq; simpl in *.
  { inversion ceq; subst; simpl in *; auto. }

  inversion ceq as [|? ? ? ? ? ceqa ceqb]; subst; simpl in *; clear ceq.
  constructor; auto.
  apply cequiv_stable; apply ceqa; auto.
Qed.
Hint Resolve cequiv_ext_subst_implies_cequiv_subst : slow.

Lemma ccequivc_ext_lsubst {o} :
  forall lib (t : @NTerm o) w sub1 sub2 c1 c2,
    cequiv_ext_subst lib sub1 sub2
    -> ccequivc_ext lib (lsubstc t w sub1 c1) (lsubstc t w sub2 c2).
Proof.
  introv ceq ext; spcast.
  unfold cequivc; simpl.
  apply cequiv_lsubst; eauto 2 with slow;[|].

  { apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
    rw @cover_vars_eq in c1; rw subvars_eq in c1; auto.
    rw @dom_csub_eq; auto. }

  { apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
    rw @cover_vars_eq in c2; rw subvars_eq in c2; auto.
    rw @dom_csub_eq; auto. }
Qed.

Lemma cequiv_ext_subst_refl {o} :
  forall lib (s : @CSub o), cequiv_ext_subst lib s s.
Proof.
  induction s; auto.
  destruct a; constructor; eauto 2 with slow.
Qed.
Hint Resolve cequiv_ext_subst_refl : slow.

Lemma implies_ccequivc_ext_mkc_spread1 {o} :
  forall lib (t1 t2 : @CTerm o) a b  (u : CVTerm [a, b]),
    ccequivc_ext lib t1 t2
    -> ccequivc_ext lib (mkc_spread t1 a b u) (mkc_spread t2 a b u).
Proof.
  introv ceq ext; apply ceq in ext; clear ceq; spcast.
  apply implies_cequivc_mkc_spread1; auto.
Qed.

Lemma ccequivc_ext_mkc_spread_mkc_pair {o} :
  forall lib (a b : @CTerm o) u v t,
    ccequivc_ext
      lib
      (mkc_spread (mkc_pair a b) u v t)
      (lsubstc2 u a v b t).
Proof.
  introv ext; spcast; apply cequivc_mkc_spread_mkc_pair.
Qed.


(* end hide *)



(* [17] ============PRODUCT ELIMINATION ============ *)

(**


<<
   H, p : x:A * B[x], J |- C ext spread(p; a,b. e)

     By perProductElimination a b

     H, p : x:A * B[x], a:A, b: B[a], J[p\<a,b>] |- C[p\<a,b>] ext e
>>

 *)


Definition rule_product_elimination {o}
           (A B C e : NTerm)
           (p x a b : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp p (mk_product A x B)) ++ J)
       (mk_concl C (mk_spread (mk_var p) a b e)))
    [ mk_baresequent
        (snoc (snoc (snoc H (mk_hyp p (mk_product A x B)))
                    (mk_hyp a A))
              (mk_hyp b (subst B x (mk_var a)))
              ++ lsubst_hyps [(p,mk_pair (mk_var a) (mk_var b))] J)
        (mk_concl (subst C p (mk_pair (mk_var a) (mk_var b))) e)
    ]
    [].

Lemma rule_product_elimination_true {o} :
  forall lib (A B C e : NTerm),
  forall p x a b : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_product_elimination
                     A B C e
                     p x a b
                     H J).
Proof.
  unfold rule_product_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (covered
            (mk_spread (mk_var p) a b e)
            (nh_vars_hyps (snoc H (mk_hyp p (mk_product A x B)) ++ J))) as cv.
  { clear hyp1.
    dwfseq.
    introv i; allrw in_remove_nvars; allsimpl.
    allrw not_over_or; allrw in_app_iff; allrw in_snoc.
    repndors; repnd; GC; subst; tcsp;[].
    applydup ce in i0.
    allrw in_app_iff; allrw in_snoc.
    repndors; subst; tcsp;[].
    autorewrite with core in *; tcsp. }

  exists cv.

  (* We prove some simple facts about our sequents *)
  assert (disjoint (free_vars A) (vars_hyps J)
          # disjoint (remove_nvars [x] (free_vars B)) (vars_hyps J)
          # subset (free_vars_hyps J) (p :: vars_hyps H)
          # subset (free_vars C) (p :: vars_hyps H ++ vars_hyps J)
          # subset (free_vars e) (p :: a :: b :: nh_vars_hyps H ++ nh_vars_hyps J)

          # (x <> p -> !LIn p (free_vars B))
          # (x <> a -> !LIn a (free_vars B))
          # (x <> b -> !LIn b (free_vars B))

          # !LIn p (vars_hyps H)
          # !LIn p (vars_hyps J)
          # !LIn p (free_vars A)

          # !LIn a (free_vars C)
          # !LIn a (vars_hyps H)
          # !LIn a (vars_hyps J)
          # !LIn a (hyps_free_vars J)
          # !LIn a (free_vars_hyps J)

          # !LIn b (free_vars C)
          # !LIn b (vars_hyps H)
          # !LIn b (vars_hyps J)
          # !LIn b (hyps_free_vars J)
          # !LIn b (free_vars_hyps J)

          # (p <> a)
          # (p <> b)
          # (a <> b)) as vhyps.

  { clear hyp1.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (introv i; discover; allunfold @disjoint; discover; auto));
      try (complete (discover; allrw in_app_iff; allrw in_snoc; repndors; tcsp));
      try (complete (introv i; discover; allrw in_app_iff; allrw in_snoc; allsimpl; repndors; tcsp));
      try (complete (introv i; discover; allsimpl; allrw in_app_iff; allrw in_snoc; tcsp));
      try (complete (assert (LIn p (remove_nvars [x] (free_vars B)))
                      as i by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp));
      try (complete (assert (LIn a (remove_nvars [x] (free_vars B)))
                      as i by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp));
      try (complete (assert (LIn b (remove_nvars [x] (free_vars B)))
                      as i by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp)).
  }

  destruct vhyps as [ daj    vhyps ].
  destruct vhyps as [ dbj    vhyps ].
  destruct vhyps as [ ssj    vhyps ].
  destruct vhyps as [ ssc    vhyps ].
  destruct vhyps as [ sse    vhyps ].

  destruct vhyps as [ nipb   vhyps ].
  destruct vhyps as [ niab   vhyps ].
  destruct vhyps as [ nibb   vhyps ].

  destruct vhyps as [ niph   vhyps ].
  destruct vhyps as [ nipj   vhyps ].
  destruct vhyps as [ nipa   vhyps ].

  destruct vhyps as [ niac   vhyps ].
  destruct vhyps as [ niah   vhyps ].
  destruct vhyps as [ niaj   vhyps ].
  destruct vhyps as [ niafj1 vhyps ].
  destruct vhyps as [ niafj2 vhyps ].

  destruct vhyps as [ nibc   vhyps ].
  destruct vhyps as [ nibh   vhyps ].
  destruct vhyps as [ nibj   vhyps ].
  destruct vhyps as [ nibfj1 vhyps ].
  destruct vhyps as [ nibfj2 vhyps ].

  destruct vhyps as [ dpa    vhyps ].
  destruct vhyps as [ dpb    dab ].

  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.
  lsubst_tac.

  rw @equality_in_product in sim2; exrepnd; spcast.
  eapply all_in_ex_bar_teq_and_eq_implies_teq_and_eq.
  eapply all_in_ex_bar_modus_ponens1;try exact sim2; clear sim2; introv y sim2; exrepnd; spcast.
  substc_lsubstc_vars3.

  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1
                _ xt
                (snoc (snoc (snoc s1a0 (p,t1)) (a,a1)) (b,b1) ++ s1b)
                (snoc (snoc (snoc s2a0 (p,t2)) (a,a2)) (b,b2) ++ s2b))
    as h; clear hyp1.
  repeat (autodimp h hyp); exrepnd.

  {
    introv y' sim'.
    rw @similarity_app in sim'; exrepnd; subst.
    rw @similarity_snoc in sim'5; exrepnd; subst.
    rw @similarity_snoc in sim'7; exrepnd; subst.
    rw @similarity_snoc in sim'8; exrepnd; subst.
    allrw length_snoc; cpx.
    apply app_split in sim'0;[|repeat (rw length_snoc); omega].
    repnd; subst; cpx; simpl in *; GC; ginv.
    autorewrite with slow core in *.

    assert (!LIn a (dom_csub s1a1)) as nias1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (!LIn b (dom_csub s1a1)) as nibs1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    repeat (match goal with
              | [ H : context[htyp (mk_hyp _ _)] |- _ ] => simpl in H
              | [ H : context[hvar (mk_hyp _ _)] |- _ ] => simpl in H
            end).

    assert (lib_extends lib'1 lib') as xt' by eauto 3 with slow.

    pose proof (eqh _ xt' (snoc s2a1 (p,mkc_pair t5 t3) ++ s2b0)) as h; clear eqh.
    autodimp h hyp.

    {
      apply similarity_app.
      eexists; eexists; eexists; eexists; dands; eauto; allrw length_snoc; try omega.

      - sim_snoc; dands; auto.
        eapply equality_respects_cequivc_left;
          [apply ccequivc_ext_sym; apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow|];[].
        lsubst_tac.
        apply equality_in_product; dands; auto; eauto 3 with slow;[].

        (* WARNING *)
        apply in_ext_implies_all_in_ex_bar; introv y''.
        eexists; eexists; eexists; eexists; dands; spcast;
          try (apply computes_to_valc_refl; eauto 2 with slow);
          auto; eauto 3 with slow;[].
        repeat substc_lsubstc_vars3;[].

        assert (wf_term (@mk_var o a)) as wa.
        { eauto 3 with slow. }
        assert (cover_vars (mk_var a) (snoc (snoc s1a1 (p, t6)) (a, t4))) as cov3.
        { apply cover_vars_var.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); tcsp. }

        lsubstc_subst_aeq.
        substc_lsubstc_vars3.
        lsubst_tac.

        repeat lsubstc_snoc2.
        GC; proof_irr; auto; eauto 3 with slow.

      - assert (alpha_eq_hyps
                  (substitute_hyps
                     (snoc (snoc (snoc s1a1 (p, t6)) (a, t4)) (b, t0))
                     (lsubst_hyps [(p, mk_pair (mk_var a) (mk_var b))] J))
                  (substitute_hyps (snoc s1a1 (p,mkc_pair t4 t0)) J)) as eqsubs.
        { repeat (rw @substitute_hyps_as_lsubst_hyps).
          eapply alpha_eq_hyps_trans;[apply combine_lsubst_hyps_aeq|].
          unfold lsubst_sub; simpl.
          rw @lsubst_mk_pair; eauto 3 with slow.
          allrw @csub2sub_snoc.
          rw (cl_lsubst_snoc_not_in (@mk_var o a) b); simpl; tcsp; eauto 2 with slow;
          [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow].
          rw (@cl_lsubst_var_snoc_in o a); eauto 3 with slow;
          [|repeat (rw @dom_sub_snoc); rw in_snoc; rw @dom_csub_eq; tcsp].
          rw (@cl_lsubst_var_snoc_in o b); eauto 3 with slow;
          [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow
           |repeat (rw @dom_sub_snoc); repeat (rw in_snoc); rw @dom_csub_eq; tcsp].
          apply alpha_eq_hyps_lsubst_if_ext_eq; eauto 2 with slow.

          introv i; allsimpl.
          allrw @sub_find_snoc.

          boolvar; simpl; tcsp;
          remember (sub_find (csub2sub s1a1) v) as sf; symmetry in Heqsf;
          destruct sf; eauto 2 with slow;
          allapply @sub_find_some;
          allapply @sub_find_none2;
          allapply @in_sub_eta; repnd;
          allrw @dom_csub_eq; GC.

          - destruct niph.
            allapply @similarity_dom; repnd.
            rw <- sim'0; auto.

          - destruct_cterms; simpl; eauto 3 with slow. }

        eapply similarity_preserves_alpha_eq_hyps in sim'1;
          [| |exact eqsubs];
          [|autorewrite with slow core; auto];[].

        apply vswf_hypotheses_nil_eq in wfh.
        apply wf_hypotheses_implies_wf_hyps in wfh.
        rw @wf_hyps_app in wfh; repnd.

        eapply similarity_preserves_cequiv_open_hyps; try (exact sim'1);
        autorewrite with slow core; auto.

        + rw @substitute_hyps_as_lsubst_hyps.
          apply implies_wf_hyps_lsubst_hyps; auto.

        + introv i.
          repeat (rw @substitute_hyps_as_lsubst_hyps in i).
          repeat (rw @lsubst_hyps_as_map in i).
          rw <- @map_combine in i.
          rw in_map_iff in i; exrepnd; ginv.
          apply in_combine_same in i1; repnd; subst.
          destruct a0; unfold eq_free_vars_hyp; simpl.
          repeat (rw @free_vars_cl_lsubst; eauto 3 with slow;[]).
          allrw @csub2sub_snoc.
          allrw @dom_sub_snoc; auto.

        + repeat (rw @substitute_hyps_as_lsubst_hyps).
          apply cequiv_open_hyps_same_hyps; auto.
          repeat (rw @csub2sub_snoc).
          apply cequiv_subst_ext_snoc; simpl; eauto 2 with slow;[].
          apply ccequivc_ext_implies_cequiv_ext.
          apply ccequivc_ext_sym; eauto 3 with slow.
    }

    apply eq_hyps_app in h; exrepnd.
    apply eq_hyps_snoc in h5; exrepnd; subst.
    allrw length_snoc.
    apply app_split in h2;[|repeat (rw length_snoc); omega]; repnd; subst.
    apply app_split in h0;[|repeat (rw length_snoc); omega]; repnd; subst.
    cpx; simpl in *; GC; ginv.
    repeat (match goal with
              | [ H : context[htyp (mk_hyp _ _)] |- _ ] => simpl in H
              | [ H : context[hvar (mk_hyp _ _)] |- _ ] => simpl in H
            end).

    assert (cover_vars (subst B x (mk_var a)) (snoc (snoc s2a2 (p, t7)) (a, t5))) as cov1.
    { eapply cover_vars_change_sub;[|eauto].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in h8; repnd.
      rw h0; rw h8; auto. }

    assert (cover_vars A (snoc s2a2 (p, t7))) as cov2.
    { eapply cover_vars_change_sub;[|eauto].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in h8; repnd.
      rw h0; rw h8; auto. }

    apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    repeat (rw length_snoc); try omega;[|].

    { apply eq_hyps_snoc; simpl.
      eexists; eexists; eexists; eexists.
      exists w3 p1 cov1; dands; eauto.

      - apply eq_hyps_snoc; simpl.
        eexists; eexists; eexists; eexists.
        exists w1 p2 cov2; dands; eauto.

        + apply eq_hyps_snoc; simpl.
          eexists; eexists; eexists; eexists.
          exists w5 p0 p4; dands; eauto.
          lsubst_tac; auto.

        + lsubst_tac.
          apply tequality_product in h6; sp.

      - lsubst_tac.
        apply tequality_product in h6; repnd.
        apply h6 in sim'6; clear h6; eauto 3 with slow;[].
        repeat (substc_lsubstc_vars3;[]).

        assert (wf_term (@mk_var o a)) as wa.
        { eauto 3 with slow. }
        assert (cover_vars (mk_var a) (snoc (snoc s1a0 (p, t1)) (a, t4))) as cov3.
        { apply cover_vars_var.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); tcsp. }
        assert (cover_vars (mk_var a) (snoc (snoc s2a2 (p, t7)) (a, t5))) as cov4.
        { apply cover_vars_var.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); tcsp. }

        lsubstc_subst_aeq.
        substc_lsubstc_vars3.
        lsubstc_subst_aeq.
        substc_lsubstc_vars3.
        lsubst_tac.

        repeat lsubstc_snoc2.
        GC; proof_irr; auto.
    }

    { assert (@wf_sub o [(p, mk_pair (mk_var a) (mk_var b))]) as ws.
      { apply wf_sub_cons; auto.
        apply wf_sub_nil. }

      assert (covered_csub
                [(p, mk_pair (mk_var a) (mk_var b))]
                (snoc (snoc (snoc s1a0 (p, t1)) (a, t4)) (b, t0))) as cc1.
      { apply covered_csub_cons; dands; eauto 2 with slow;[].
        unfold covered; simpl; rw subvars_eq.
        repeat (rw @dom_csub_snoc; simpl).
        introv i; allsimpl; repeat (rw in_snoc); tcsp. }

      assert (covered_csub
                [(p, mk_pair (mk_var a) (mk_var b))]
                (snoc (snoc (snoc s2a2 (p, t7)) (a, t5)) (b, t3))) as cc2.
      { apply covered_csub_cons; dands; eauto 2 with slow;[].
        unfold covered; simpl; rw subvars_eq.
        repeat (rw @dom_csub_snoc; simpl).
        introv i; allsimpl; repeat (rw in_snoc); tcsp. }

      apply (sub_eq_hyps_snoc_subst _ _ _ _ _ _ _ ws cc1 cc2).
      simpl.
      lsubst_tac.

      repeat (rw cons_snoc).
      repeat (apply sub_eq_hyps_snoc_weak; auto;[]).
      apply sub_eq_hyps_snoc_weak_dup1;[simpl;tcsp|];[].
      apply sub_eq_hyps_snoc_weak_dup2;[simpl;tcsp|];[].

      clear_cover.

      apply sub_eq_hyps_snoc_move1; auto;
      [allapply @similarity_dom; repnd; allrw; auto|];[].
      apply sub_eq_hyps_snoc_move2; auto;
      [allapply @similarity_dom; repnd; allrw; auto|];[].
      eapply sub_eq_hyps_cequiv_csub1;
        [|eapply sub_eq_hyps_cequiv_csub2;
           [|exact h1]
        ];[|]; eauto 4 with slow.
    }
  }

  { apply similarity_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    repeat (rw length_snoc); try omega;[|].

    - sim_snoc2.
      { apply wf_term_subst; eauto 3 with slow. }
      { apply cover_vars_lsubst_if; allsimpl.
        - clear sim2; rw @cover_vars_eq in c7; rw subvars_eq in c7; rw subvars_eq.
          allsimpl; repeat (rw @dom_csub_snoc); simpl.
          eapply subset_trans;[eauto|].
          apply subset_cons2.
          repeat (apply subset_snoc_r); auto.
        - introv i; repndors; tcsp; ginv.
          apply cover_vars_var; repeat (rw @dom_csub_snoc); simpl.
          rw in_snoc; tcsp. }
      dands; auto.

      + sim_snoc2.
        { apply cover_vars_snoc_weak; auto. }
        dands; auto.

        * sim_snoc; dands; auto; eauto 3 with slow;[].
          lsubst_tac; auto.
          apply equality_in_product; dands; eauto 3 with slow;[].

          (* WARNING *)
          apply in_ext_implies_all_in_ex_bar; introv y''.
          eexists; eexists; eexists; eexists; dands; spcast;
            try (apply computes_to_valc_refl; eauto 2 with slow);
            eauto 3 with slow;[].
          repeat substc_lsubstc_vars3;[].
          clear_irr; eauto 3 with slow.

        * lsubst_tac; clear_irr; auto.

      + assert (wf_term (@mk_var o a)) as wa.
        { eauto 3 with slow. }
        assert (cover_vars (mk_var a) (snoc (snoc s1a0 (p, t1)) (a, a1))) as cov3.
        { apply cover_vars_var.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); tcsp. }
        lsubstc_subst_aeq.
        substc_lsubstc_vars3.
        lsubst_tac.
        repeat lsubstc_snoc2.
        GC; proof_irr; auto.

    - assert (!LIn a (dom_csub s1a0)) as nia.
      { allapply @similarity_dom; repnd.
        rw sim10; auto. }
      assert (!LIn b (dom_csub s1a0)) as nib.
      { allapply @similarity_dom; repnd.
        rw sim10; auto. }

      assert (alpha_eq_hyps
                (substitute_hyps
                   (snoc (snoc (snoc s1a0 (p, t1)) (a, a1)) (b, b1))
                   (lsubst_hyps [(p, mk_pair (mk_var a) (mk_var b))] J))
                (substitute_hyps (snoc s1a0 (p,mkc_pair a1 b1)) J)) as eqsubs.
      { repeat (rw @substitute_hyps_as_lsubst_hyps).
        eapply alpha_eq_hyps_trans;[apply combine_lsubst_hyps_aeq|].
        unfold lsubst_sub; simpl.
        rw @lsubst_mk_pair; eauto 3 with slow.
        allrw @csub2sub_snoc.
        rw (cl_lsubst_snoc_not_in (@mk_var o a) b); simpl; tcsp; eauto 2 with slow;
        [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow].
        rw (@cl_lsubst_var_snoc_in o a); eauto 3 with slow;
        [|repeat (rw @dom_sub_snoc); rw in_snoc; rw @dom_csub_eq; tcsp];[].
        rw (@cl_lsubst_var_snoc_in o b); eauto 3 with slow;
        [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow
         |repeat (rw @dom_sub_snoc); repeat (rw in_snoc); rw @dom_csub_eq; tcsp];[].
        apply alpha_eq_hyps_lsubst_if_ext_eq; eauto 2 with slow.

        introv i; allsimpl.
        allrw @sub_find_snoc.

        boolvar; simpl; tcsp;
        remember (sub_find (csub2sub s1a0) v) as sf; symmetry in Heqsf;
        destruct sf; eauto 2 with slow;
        allapply @sub_find_some;
        allapply @sub_find_none2;
        allapply @in_sub_eta; repnd;
        allrw @dom_csub_eq; GC.

        - destruct niph.
          allapply @similarity_dom; repnd.
          rw <- sim10; auto.

        - destruct_cterms; simpl; eauto 3 with slow. }

      eapply similarity_preserves_alpha_eq_hyps;
        [|apply alpha_eq_hyps_sym; exact eqsubs|];
        [autorewrite with slow core; auto|];[].

      apply vswf_hypotheses_nil_eq in wfh.
      apply wf_hypotheses_implies_wf_hyps in wfh.
      rw @wf_hyps_app in wfh; repnd.

      eapply similarity_preserves_cequiv_open_hyps;
        try (eapply lib_extends_preserves_similarity;[|eauto]; eauto 3 with slow);
        autorewrite with slow core; auto; eauto 3 with slow.

      + rw @substitute_hyps_as_lsubst_hyps.
        apply implies_wf_hyps_lsubst_hyps; auto.

      + introv i.
        repeat (rw @substitute_hyps_as_lsubst_hyps in i).
        repeat (rw @lsubst_hyps_as_map in i).
        rw <- @map_combine in i.
        rw in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0; unfold eq_free_vars_hyp; simpl.
        repeat (rw @free_vars_cl_lsubst; eauto 3 with slow;[]).
        allrw @csub2sub_snoc.
        allrw @dom_sub_snoc; auto.

      + repeat (rw @substitute_hyps_as_lsubst_hyps).
        apply cequiv_open_hyps_same_hyps; auto.
        repeat (rw @csub2sub_snoc).
        apply cequiv_subst_ext_snoc; eauto 2 with slow.
        apply ccequivc_ext_implies_cequiv_ext; eauto 3 with slow.
  }

  lsubst_tac.
  lsubstc_subst_aeq2.
  { rw @cover_vars_eq; simpl.
    rw subvars_eq; rw @dom_csub_app; repeat (rw @dom_csub_snoc); simpl.
    introv i; allsimpl; repndors; subst; tcsp; rw in_app_iff; repeat (rw in_snoc); tcsp. }
  substc_lsubstc_vars3.
  lsubstc_subst_aeq2.
  substc_lsubstc_vars3.
  lsubstc_subst_aeq2.
  { rw @cover_vars_eq; simpl.
    rw subvars_eq; rw @dom_csub_app; repeat (rw @dom_csub_snoc); simpl.
    introv i; allsimpl; repndors; subst; tcsp; rw in_app_iff; repeat (rw in_snoc); tcsp. }
  substc_lsubstc_vars3.

  repeat lsubstc_snoc_app.

  clear_cover.
  lsubst_tac.

  assert (!LIn p (dom_csub s1a0)) as nip1.
  { allapply @similarity_dom; repnd; allrw; auto. }
  assert (!LIn p (dom_csub s2a0)) as nip2.
  { allapply @similarity_dom; repnd; allrw; auto. }

  repeat lsubstc_snoc_move2.

  (* some cleaning up *)
  proof_irr.
  clear_cover.

  dands.

  { eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact h0] ];
      apply ccequivc_ext_lsubst.

    - constructor; eauto 2 with slow;[].
      apply ccequivc_ext_sym; eauto 2 with slow.

    - constructor; eauto 2 with slow;[].
      apply ccequivc_ext_sym; eauto 2 with slow.
  }

  { eapply equality_respects_cequivc_left;
      [apply implies_ccequivc_ext_mkc_spread1;apply ccequivc_ext_sym;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto 3 with slow
      |];[].
    eapply equality_respects_cequivc_right;
      [apply implies_ccequivc_ext_mkc_spread1;apply ccequivc_ext_sym;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto 3 with slow
      |];[].
    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym;apply ccequivc_ext_mkc_spread_mkc_pair |];[].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym;apply ccequivc_ext_mkc_spread_mkc_pair |];[].

    eapply equality_respects_cequivc_left;
      [|eapply equality_respects_cequivc_right;
         [|eapply cequivc_preserving_equality;
            [exact h1|]
         ]
      ].

    - introv x'; spcast.
      unfold cequivc; simpl.
      rw @csubst_app; simpl.
      apply alpha_implies_cequiv.

      + apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
        rw @dom_csub_eq; simpl.
        repeat (rw @dom_csub_app).
        repeat (rw @dom_csub_snoc); simpl.
        allapply @similarity_dom; repnd; allrw.
        autorewrite with core slow.
        eauto 3 with slow.
        eapply subset_trans;[eauto|].

        introv i; allsimpl;
        repeat (rw in_app_iff in i);
        repeat (rw in_app_iff);
        repeat (rw in_snoc);
        sp; subst; allapply @subset_hs_vars_hyps; tcsp.

      + apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
        rw @dom_csub_eq; simpl.
        repeat (rw @dom_csub_app).
        rw @dom_csub_csub_filter.
        repeat (rw @dom_csub_app).
        repeat (rw @dom_csub_snoc); simpl.
        allapply @similarity_dom; repnd; allrw.
        autorewrite with core slow.
        eapply subset_trans;[eauto|].

        introv i; allsimpl;
        repeat (rw in_app_iff in i);
        repeat (rw in_app_iff);
        repeat (rw in_remove_nvars);
        repeat (rw in_app_iff);
        repeat (rw in_snoc);
        simpl; repeat (rw not_over_or);
        sp; subst; allapply @subset_hs_vars_hyps; tcsp;
        destruct (deq_nvar x0 a) as [d|d]; subst; tcsp;
        destruct (deq_nvar x0 b) as [q|q]; subst; tcsp;
        try (complete (left; dands; tcsp)).

      + apply alpha_eq_lsubst_if_ext_eq; auto;[].
        introv i.
        repeat (rw <- @csub2sub_app); simpl.
        rw <- @sub_filter_csub2sub.
        repeat (rw <- @csub2sub_app); simpl.
        repeat (rw @csub2sub_snoc); simpl.
        rw @sub_filter_app.
        rw @sub_filter_snoc; simpl.
        repeat (rw memvar_cons).
        boolvar; tcsp;[]; GC.
        repeat (rw @sub_filter_disjoint1;
                [|rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw;
                  autorewrite with core slow;
                  repeat (rw disjoint_cons_r); dands; tcsp; fail]).
        repeat (rw @sub_find_app).
        repeat (rw @sub_find_snoc); simpl.

        boolvar; tcsp;
          remember (sub_find (csub2sub s1a0) v) as sf;
          symmetry in Heqsf; destruct sf; eauto 3 with slow;
            remember (sub_find (csub2sub s1b) v) as sg;
            symmetry in Heqsg; destruct sg; eauto 3 with slow;
              try subst v; tcsp;
                provefalse;
                allapply @sub_find_some;
                allapply @in_sub_eta;
                allrw @dom_csub_eq;
                revert Heqsf; revert Heqsg;
                  allapply @similarity_dom; repnd; allrw;
                    autorewrite with slow core; tcsp.

    - introv x'; spcast.
      unfold cequivc; simpl.
      rw @csubst_app; simpl.
      apply alpha_implies_cequiv.

      + apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
        rw @dom_csub_eq; simpl.
        repeat (rw @dom_csub_app).
        repeat (rw @dom_csub_snoc); simpl.
        allapply @similarity_dom; repnd; allrw.
        autorewrite with core slow.
        eauto 3 with slow.
        eapply subset_trans;[eauto|].

        introv i; allsimpl;
        repeat (rw in_app_iff in i);
        repeat (rw in_app_iff);
        repeat (rw in_snoc);
        sp; subst; allapply @subset_hs_vars_hyps; tcsp.

      + apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
        rw @dom_csub_eq; simpl.
        repeat (rw @dom_csub_app).
        rw @dom_csub_csub_filter.
        repeat (rw @dom_csub_app).
        repeat (rw @dom_csub_snoc); simpl.
        allapply @similarity_dom; repnd; allrw.
        autorewrite with core slow.
        eapply subset_trans;[eauto|].

        introv i; allsimpl;
        repeat (rw in_app_iff in i);
        repeat (rw in_app_iff);
        repeat (rw in_remove_nvars);
        repeat (rw in_app_iff);
        repeat (rw in_snoc);
        simpl; repeat (rw not_over_or);
        sp; subst; allapply @subset_hs_vars_hyps; tcsp;
        destruct (deq_nvar x0 a) as [d|d]; subst; tcsp;
        destruct (deq_nvar x0 b) as [q|q]; subst; tcsp;
        try (complete (left; dands; tcsp)).

      + apply alpha_eq_lsubst_if_ext_eq; auto;[].
        introv i.
        repeat (rw <- @csub2sub_app); simpl.
        rw <- @sub_filter_csub2sub.
        repeat (rw <- @csub2sub_app); simpl.
        repeat (rw @csub2sub_snoc); simpl.
        rw @sub_filter_app.
        rw @sub_filter_snoc; simpl.
        repeat (rw memvar_cons).
        boolvar; tcsp;[]; GC.
        repeat (rw @sub_filter_disjoint1;
                [|rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw;
                  autorewrite with core slow;
                  repeat (rw disjoint_cons_r); dands; tcsp; fail]).
        repeat (rw @sub_find_app).
        repeat (rw @sub_find_snoc); simpl.

        boolvar; tcsp;
          remember (sub_find (csub2sub s2a0) v) as sf;
          symmetry in Heqsf; destruct sf; eauto 3 with slow;
            remember (sub_find (csub2sub s2b) v) as sg;
            symmetry in Heqsg; destruct sg; eauto 3 with slow;
              try subst v; tcsp;
                provefalse;
                allapply @sub_find_some;
                allapply @in_sub_eta;
                allrw @dom_csub_eq;
                revert Heqsf; revert Heqsg;
                  allapply @similarity_dom; repnd; allrw;
                    autorewrite with slow core; tcsp.

    - apply ccequivc_ext_lsubst;[].
      constructor; eauto 2 with slow;[].
      apply ccequivc_ext_sym; eauto 2 with slow.
  }
Qed.


(* begin hide *)


Lemma rule_product_elimination_true_ex {o} :
  forall lib (A B C e : NTerm),
  forall p x a b : NVar,
  forall H J : @barehypotheses o,
    rule_true_if lib (rule_product_elimination
                        A B C e
                        p x a b
                        H J).
Proof.
  intros.
  pose proof (rule_product_elimination_true lib A B C e p x a b H J) as rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.


(* end hide *)



(* [23] ============ PAIR FORMATION ============ *)

(**

<<
   H |- x:A * B ext <a,b>

     By pairFormation lvl(i) s z ()

     H |- a in A
     H |- B[x\a] ext b
     H, z : A |- B[x\z] in U(i)
>>

 *)

Definition rule_pair_formation {p}
           (A B a b : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_product A x B) (mk_pair a b)))
    [ mk_baresequent H (mk_conclax (mk_member a A)),
      mk_baresequent H (mk_concl (subst B x a) b),
      mk_baresequent (snoc H (mk_hyp z A))
                     (mk_conclax (mk_member (subst B x (mk_var z)) (mk_uni i))) ]
    [sarg_var z, sarg_term a].


Lemma rule_pair_formation_true {p} :
  forall lib (A B a b : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses p),
    rule_true lib (rule_pair_formation A B a b x z i H).
Proof.
  intros.
  unfold rule_pair_formation, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_var z)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a)) as arg2; autodimp arg2 hyp.
  clear cargs.
  allunfold @arg_constraints; GC.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_concl (mk_product A x B) (mk_pair a b))) as cp.
  { clear hyp1 hyp2 hyp3.
    unfold closed_extract; simpl.
    allunfold @covered; allsimpl.
    autorewrite with slow core in *.
    allrw subvars_app_l; repnd; dands; auto. }

  exists cp; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2 hyp3.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (assert (LIn z (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp)). }

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.

  assert (in_ext lib' (fun lib => forall s3,
            similarity lib s1 s3 H
            -> {ca3 : cover_vars A s3
                & {cb3 : cover_vars_upto B (csub_filter s3 [x]) [x]
                & tequality
                    lib
                    (mkc_product (lsubstc A w1 s1 c1) x
                                 (lsubstc_vars B w2 (csub_filter s1 [x]) [x] c2))
                    (mkc_product (lsubstc A w1 s3 ca3) x
                                 (lsubstc_vars B w2 (csub_filter s3 [x]) [x] cb3)) }})) as teq.

  { introv xt sim'.
    dup sim' as ca3.
    eapply similarity_cover_vars in ca3;[|exact c1].
    dup sim' as cb3.
    eapply similarity_cover_vars_upto in cb3;[|exact c2].

    exists ca3 cb3.

    apply tequality_product; dands.

    + vr_seq_true in hyp1.
      pose proof (hyp1
                    _ (lib_extends_trans xt ext)
                    s1 s3
                    (lib_extends_preserves_hyps_functionality_ext xt _ _ eqh)
                    sim') as h; clear hyp1; exrepnd.
      lsubst_tac; proof_irr.
      clear h1.
      apply tequality_mkc_member_sp in h0; repnd; auto.

    + intros lib'' xt' a1 a2 ea.
      repeat (substc_lsubstc_vars3;[]).

      vr_seq_true in hyp3.
      pose proof (hyp3
                    _ (lib_extends_trans xt' (lib_extends_trans xt ext))
                    (snoc s1 (z,a1)) (snoc s3 (z,a2))) as h; clear hyp3.
      repeat (autodimp h hyp).

      * apply hyps_functionality_ext_snoc2; simpl; auto; eauto 3 with slow;[].
        introv xt'' equ sim''.

        vr_seq_true in hyp1.
        pose proof (hyp1
                      _ (lib_extends_trans xt'' (lib_extends_trans xt' (lib_extends_trans xt ext)))
                      s1 s'
                      (lib_extends_preserves_hyps_functionality_ext (lib_extends_trans xt'' (lib_extends_trans xt' xt)) _ _ eqh)
                      sim'') as h; clear hyp1; exrepnd.
        lsubst_tac; proof_irr.
        clear h1.
        apply tequality_mkc_member_sp in h0; repnd; auto.

      * sim_snoc; dands; auto; eauto 3 with slow.

      * exrepnd.
        lsubst_tac; proof_irr.
        apply member_if_inhabited in h1.
        apply member_in_uni in h1.
        apply tequality_in_uni_implies_tequality in h0; auto;[].

        clear h1.

        assert (cover_vars (mk_var z) (snoc s1 (z, a1))) as cov1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
        assert (cover_vars (mk_var z) (snoc s3 (z, a2))) as cov2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

        repeat lsubstc_subst_aeq.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        proof_irr; auto. }

  dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; auto; eauto 3 with slow. }

  apply equality_in_product; dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; auto; eauto 3 with slow.
    apply tequality_product in sim1; repnd.
    apply tequality_refl in sim0; auto. }

  { intros lib'' xt' a1 a2 ea.
    repeat (substc_lsubstc_vars3;[]).
    apply similarity_refl in sim.
    apply teq in sim; clear teq; exrepnd; proof_irr; eauto 3 with slow.
    apply tequality_product in sim1; repnd; proof_irr.
    apply sim1 in ea; clear sim1; eauto 3 with slow.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto. }

  apply in_ext_implies_all_in_ex_bar; introv xt.
  eexists; eexists; eexists; eexists; dands; eauto 3 with slow;[|].

  - vr_seq_true in hyp1.
    pose proof (hyp1
                  _ (lib_extends_trans xt ext)
                  s1 s2
                  (lib_extends_preserves_hyps_functionality_ext xt _ _ eqh)
                  (lib_extends_preserves_similarity xt _ _ _ sim)) as h; clear hyp1; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_member_sp in h0; repnd.
    apply member_if_inhabited in h1.
    allrw @fold_equorsq.
    eapply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;try exact h0; clear h0; introv xt' h0; exrepnd; spcast.
    eapply cequorsq_equality_trans2;[eauto|];eauto 3 with slow.

  - repeat (substc_lsubstc_vars3;[]).
    vr_seq_true in hyp2.
    pose proof (hyp2
                  _ (lib_extends_trans xt ext)
                  s1 s2
                  (lib_extends_preserves_hyps_functionality_ext xt _ _ eqh)
                  (lib_extends_preserves_similarity xt _ _ _ sim)) as h; clear hyp2; exrepnd.

    repeat lsubstc_subst_aeq.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto.
Qed.

(* begin hide *)

Lemma rule_pair_formation_true_ex {p} :
  forall lib i z A B a b x H,
    @rule_true_if p lib (rule_pair_formation A B a b x z i H).
Proof.
  intros.
  generalize (rule_pair_formation_true lib A B a b x z i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.



(* end hide *)


(* ============ PAIR EQUALITY ============ *)

(**

<<

   H |- <a1,b1> = <a2,b2> in x:A*B

     By pairEquality lvl(i) z ()

     H |- a1 = a2 in A
     H |- b1 = b2 in B[x\a1]
     H, z : A |- B[x\z] in Type(i)
>>
 *)

Definition rule_pair_equality {o}
           (A B a1 a2 b1 b2 : NTerm)
           (x z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_pair a1 b1)
                      (mk_pair a2 b2)
                      (mk_product A x B))))
    [ mk_baresequent H (mk_conclax (mk_equality a1 a2 A)),
      mk_baresequent H (mk_conclax (mk_equality b1 b2 (subst B x a1))),
      mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_member
                       (subst B x (mk_var z))
                       (mk_uni i))) ]
    [sarg_var z].

Lemma rule_pair_equality_true {o} :
  forall lib (A B a1 a2 b1 b2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true lib (rule_pair_equality A B a1 a2 b1 b2 x z i H).
Proof.
  intros.
  unfold rule_pair_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2 hyp3.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (assert (LIn z (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp)). }

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw <- @member_equality_iff.

  assert (in_ext lib' (fun lib => forall s1 s2,
            hyps_functionality_ext lib s1 H ->
            similarity lib s1 s2 H
            -> {ca1 : cover_vars A s1
                & {cb1 : cover_vars_upto B (csub_filter s1 [x]) [x]
                & {ca2 : cover_vars A s2
                & {cb2 : cover_vars_upto B (csub_filter s2 [x]) [x]
                & tequality
                    lib
                    (mkc_product (lsubstc A w0 s1 ca1) x
                                 (lsubstc_vars B w3 (csub_filter s1 [x]) [x] cb1))
                    (mkc_product (lsubstc A w0 s2 ca2) x
                                 (lsubstc_vars B w3 (csub_filter s2 [x]) [x] cb2)) }}}})) as teq.

  { introv xt eqh' sim'.
    dup sim' as ca.
    eapply lib_extends_preserves_similarity in sim;[|exact xt].
    eapply similarity_cover_vars2 in ca;[|exact sim|exact c4]; repnd; GC;[].
    dup sim' as cb.
    eapply similarity_cover_vars_upto2 in cb;[|exact sim|exact c5]; repnd; GC;[].

    exists ca1 cb1 ca cb.

    apply tequality_product; dands.

    + vr_seq_true in hyp1.
      pose proof (hyp1 _ (lib_extends_trans xt ext) s0 s3 eqh' sim') as h; clear hyp1; exrepnd.
      lsubst_tac; proof_irr.
      clear h1.
      apply tequality_mkc_equality_sp in h0; repnd; auto.

    + intros lib'' xt' a a' ea.
      repeat (substc_lsubstc_vars3;[]).

      vr_seq_true in hyp3.
      pose proof (hyp3 _ (lib_extends_trans xt' (lib_extends_trans xt ext)) (snoc s0 (z,a)) (snoc s3 (z,a'))) as h; clear hyp3.
      repeat (autodimp h hyp).

      * apply hyps_functionality_ext_snoc2; simpl; eauto 3 with slow;[].
        introv xt'' equ sim''.

        vr_seq_true in hyp1.
        pose proof (hyp1
                      _ (lib_extends_trans xt'' (lib_extends_trans xt' (lib_extends_trans xt ext)))
                      s0 s'
                      (lib_extends_preserves_hyps_functionality_ext (lib_extends_trans xt'' xt') _ _ eqh')
                      sim'') as h; clear hyp1; exrepnd.
        lsubst_tac; proof_irr.
        clear h1.
        apply tequality_mkc_equality_sp in h0; repnd; auto.

      * sim_snoc; dands; eauto 3 with slow.

      * exrepnd.
        lsubst_tac; proof_irr.
        apply member_if_inhabited in h1.
        apply member_in_uni in h1.
        apply tequality_in_uni_implies_tequality in h0; auto;[].

        clear h1.

        assert (cover_vars (mk_var z) (snoc s0 (z, a))) as cov1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
        assert (cover_vars (mk_var z) (snoc s3 (z, a'))) as cov2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

        repeat lsubstc_subst_aeq.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        proof_irr; auto. }

  pose proof (teq_and_eq_if_equality
                lib' (mk_product A x B) (mk_pair a1 b1) (mk_pair a2 b2)
                s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0
                eqh sim) as eqp.
  repeat (autodimp eqp hyp); auto;
  [| |lsubst_tac; clear_irr; auto];[|].

  { lsubst_tac; clear_irr.
    apply teq in sim; clear teq; exrepnd; proof_irr; eauto 3 with slow. }

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply equality_in_product; dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; eauto 3 with slow.
    apply tequality_product in sim1; repnd.
    apply tequality_refl in sim0; auto. }

  { intros lib'' xt' a a' ea.
    repeat (substc_lsubstc_vars3;[]).
    apply similarity_refl in sim.
    apply teq in sim; auto; clear teq; exrepnd; proof_irr; eauto 3 with slow.
    apply tequality_product in sim1; repnd; proof_irr.
    apply sim1 in ea; clear sim1; eauto 3 with slow.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto. }

  apply in_ext_implies_all_in_ex_bar; introv xt.
  eexists; eexists; eexists; eexists; dands; eauto 3 with slow;[|].

  - vr_seq_true in hyp1.
    pose proof (hyp1
                  _ (lib_extends_trans xt ext)
                  s1 s2
                  (lib_extends_preserves_hyps_functionality_ext xt _ _ hf)
                  (lib_extends_preserves_similarity xt _ _ _ sim)) as h; clear hyp1; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_equality_sp in h0; repnd.
    rw <- @member_equality_iff in h1.
    allrw @fold_equorsq.
    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;try exact h0; clear h0; introv xt' h0; exrepnd; spcast.
    eapply cequorsq_equality_trans2;[eauto|];eauto 3 with slow.

  - repeat (substc_lsubstc_vars3;[]).
    vr_seq_true in hyp2.
    pose proof (hyp2
                  _ (lib_extends_trans xt ext)
                  s1 s2
                  (lib_extends_preserves_hyps_functionality_ext xt _ _ hf)
                  (lib_extends_preserves_similarity xt _ _ _ sim)) as h; clear hyp2; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_equality_sp in h0; repnd.
    rw <- @member_equality_iff in h1.
    clear h2.

    assert (cover_vars a1 s2) as cov.
    { eapply similarity_cover_vars in sim; eauto. }

    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens2;[|exact h0|exact h3]; clear h0 h3; introv xt' h0 h3; exrepnd; spcast.

    allrw @fold_equorsq.
    repeat lsubstc_subst_aeq.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto.

    eapply equality_monotone in h1;[|exact xt'].
    eapply cequorsq_equality_trans2;[eauto|]; eauto 3 with slow.
Qed.


(* ============ SPREAD EQUALITY ============ *)

(**

<<
   H |- let x1,y1 = e1 in t1 = let x2,y2 = e2 in t2 in C[z\e1]

     By spreadEquality ()

     H |- e1 = e2 in x:A*B
     H, a : A, b : B[x\a], y : e1 = <a,b> in x:A*B  |- t1[x1,y1\a,b] = t2[x2,y2\a,b] in C[z\<a,b>]
>>
 *)

Definition rule_spread_equality {o}
           (A B e1 e2 t1 t2 C : NTerm)
           (x x1 x2 y1 y2 z a b y : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality
                                     (mk_spread e1 x1 y1 t1)
                                     (mk_spread e2 x2 y2 t2)
                                     (subst C z e1))))
    [ mk_baresequent H (mk_conclax (mk_equality e1 e2 (mk_product A x B))),
      mk_baresequent
        (snoc (snoc (snoc H (mk_hyp a A))
                    (mk_hyp b (subst B x (mk_var a))))
              (mk_hyp y (mk_equality e1 (mk_pair (mk_var a) (mk_var b)) (mk_product A x B))))
        (mk_conclax (mk_equality
                       (lsubst t1 [(x1,mk_var a),(y1,mk_var b)])
                       (lsubst t2 [(x2,mk_var a),(y2,mk_var b)])
                       (subst C z (mk_pair (mk_var a) (mk_var b)))))
    ]
    [].

Lemma rule_spread_equality_true {o} :
  forall lib
         (A B e1 e2 t1 t2 C : NTerm)
         (x x1 x2 y1 y2 z a b y : NVar)
         (H   : @barehypotheses o),
    rule_true lib (rule_spread_equality A B e1 e2 t1 t2 C x x1 x2 y1 y2 z a b y H).
Proof.
  intros.
  unfold rule_spread_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert ((a <> x -> !LIn a (free_vars B))
          # (b <> x -> !LIn b (free_vars B))
          # (y <> x -> !LIn y (free_vars B))

          # (a <> z -> !LIn a (free_vars C))
          # (b <> z -> !LIn b (free_vars C))
          # (y <> z -> !LIn y (free_vars C))

          # (!LIn a [x1,y1] -> !LIn a (free_vars t1))
          # (!LIn b [x1,y1] -> !LIn b (free_vars t1))
          # (!LIn y [x1,y1] -> !LIn y (free_vars t1))

          # (!LIn a [x2,y2] -> !LIn a (free_vars t2))
          # (!LIn b [x2,y2] -> !LIn b (free_vars t2))
          # (!LIn y [x2,y2] -> !LIn y (free_vars t2))

          # subset (free_vars C) (z :: vars_hyps H)
          # subset (free_vars t1) (x1 :: y1 :: vars_hyps H)
          # subset (free_vars t2) (x2 :: y2 :: vars_hyps H)

          # a <> b
          # a <> y
          # b <> y

          # !LIn a (free_vars A)
          # !LIn b (free_vars A)
          # !LIn y (free_vars A)

          # !LIn a (free_vars e1)
          # !LIn b (free_vars e1)
          # !LIn y (free_vars e1)

          # !LIn a (free_vars e2)
          # !LIn b (free_vars e2)
          # !LIn y (free_vars e2)

          # !LIn a (vars_hyps H)
          # !LIn b (vars_hyps H)
          # !LIn y (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (assert (LIn a (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp));
      try (complete (assert (LIn b (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp));
      try (complete (assert (LIn y (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp));
      try (complete (assert (LIn a (remove_nvars [z] (free_vars C)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     assert (LIn a (free_vars (subst C z e1)))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn b (remove_nvars [z] (free_vars C)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     assert (LIn b (free_vars (subst C z e1)))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn y (remove_nvars [z] (free_vars C)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     assert (LIn y (free_vars (subst C z e1)))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (intros xx i; simpl; destruct (deq_nvar z xx) as [d|d]; tcsp;
                     assert (LIn xx (free_vars (subst C z e1)))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; left;
                                rw in_remove_nvars; simpl; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn a (remove_nvars [x1,y1] (free_vars t1)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn a (free_vars (lsubst t1 [(x1, mk_var a), (y1, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn b (remove_nvars [x1,y1] (free_vars t1)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn b (free_vars (lsubst t1 [(x1, mk_var a), (y1, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn y (remove_nvars [x1,y1] (free_vars t1)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn y (free_vars (lsubst t1 [(x1, mk_var a), (y1, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn a (remove_nvars [x2,y2] (free_vars t2)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn a (free_vars (lsubst t2 [(x2, mk_var a), (y2, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn b (remove_nvars [x2,y2] (free_vars t2)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn b (free_vars (lsubst t2 [(x2, mk_var a), (y2, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (assert (LIn y (remove_nvars [x2,y2] (free_vars t2)))
                      as j by (rw in_remove_nvars; simpl; tcsp);
                     assert (LIn y (free_vars (lsubst t2 [(x2, mk_var a), (y2, mk_var b)])))
                       as k by (apply eqset_free_vars_disjoint; simpl; rw in_app_iff; tcsp);
                     discover; tcsp));
      try (complete (intros xx i; simpl;
                     destruct (deq_nvar x1 xx) as [d|d]; tcsp;[];
                     destruct (deq_nvar y1 xx) as [q|q]; tcsp;[];
                     assert (LIn xx (remove_nvars [x1, y1] (free_vars t1)))
                       as k by (rw in_remove_nvars; simpl; tcsp);
                     discover; tcsp));
      try (complete (intros xx i; simpl;
                     destruct (deq_nvar x2 xx) as [d|d]; tcsp;[];
                     destruct (deq_nvar y2 xx) as [q|q]; tcsp;[];
                     assert (LIn xx (remove_nvars [x2, y2] (free_vars t2)))
                       as k by (rw in_remove_nvars; simpl; tcsp);
                     discover; tcsp)). }

  destruct vhyps as [ naxB vhyps ].
  destruct vhyps as [ nbxB vhyps ].
  destruct vhyps as [ nyxB vhyps ].

  destruct vhyps as [ naxC vhyps ].
  destruct vhyps as [ nbxC vhyps ].
  destruct vhyps as [ nyxC vhyps ].

  destruct vhyps as [ nat1 vhyps ].
  destruct vhyps as [ nbt1 vhyps ].
  destruct vhyps as [ nyt1 vhyps ].

  destruct vhyps as [ nat2 vhyps ].
  destruct vhyps as [ nbt2 vhyps ].
  destruct vhyps as [ nyt2 vhyps ].

  destruct vhyps as [ ssC  vhyps ].
  destruct vhyps as [ sst1 vhyps ].
  destruct vhyps as [ sst2 vhyps ].

  destruct vhyps as [ nab vhyps ].
  destruct vhyps as [ nay vhyps ].
  destruct vhyps as [ nby vhyps ].

  destruct vhyps as [ naA vhyps ].
  destruct vhyps as [ nbA vhyps ].
  destruct vhyps as [ nyA vhyps ].

  destruct vhyps as [ nae1 vhyps ].
  destruct vhyps as [ nbe1 vhyps ].
  destruct vhyps as [ nye1 vhyps ].

  destruct vhyps as [ nae2 vhyps ].
  destruct vhyps as [ nbe2 vhyps ].
  destruct vhyps as [ nye2 vhyps ].

  destruct vhyps as [ naH vhyps ].
  destruct vhyps as [ nbH nyH ].
  (* done with proving these simple facts *)

  vr_seq_true.

  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                lib' (subst C z e1)
                (mk_spread e1 x1 y1 t1)
                (mk_spread e2 x2 y2 t2)
                s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0
                eqh
                sim) as eqp.
  repeat (autodimp eqp hyp); auto;[| |lsubst_tac; clear_irr; auto];[|].

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 eqh sim) as h; exrepnd; proof_irr.
    lsubst_tac.
    rw <- @member_equality_iff in h1.
    apply equality_commutes3 in h0;auto;[].
    clear h1.

    apply equality_in_product in h0; repnd.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens1;try exact h0; clear h0; introv xt' h0; exrepnd; spcast; proof_irr.

    apply (lib_extends_preserves_hyps_functionality_ext xt') in eqh.
    apply (lib_extends_preserves_similarity xt') in sim.

    vr_seq_true in hyp2.
    pose proof (hyp2
                  _
                  (lib_extends_trans xt' ext)
                  (snoc (snoc (snoc s1 (a,a1)) (b,b1)) (y,mkc_axiom))
                  (snoc (snoc (snoc s2 (a,a2)) (b,b2)) (y,mkc_axiom))) as q.
    clear hyp2.
    repeat (autodimp q hyp).

    + apply hyps_functionality_ext_snoc2; simpl; auto.

      * introv xt'' equ sim'.
        lsubst_tac.

        apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.
        apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.

        revert c22 c24 c25 c26 c27.
        repeat (rw (@hvar_mk_hyp o)); introv.
        lsubst_tac; clear_irr.
        apply equality_refl in equ.
        rw <- @member_equality_iff in equ.

        lsubstc_snoc_vs.

        apply tequality_mkc_equality_sp; dands.

        { pose proof (hyp1 _ (lib_extends_trans xt'' (lib_extends_trans xt' ext)) s1a s2a0) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow;[].
          lsubst_tac; auto.
          apply tequality_mkc_equality_sp in q0; repnd; auto. }

        { apply in_ext_implies_all_in_ex_bar; introv xt'''.
          left.
          pose proof (hyp1 _ (lib_extends_trans xt''' (lib_extends_trans xt'' (lib_extends_trans xt' ext))) s1a s2a0) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow;[].
          lsubst_tac; auto.
          rw <- @member_equality_iff in q1; auto.
          apply equality_commutes3 in q0; auto. }

        { apply in_ext_implies_all_in_ex_bar; introv xt'''.
          left.
          apply equality_in_product; dands; eauto 4 with slow;[].
          apply in_ext_implies_all_in_ex_bar; introv xt''''.
          eexists; eexists; eexists; eexists; dands; eauto 2 with slow;[|];
            try (complete (allsimpl; auto)); eauto 3 with slow;[].
          simpl in sim'1.
          lsubstc_subst_aeq2.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr; eauto 3 with slow. }

      * apply hyps_functionality_ext_snoc2; simpl; auto.

        { introv xt'' equ sim'.
          lsubst_tac.

          apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.

          revert c'.
          repeat (rw (@hvar_mk_hyp o)); introv.

          assert (cover_vars (mk_var a) (snoc s1a (a, t0))) as cov1.
          { apply cover_vars_var.
            rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          assert (cover_vars (mk_var a) (snoc s2a (a, t3))) as cov2.
          { apply cover_vars_var.
            rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr.

          pose proof (hyp1
                        _
                        (lib_extends_trans xt'' (lib_extends_trans xt' ext))
                        s1a s2a) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow;[].
          lsubst_tac; auto.
          clear q1.
          apply tequality_mkc_equality_sp in q0; repnd.
          clear q0 q2.
          apply tequality_product in q1; repnd.
          clear q0.
          pose proof (q1 _ (lib_extends_refl lib'1) t0 t3) as h; clear q1.
          autodimp h hyp;[].
          repeat (substc_lsubstc_vars3;[]).
          proof_irr; auto. }

        { apply hyps_functionality_ext_snoc2; simpl; auto;[].

          introv xt'' equ sim'.

          pose proof (hyp1 _ (lib_extends_trans xt'' (lib_extends_trans xt' ext)) s1 s') as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow;[].
          clear q1.
          lsubst_tac; auto.
          apply tequality_mkc_equality_sp in q0; repnd.
          clear q0 q2.
          apply tequality_product in q1; repnd; auto. }

    + assert (wf_term (mk_equality e1 (mk_pair (mk_var a) (mk_var b)) (mk_product A x B))) as wfe.
      { apply wf_equality; auto. }

      assert (cover_vars
                (mk_equality e1 (mk_pair (mk_var a) (mk_var b)) (mk_product A x B))
                (snoc (snoc s1 (a, a1)) (b, b1))) as cove.
      { apply cover_vars_equality; dands; eauto 3 with slow.
        - repeat (apply cover_vars_snoc_weak); auto.
        - apply cover_vars_pair; dands; eauto 3 with slow;
          apply cover_vars_var;
          repeat (rw @dom_csub_snoc); simpl;
          repeat (rw in_snoc); tcsp.
        - repeat (apply cover_vars_snoc_weak); auto. }

      assert (cover_vars (mk_var a) (snoc s1 (a, a1))) as cva.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

      sim_snoc.
      dands; eauto;[|].

      * assert (wf_term (subst B x (mk_var a))) as wsb.
        { apply wf_term_subst; eauto 3 with slow. }

        assert (cover_vars (subst B x (mk_var a)) (snoc s1 (a,a1))) as csb.
        { apply cover_vars_lsubst_if; simpl.
          - allunfold @cover_vars_upto.
            eapply subvars_trans;[exact c13|]; simpl.
            rw @dom_csub_csub_filter; simpl.
            apply subvars_cons_lr.
            apply subvars_remove_nvars.
            rw @dom_csub_snoc; simpl.
            apply subvars_app_weak_l.
            apply subvars_snoc_weak; auto.
          - introv i; repndors; tcsp; ginv; auto. }

        sim_snoc; dands; auto.

        { sim_snoc; dands; auto. }

        { repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr; auto. }

      * lsubst_tac.
        rw <- @member_equality_iff.
        eapply equality_respects_cequivc_left;
          [apply ccequivc_ext_sym; apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto|].
        apply member_product2.

        dands; auto.

        { apply tequality_product; dands; eauto 3 with slow;[].
          introv xt'' i.
          apply h2 in i; eauto 3 with slow.

          repeat (substc_lsubstc_vars3;[]).
          repeat (lsubstc_snoc2;[]).
          proof_irr; eauto 3 with slow. }

        { apply in_ext_implies_all_in_ex_bar; introv xt''.
          eexists; eexists; dands; eauto 2 with slow;[|].
          - apply equality_refl in h5; auto; eauto 3 with slow.
          - repeat (substc_lsubstc_vars3;[]).
            repeat (lsubstc_snoc2;[]).
            proof_irr; auto.
            apply equality_refl in h0; eauto 3 with slow. }

    + exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in q0; repnd.

      apply all_in_ex_bar_tequality_implies_tequality.
      eapply all_in_ex_bar_modus_ponens2;[|exact q0|exact q3]; clear q0 q3; introv xt'' q0 q3; exrepnd; spcast.
      allrw @fold_equorsq.

      assert (cover_vars (mk_pair (mk_var a) (mk_var b))
                         (snoc (snoc (snoc s1 (a, a1)) (b, b1)) (y, mkc_axiom))) as cov1.
      { apply cover_vars_pair; dands;
        apply cover_vars_var; repeat (rw @dom_csub_snoc);
        simpl; repeat (rw in_snoc); tcsp. }

      assert (cover_vars (mk_pair (mk_var a) (mk_var b))
                         (snoc (snoc (snoc s2 (a, a2)) (b, b2)) (y, mkc_axiom))) as cov2.
      { apply cover_vars_pair; dands;
        apply cover_vars_var; repeat (rw @dom_csub_snoc);
        simpl; repeat (rw in_snoc); tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      proof_irr; auto; GC.

      eapply tequality_monotone in q2;[|exact xt''].
      eapply tequality_respects_cequivc_left;
        [|eapply tequality_respects_cequivc_right;[|exact q2] ].

      * apply ccequivc_ext_lsubst;[].
        constructor; eauto 2 with slow;[].
        apply ccequivc_ext_sym; eauto 3 with slow.

      * apply ccequivc_ext_lsubst;[].
        constructor; eauto 2 with slow;[].
        apply ccequivc_ext_sym; eauto 3 with slow.

  - clear dependent s1.
    clear dependent s2.
    introv hf sim.

    lsubst_tac.

    vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; exrepnd; proof_irr.
    lsubst_tac.
    rw <- @member_equality_iff in h1.
    apply equality_commutes4 in h0;auto;[].
    clear h1.
    apply equality_in_product in h0; repnd.

    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;try exact h0; clear h0; introv xt' h0; exrepnd; spcast; proof_irr.

    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym; apply implies_ccequivc_ext_mkc_spread1;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
      |].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym; apply implies_ccequivc_ext_mkc_spread1;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
      |].
    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym; apply ccequivc_ext_mkc_spread_mkc_pair
      |].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym; apply ccequivc_ext_mkc_spread_mkc_pair
      |].

    vr_seq_true in hyp2.
    pose proof (hyp2
                  _
                  (lib_extends_trans xt' ext)
                  (snoc (snoc (snoc s1 (a,a1)) (b,b1)) (y,mkc_axiom))
                  (snoc (snoc (snoc s2 (a,a2)) (b,b2)) (y,mkc_axiom))) as q.
    clear hyp2.
    repeat (autodimp q hyp).

    + apply hyps_functionality_ext_snoc2; simpl; auto.

      * introv xt'' equ sim'.
        lsubst_tac.

        apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.
        apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.

        revert c16 c20 c21 c18 c19.
        repeat (rw (@hvar_mk_hyp o)); introv.
        lsubst_tac; clear_irr.
        apply equality_refl in equ.
        rw <- @member_equality_iff in equ.

        lsubstc_snoc_vs.

        apply tequality_mkc_equality_sp; dands.

        { pose proof (hyp1 _ (lib_extends_trans xt'' (lib_extends_trans xt' ext)) s1a s2a0) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow.
          lsubst_tac; auto.
          apply tequality_mkc_equality_sp in q0; repnd; auto. }

        { apply in_ext_implies_all_in_ex_bar; introv xt'''.
          left.
          pose proof (hyp1 _ (lib_extends_trans xt''' (lib_extends_trans xt'' (lib_extends_trans xt' ext))) s1a s2a0) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 4 with slow;[].
          lsubst_tac; auto.
          rw <- @member_equality_iff in q1; auto.
          apply equality_commutes3 in q0; auto. }

        { apply in_ext_implies_all_in_ex_bar; introv xt'''.
          left.
          apply equality_in_product; dands; eauto 4 with slow;[].

          apply in_ext_implies_all_in_ex_bar; introv xt''''.
          eexists; eexists; eexists; eexists; dands; eauto 2 with slow;[|];
              try (complete (allsimpl; auto)); eauto 3 with slow;[].
          simpl in sim'1.
          lsubstc_subst_aeq2.
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr; eauto 3 with slow. }

      * apply hyps_functionality_ext_snoc2; simpl; auto.

        { introv xt'' equ sim'.
          lsubst_tac.

          apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx; GC; ginv; proof_irr; GC.

          revert c'.
          repeat (rw (@hvar_mk_hyp o)); introv.

          assert (cover_vars (mk_var a) (snoc s1a (a, t0))) as cov1.
          { apply cover_vars_var.
            rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          assert (cover_vars (mk_var a) (snoc s2a (a, t3))) as cov2.
          { apply cover_vars_var.
            rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr.

          pose proof (hyp1 _ (lib_extends_trans xt'' (lib_extends_trans xt' ext)) s1a s2a) as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow.
          lsubst_tac; auto.
          clear q1.
          apply tequality_mkc_equality_sp in q0; repnd.
          clear q0 q2.
          apply tequality_product in q1; repnd.
          clear q0.
          pose proof (q1 _ (lib_extends_refl lib'1) t0 t3) as h; clear q1.
          autodimp h hyp;[].
          repeat (substc_lsubstc_vars3;[]).
          proof_irr; auto. }

        { apply hyps_functionality_ext_snoc2; simpl; eauto 3 with slow;[].

          introv xt'' equ sim'.

          pose proof (hyp1 _ (lib_extends_trans xt'' (lib_extends_trans xt' ext)) s1 s') as q.
          repeat (autodimp q hyp); exrepnd; proof_irr; eauto 3 with slow;[].
          clear q1.
          lsubst_tac; auto.
          apply tequality_mkc_equality_sp in q0; repnd.
          clear q0 q2.
          apply tequality_product in q1; repnd; auto. }

    + assert (wf_term (mk_equality e1 (mk_pair (mk_var a) (mk_var b)) (mk_product A x B))) as wfe.
      { apply wf_equality; auto. }

      assert (cover_vars
                (mk_equality e1 (mk_pair (mk_var a) (mk_var b)) (mk_product A x B))
                (snoc (snoc s1 (a, a1)) (b, b1))) as cove.
      { apply cover_vars_equality; dands; eauto 3 with slow.
        - repeat (apply cover_vars_snoc_weak); auto.
        - apply cover_vars_pair; dands; eauto 3 with slow;
          apply cover_vars_var;
          repeat (rw @dom_csub_snoc); simpl;
          repeat (rw in_snoc); tcsp.
        - repeat (apply cover_vars_snoc_weak); auto. }

      assert (cover_vars (mk_var a) (snoc s1 (a, a1))) as cva.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

      sim_snoc.
      dands; eauto;[|].

      * assert (wf_term (subst B x (mk_var a))) as wsb.
        { apply wf_term_subst; eauto 3 with slow. }

        assert (cover_vars (subst B x (mk_var a)) (snoc s1 (a,a1))) as csb.
        { apply cover_vars_lsubst_if; simpl.
          - allunfold @cover_vars_upto.
            eapply subvars_trans;[exact c6|]; simpl.
            rw @dom_csub_csub_filter; simpl.
            apply subvars_cons_lr.
            apply subvars_remove_nvars.
            rw @dom_csub_snoc; simpl.
            apply subvars_app_weak_l.
            apply subvars_snoc_weak; auto.
          - introv i; repndors; tcsp; ginv; auto. }

        sim_snoc; dands; auto.

        { sim_snoc; dands; eauto 3 with slow. }

        { repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          proof_irr; auto. }

      * lsubst_tac.
        rw <- @member_equality_iff.
        eapply equality_respects_cequivc_left;
          [apply ccequivc_ext_sym; apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto|].
        apply member_product2.

        dands; auto.

        { apply tequality_product; dands; eauto 3 with slow;[].
          introv xt'' i.
          apply h2 in i; eauto 3 with slow.

          repeat (substc_lsubstc_vars3;[]).
          repeat (lsubstc_snoc2;[]).
          proof_irr; auto. }

        { apply in_ext_implies_all_in_ex_bar; introv xt''.
          eexists; eexists; dands; eauto 3 with slow;[|].
          - apply equality_refl in h5; eauto 3 with slow.
          - repeat (substc_lsubstc_vars3;[]).
            repeat (lsubstc_snoc2;[]).
            proof_irr; auto.
            apply equality_refl in h0; eauto 3 with slow. }

    + exrepnd.
      lsubst_tac.
      rw <- @member_equality_iff in q1.
      apply equality_commutes4 in q0; auto;[].
      clear q1.

      assert (cover_vars (mk_pair (mk_var a) (mk_var b))
                         (snoc (snoc (snoc s1 (a, a1)) (b, b1)) (y, mkc_axiom))) as cov1.
      { apply cover_vars_pair; dands;
        apply cover_vars_var; repeat (rw @dom_csub_snoc);
        simpl; repeat (rw in_snoc); tcsp. }

      assert (cover_vars (mk_pair (mk_var a) (mk_var b))
                         (snoc (snoc (snoc s2 (a, a2)) (b, b2)) (y, mkc_axiom))) as cov2.
      { apply cover_vars_pair; dands;
        apply cover_vars_var; repeat (rw @dom_csub_snoc);
        simpl; repeat (rw in_snoc); tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      proof_irr; auto; GC.

      eapply equality_respects_alphaeqc_left;
        [|eapply equality_respects_alphaeqc_right;
           [|eapply cequivc_preserving_equality;
              [exact q0|]
           ]
        ].

      * unfold alphaeqc; simpl.
        rw @csubst_app.
        eapply alpha_eq_trans;[apply combine_sub_nest|].
        simpl.
        allrw @csub2sub_snoc.

        rw (@cl_lsubst_var_snoc_not_in o a y); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_not_in o a b); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_not_in o b y); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_in o a); eauto 2 with slow;
        [|rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; tcsp].
        rw (@cl_lsubst_var_snoc_in o b); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)
         |rw @dom_sub_snoc; rw in_snoc;
          rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; tcsp].

        apply alpha_eq_lsubst_if_ext_eq; auto;[].
        introv i; simpl.
        rw <- @csub2sub_app; simpl.
        rw @sub_find_app; simpl.
        repeat (rw @sub_find_snoc).
        rw <- @sub_filter_csub2sub.
        rw @sub_find_sub_filter_eq.
        rw memvar_cons; rw memvar_singleton.

        boolvar; simpl; tcsp.

        { autodimp nat1 hyp; tcsp;[].
          simpl; tcsp. }

        { autodimp nbt1 hyp; tcsp;[].
          simpl; tcsp. }

        { autodimp nyt1 hyp; tcsp;[].
          simpl; tcsp. }

        { apply sst1 in i.
          allsimpl; repndors; tcsp.
          assert (LIn v (dom_csub s1)) as vs1 by (allapply @similarity_dom; repnd; allrw; auto).
          apply in_dom_csub_exists in vs1; exrepnd.
          rw vs1; simpl; auto. }

      * unfold alphaeqc; simpl.
        rw @csubst_app.
        eapply alpha_eq_trans;[apply combine_sub_nest|].
        simpl.
        allrw @csub2sub_snoc.

        rw (@cl_lsubst_var_snoc_not_in o a y); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_not_in o a b); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_not_in o b y); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)].
        rw (@cl_lsubst_var_snoc_in o a); eauto 2 with slow;
        [|rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; tcsp].
        rw (@cl_lsubst_var_snoc_in o b); eauto 2 with slow;
        [|repeat (apply cl_sub_snoc; dands; eauto 2 with slow)
         |rw @dom_sub_snoc; rw in_snoc;
          rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; tcsp].

        apply alpha_eq_lsubst_if_ext_eq; auto;[].
        introv i; simpl.
        rw <- @csub2sub_app; simpl.
        rw @sub_find_app; simpl.
        repeat (rw @sub_find_snoc).
        rw <- @sub_filter_csub2sub.
        rw @sub_find_sub_filter_eq.
        rw memvar_cons; rw memvar_singleton.

        boolvar; simpl; tcsp.

        { autodimp nat2 hyp; tcsp;[].
          simpl; tcsp. }

        { autodimp nbt2 hyp; tcsp;[].
          simpl; tcsp. }

        { autodimp nyt2 hyp; tcsp;[].
          simpl; tcsp. }

        { apply sst2 in i.
          allsimpl; repndors; tcsp.
          assert (LIn v (dom_csub s2)) as vs2 by (allapply @similarity_dom; repnd; allrw; auto).
          apply in_dom_csub_exists in vs2; exrepnd.
          rw vs1; simpl; auto. }

      * apply ccequivc_ext_lsubst;[].
        constructor; eauto 2 with slow;[].
        apply ccequivc_ext_sym; eauto 2 with slow.
Qed.


(* begin hide *)



(* end hide *)


(* [27] ============ SPREAD REDUCE ============ *)

(**

<<
   H |- let x,y = <s,t> in u = t2 in T

     By spreadReduce ()

     H |- u[x\s,y\t] = t2 in T
>>
 *)

Definition rule_spread_reduce {o}
           (T s t u t2 : NTerm)
           (x y : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality (mk_spread (mk_pair s t) x y u) t2 T)))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality (lsubst u [(x,s),(y,t)]) t2 T))
    ]
    [].

Lemma rule_spread_reduce_true {o} :
  forall lib (T s t u t2 : NTerm)
         (x y : NVar)
         (H   : @barehypotheses o),
    rule_true lib (rule_spread_reduce T s t u t2 x y H).
Proof.
  intros.
  unfold rule_spread_reduce, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (subset (free_vars u) (x :: y :: vars_hyps H)
          # subset (free_vars s) (vars_hyps H)
          # subset (free_vars t) (vars_hyps H)) as vhyps.
  { clear hyp1.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (intros xx i; simpl;
                     destruct (deq_nvar x xx) as [d|d]; tcsp;[];
                     destruct (deq_nvar y xx) as [q|q]; tcsp;[];
                     assert (LIn xx (remove_nvars [x,y] (free_vars u)))
                       as k by (rw in_remove_nvars; simpl; tcsp);
                     discover; tcsp)). }

  destruct vhyps as [ssu vhyps].
  destruct vhyps as [sss sst].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.

  pose proof (hyp1 _ ext s1 s2 eqh sim) as hyp1; exrepnd.

  lsubst_tac.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality2_sp in hyp0; repnd.
  rw @tequality_mkc_equality2_sp.
  repeat (rw prod_assoc).
  allunfold @equorsq2; repnd.

  assert (ccequivc_ext
            lib'
            (mkc_spread (mkc_pair (lsubstc s w5 s1 c10) (lsubstc t w6 s1 c11)) x y
                        (lsubstc_vars u w4 (csub_filter s1 [x, y]) [x, y] c7))
            (lsubstc (lsubst u [(x,s),(y,t)]) w1 s1 c1))
    as ceq1.
  { introv xt; spcast.
    eapply cequivc_trans;[apply cequivc_mkc_spread_mkc_pair|].
    destruct_cterms; unfold cequivc; simpl.
    rw @csubst_app.
    eapply cequiv_rw_r_eauto;[apply alpha_eq_sym;apply combine_sub_nest|].
    simpl.
    apply alpha_implies_cequiv.

    { apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
      rw @dom_csub_eq; simpl.
      rw @dom_csub_app; simpl.
      rw @dom_csub_csub_filter.
      allapply @similarity_dom; repnd; allrw.
      autorewrite with core slow.
      eapply subset_trans;[exact ssu|].
      apply cons_subset; rw in_app_iff; simpl; dands; tcsp.
      apply cons_subset; rw in_app_iff; simpl; dands; tcsp.
      intros xx i; rw in_app_iff; rw in_remove_nvars; simpl.
      destruct (deq_nvar xx x) as [d|d]; subst; simpl; tcsp;[].
      destruct (deq_nvar xx y) as [q|q]; subst; simpl; tcsp;[].
      left; tcsp. }

    { apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
      { repeat (apply prog_sub_cons; dands); eauto 2 with slow;
        apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow;
        rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; auto. }
      simpl.
      rw @dom_csub_eq; simpl.
      allapply @similarity_dom; repnd; allrw.
      autorewrite with core slow; auto. }

    apply alpha_eq_lsubst_if_ext_eq; auto;[].
    introv i; simpl.
    rw <- @csub2sub_app; simpl.
    rw @sub_find_app; simpl.
    rw <- @sub_filter_csub2sub.
    rw @sub_find_sub_filter_eq.
    rw memvar_cons; rw memvar_singleton.

    boolvar; simpl; tcsp.

    apply ssu in i.
    allsimpl; repndors; tcsp;[].
    assert (LIn v (dom_csub s1)) as vs1 by (allapply @similarity_dom; repnd; allrw; auto).
    apply in_dom_csub_exists in vs1; exrepnd.
    rw vs1; simpl; auto.
  }

  assert (ccequivc_ext
            lib'
            (mkc_spread (mkc_pair (lsubstc s w5 s2 c12) (lsubstc t w6 s2 c13)) x y
                        (lsubstc_vars u w4 (csub_filter s2 [x, y]) [x, y] c9))
            (lsubstc (lsubst u [(x,s),(y,t)]) w1 s2 c0))
    as ceq2.
  { introv xt; spcast.
    eapply cequivc_trans;[apply cequivc_mkc_spread_mkc_pair|].
    destruct_cterms; unfold cequivc; simpl.
    rw @csubst_app.
    eapply cequiv_rw_r_eauto;[apply alpha_eq_sym;apply combine_sub_nest|].
    simpl.
    apply alpha_implies_cequiv.

    { apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
      rw @dom_csub_eq; simpl.
      rw @dom_csub_app; simpl.
      rw @dom_csub_csub_filter.
      allapply @similarity_dom; repnd; allrw.
      autorewrite with core slow.
      eapply subset_trans;[exact ssu|].
      apply cons_subset; rw in_app_iff; simpl; dands; tcsp.
      apply cons_subset; rw in_app_iff; simpl; dands; tcsp.
      intros xx i; rw in_app_iff; rw in_remove_nvars; simpl.
      destruct (deq_nvar xx x) as [d|d]; subst; simpl; tcsp;[].
      destruct (deq_nvar xx y) as [q|q]; subst; simpl; tcsp;[].
      left; tcsp. }

    { apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
      { repeat (apply prog_sub_cons; dands); eauto 2 with slow;
        apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow;
        rw @dom_csub_eq; allapply @similarity_dom; repnd; allrw; auto. }
      simpl.
      rw @dom_csub_eq; simpl.
      allapply @similarity_dom; repnd; allrw.
      autorewrite with core slow; auto. }

    apply alpha_eq_lsubst_if_ext_eq; auto;[].
    introv i; simpl.
    rw <- @csub2sub_app; simpl.
    rw @sub_find_app; simpl.
    rw <- @sub_filter_csub2sub.
    rw @sub_find_sub_filter_eq.
    rw memvar_cons; rw memvar_singleton.

    boolvar; simpl; tcsp.

    apply ssu in i.
    allsimpl; repndors; tcsp;[].
    assert (LIn v (dom_csub s2)) as vs1 by (allapply @similarity_dom; repnd; allrw; auto).
    apply in_dom_csub_exists in vs1; exrepnd.
    rw vs1; simpl; auto.
  }

  dands; try (complete sp).

  - apply in_ext_implies_all_in_ex_bar; introv xt.
    left.
    eapply @equality_respects_cequivc_left;[apply ccequivc_ext_sym;eapply lib_extends_preserves_ccequivc_ext;try exact ceq1;auto|].
    apply @equality_sym.
    eapply @equality_respects_cequivc_left;[apply ccequivc_ext_sym;eapply lib_extends_preserves_ccequivc_ext;try exact ceq2;auto|].
    apply @equality_sym.

    apply all_in_ex_bar_equality_implies_equality.
    unfold equorsq2_bar, equorsq_bar in hyp0; repnd.
    eapply lib_extends_preserves_all_in_ex_bar in hyp3;[|exact xt].
    eapply lib_extends_preserves_all_in_ex_bar in hyp0;[|exact xt].

    eapply all_in_ex_bar_modus_ponens2;[|exact hyp0|exact hyp3]; clear hyp0 hyp3; introv xt' hyp0 hyp3; exrepnd; spcast; proof_irr.

    unfold equorsq in hyp3; repdors; spcast; sp.
    apply @equality_respects_cequivc; sp.
    allapply @equality_refl; sp; eauto 3 with slow.

  - unfold equorsq2_bar, equorsq_bar in *; repnd.
    eapply all_in_ex_bar_modus_ponens2;[|exact hyp0|exact hyp3]; clear hyp0 hyp3; introv xt' hyp0 hyp3; exrepnd; spcast; proof_irr; auto.

  - eapply @equality_respects_cequivc_left;[apply ccequivc_ext_sym;exact ceq1|].
    auto.
Qed.
