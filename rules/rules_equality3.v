(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export per_props_cequiv.
Require Export per_props_product.

Require Export subst_tacs.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export sequents_useful.
Require Export cnterm.

Definition or_base {o} (x : NVar) (A : @NTerm o) : NTerm :=
  mk_image
    (mk_product
       (mk_or mk_int mk_int)
       x
       (mk_ite (mk_var x) A mk_base)
    )
    (mk_lam x (mk_pi2 (mk_var x))).

Lemma isprog_vars_spread_iff {p} :
  forall vs (a : @NTerm p) v1 v2 b,
    isprog_vars vs (mk_spread a v1 v2 b)
    <=> (isprog_vars vs a
         # isprog_vars (v1 :: v2 :: vs) b).
Proof.
  introv; split; intro k; try (repnd; apply isprog_vars_spread); auto.
  allrw @isprog_vars_eq; allsimpl.
  autorewrite with list in *; repnd.
  allrw subvars_eq; allrw subset_app; repnd.
  allrw <- @wf_term_eq.
  apply wf_term_spread_iff in k; exrepnd.
  allunfold @nobnd; ginv.
  allrw <- subvars_eq; allrw subvars_remove_nvars; allrw subvars_eq.
  dands; auto.
  introv i; simpl; apply k0 in i; apply in_app_iff in i; simpl in *; repndors; tcsp.
Qed.

Lemma isprog_vars_pi2 {p} :
  forall vs (a : @NTerm p),
    isprog_vars vs (mk_pi2 a) <=> isprog_vars vs a.
Proof.
  introv.
  unfold mk_pi2.
  rw @isprog_vars_spread_iff.
  split; intro h; repnd; dands; auto.
  apply isprog_vars_var_if; simpl; tcsp.
Qed.

Lemma implies_isprog_vars_pi2 {p} :
  forall vs (a : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs (mk_pi2 a).
Proof.
  intros; apply isprog_vars_pi2; sp.
Qed.

Definition mkc_pi2 {o} (a : @CTerm o) :=
  let (t,x) := a in
  exist isprog (mk_pi2 t) (isprog_pi2 t x).

Definition mkcv_pi2 {p} (vs : list NVar) (a : @CVTerm p vs) :=
  let (t,x) := a in
  exist (isprog_vars vs)
        (mk_pi2 t)
        (implies_isprog_vars_pi2 vs t x).

Definition or_basec {o} (x : NVar) (A : @CTerm o) : CTerm :=
  mkc_image
    (mkc_product
       (mkc_or mkc_int mkc_int)
       x
       (mkcv_ite [x] (mkc_var x) (mk_cv [x] A) (mkcv_base [x]))
    )
    (mkc_lam x (mkcv_pi2 [x] (mkc_var x))).

Lemma substc_mkcv_pi2 {o} :
  forall v (t : @CVTerm o [v]) a,
    substc a v (mkcv_pi2 [v] t) = mkc_pi2 (substc a v t).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfold mk_pi2.

  repeat (unfsubst; simpl).
  allrw @memvar_cons.
  boolvar; simpl in *; auto; fold_terms; GC.
  boolvar; simpl in *; auto; fold_terms; GC.
  tcsp.
Qed.
Hint Rewrite @substc_mkcv_pi2 : slow.

Lemma cequivc_pi2_pair {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_pi2 (mkc_pair a b)) b.
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; auto.
Qed.

Lemma mkcv_base_as_mkc_base {o} :
  forall vs, @mkcv_base o vs = mk_cv vs mkc_base.
Proof.
  tcsp.
Qed.

Hint Rewrite @substc_mkcv_ite : slow.

Lemma equality_in_or_basec_implies {o} :
  forall lib (x : NVar) (A : @CTerm o) a b,
    equality lib a b (or_basec x A)
    -> False.
Proof.
  introv h.

  unfold or_basec in h.
  apply equality_in_mkc_image in h; repnd.

  apply equal_in_image_prop in h; exrepnd; spcast.

  apply member_product2 in h4; exrepnd; GC.
  apply member_product2 in h2; exrepnd; GC.

  apply member_mkc_or in h7; repnd; GC.
  apply member_mkc_or in h9; repnd; GC.

  spcast.

  apply cequivc_sym in h1.
  eapply cequivc_trans in h1;
    [|apply implies_cequivc_apply;
      [apply cequivc_refl|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h6]
    ].
  clear dependent a1.
  eapply cequivc_trans in h1;[|apply cequivc_sym;apply cequivc_beta].

  apply cequivc_sym in h3.
  eapply cequivc_trans in h3;
    [|apply implies_cequivc_apply;
      [apply cequivc_refl|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h8]
    ].
  clear dependent a2.
  eapply cequivc_trans in h3;[|apply cequivc_sym;apply cequivc_beta].

  allrw @mkcv_base_as_mkc_base.
  autorewrite with slow in *.

  eapply cequivc_trans in h1;[|apply cequivc_sym;apply cequivc_pi2_pair].
  eapply cequivc_trans in h3;[|apply cequivc_sym;apply cequivc_pi2_pair].

  repndors; exrepnd; spcast.

  - eapply cequivc_preserving_equality in h4;
      [|eapply mkc_ite_ceq_inl;apply computes_to_valc_implies_cequivc;eauto].
    eapply cequivc_preserving_equality in h2;
      [|eapply mkc_ite_ceq_inl;apply computes_to_valc_implies_cequivc;eauto].

Abort.



(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase_1

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality_base_1 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl_eq_ext a1 b1 A e2),
      mk_baresequent H (mk_concl_eq_ext a2 b2 A e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_1_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_1 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_1, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (teq_and_eq_if_equality2
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  apply eqp; eauto 2 with slow;[]; clear eqp.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands;[| |].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc B wT1 s2 cT0)) as teq.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.

      pose proof (q0 (lsubstc A wT0 s1 cT) y1 y2) as w; destruct w as [w w']; clear w'.
      repeat (autodimp w hyp); dands; eauto 3 with nequality slow;[].
      repnd.
      apply equality_in_uni in w7; auto.
    }

    assert (cover_vars A s2) as covA2.
    { eapply similarity_cover_vars; eauto. }

    assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc A wT0 s2 covA2)) as teqA.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (q0 (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality slow.
    }

    introv.
    split; introv h; repnd; dands;
      try (complete (eapply tequality_preserving_equality;[|exact teq]; auto));
      try (complete (eapply tequality_preserving_equality;[|apply tequality_sym;exact teq]; auto)).

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2 m3.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].
      eapply tequality_preserving_equality in q1;[exact q1|].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].
      eapply tequality_preserving_equality in q1;[exact q1|].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h0;[|apply tequality_sym;eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].

      eapply tequality_preserving_equality in q1;[|apply tequality_sym;exact teqA].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h1;[|apply tequality_sym;eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].

      eapply tequality_preserving_equality in q1;[|apply tequality_sym;exact teqA].

      eauto 3 with nequality.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase_2

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base_2 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl_eq_ext a1 b1 A e2),
      mk_baresequent H (mk_concl_eq_ext a2 b2 mk_base e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_2_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_2 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (teq_and_eq_if_equality2
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  apply eqp; eauto 2 with slow;[]; clear eqp.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands;[| |].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc B wT1 s2 cT0)) as teq.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.

      pose proof (q0 (lsubstc A wT0 s1 cT) y1 y2) as w; destruct w as [w w']; clear w'.
      repeat (autodimp w hyp); dands; eauto 3 with nequality slow;[].
      repnd.
      apply equality_in_uni in w7; auto.
    }

    assert (cover_vars A s2) as covA2.
    { eapply similarity_cover_vars; eauto. }

    assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc A wT0 s2 covA2)) as teqA.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (q0 (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality slow.
    }

    introv.
    split; introv h; repnd; dands;
      try (complete (eapply tequality_preserving_equality;[|exact teq]; auto));
      try (complete (eapply tequality_preserving_equality;[|apply tequality_sym;exact teq]; auto)).

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2 m3.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].
      eapply tequality_preserving_equality in q1;[exact q1|].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].

      apply equality_in_base_iff in q1; spcast.
      eapply equality_respects_cequivc_right;[exact q1|]; auto.
      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h0;[|apply tequality_sym;eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].

      eapply tequality_preserving_equality in q1;[|apply tequality_sym;exact teqA].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h1;[|apply tequality_sym;eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].

      apply equality_in_base_iff in q1; spcast.
      apply equality_in_base_iff in m6; spcast.

      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact m6|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact q1|].
      eauto 3 with nequality.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase_3

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality_base_3 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl_eq_ext a1 b1 mk_base e2),
      mk_baresequent H (mk_concl_eq_ext a2 b2 A e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_3_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_3 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (teq_and_eq_if_equality2
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  apply eqp; eauto 2 with slow;[]; clear eqp.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands;[| |].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc B wT1 s2 cT0)) as teq.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.

      pose proof (q0 (lsubstc A wT0 s1 cT) y1 y2) as w; destruct w as [w w']; clear w'.
      repeat (autodimp w hyp); dands; eauto 3 with nequality slow;[].
      repnd.
      apply equality_in_uni in w7; auto.
    }

    assert (cover_vars A s2) as covA2.
    { eapply similarity_cover_vars; eauto. }

    assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc A wT0 s2 covA2)) as teqA.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (q0 (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT) (lsubstc A wT0 s1 cT)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality slow.
    }

    introv.
    split; introv h; repnd; dands;
      try (complete (eapply tequality_preserving_equality;[|exact teq]; auto));
      try (complete (eapply tequality_preserving_equality;[|apply tequality_sym;exact teq]; auto)).

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].

      apply equality_in_base_iff in q1; spcast.
      eapply equality_respects_cequivc_right;[exact q1|]; auto.
      eauto 3 with nequality.

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].
      eapply tequality_preserving_equality in q1;[exact q1|].

      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h0;[|apply tequality_sym;eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h0|].

      apply equality_in_base_iff in q1; spcast.
      apply equality_in_base_iff in m6; spcast.

      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact m6|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact q1|].
      eauto 3 with nequality.

    + eapply tequality_preserving_equality in h1;[|apply tequality_sym;eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      eapply equality_trans;[exact h1|].

      eapply tequality_preserving_equality in q1;[|apply tequality_sym;exact teqA].

      eauto 3 with nequality.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase_4

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base_4 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl_eq_ext a1 b1 mk_base e2),
      mk_baresequent H (mk_concl_eq_ext a2 b2 mk_base e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_4_tue {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_4 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_4, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (teq_and_eq_if_equality2
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  apply eqp; eauto 2 with slow;[]; clear eqp.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands;[| |].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc B wT1 s2 cT0)) as teq.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.

      pose proof (q0 (lsubstc A wT0 s1 cT) y1 y2) as w; destruct w as [w w']; clear w'.
      repeat (autodimp w hyp); dands; eauto 3 with nequality slow;[].
      repnd.
      apply equality_in_uni in w7; auto.
    }

    introv.
    split; introv h; repnd; dands;
      try (complete (eapply tequality_preserving_equality;[|eauto]; auto));
      try (complete (eapply tequality_preserving_equality;[|apply tequality_sym;eauto]; auto)).

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1) (lsubstc a1 w0 s1 c1)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      apply equality_in_base_iff in q1; spcast.

      eapply equality_respects_cequivc_right;[exact q1|]; auto.

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2) (lsubstc a2 w3 s1 c2)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      apply equality_in_base_iff in q1; spcast.

      eapply equality_respects_cequivc_right;[exact q1|]; auto.

    + eapply tequality_preserving_equality in h0;[|apply tequality_sym;eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5) (lsubstc b1 w4 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      apply equality_in_base_iff in q1; spcast.
      apply equality_in_base_iff in m6; spcast.

      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact m6|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact q1|]; auto.

    + eapply tequality_preserving_equality in h1;[|apply tequality_sym;eauto].
      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in m0; repnd; GC.
      clear m2.
      apply equality_in_mkc_equality in m1; exrepnd.
      clear dependent y1.
      clear dependent y2.

      pose proof (m0 (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5) (lsubstc b2 w5 s1 c5)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp; repnd; dands; eauto 3 with nequality;[].

      apply equality_in_base_iff in q1; spcast.
      apply equality_in_base_iff in m6; spcast.

      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact m6|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;exact q1|]; auto.
Qed.



(*
(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- a1 = b1 in Image(x:(Int+Int) * if x then A else Base, pi2)
     H |- a2 = b2 in Image(x:(Int+Int) * if x then A else Base, pi2)
>>
 *)
Definition rule_equality_equality_base {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl (mk_squash (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1))) e2),
      mk_baresequent H (mk_concl (mk_squash (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2))) e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_or_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_or H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_or, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- squash(a1 = b1 in A \/ a1 ~ b1)
     H |- squash(a2 = b2 in A \/ a2 ~ b2)
>>
 *)
Definition rule_equality_equality_base_or {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_concl_eq (mk_equality a1 a2 A)
                    (mk_equality b1 b2 B)
                    (mk_uni i)))
    [ mk_baresequent H (mk_concl_eq_ext A B (mk_uni i) e1),
      mk_baresequent H (mk_concl (mk_squash (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1))) e2),
      mk_baresequent H (mk_concl (mk_squash (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2))) e3)
    ]
    [sarg_term a1, sarg_term a2, sarg_term A].

Lemma rule_equality_equality_base_or_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_or H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base_or, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term a1)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a2)) as arg2; autodimp arg2 hyp.
  pose proof (cargs (sarg_term A)) as arg3; autodimp arg3 hyp.
  unfold arg_constraints in cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- context[closed_extract ?a ?b] ] =>
    assert (closed_extract a b) as cext
  end.
  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    unfold closed_extract; simpl.
    apply covered_prefl_same.
    unfold covered; simpl; autorewrite with list.
    repeat (apply implies_subvars_app_l); apply subvars_eq; tcsp.
  }
  exists cext.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

(* XXXXXXXXXXXXXXXXXXXX *)
  dands.

  {
    apply tequality_mkc_equality; dands; eauto 2 with slow.
    introv; split; intro h; repnd; dands.
  }

XXXXXXXXXXXXXXXXXX
  pose proof (teq_and_eq_if_equality2
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  apply eqp; eauto 2 with slow;[]; clear eqp.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands;[| |].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; exrepnd.
    apply tequality_mkc_equality_in_universe_true in h0; auto;[].
    eauto 3 with nequality.

  - assert (tequality lib (lsubstc A wT0 s1 cT) (lsubstc B wT1 s2 cT0)) as teq.
    {
      vr_seq_true in hyp1.
      pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
      lsubst_tac.

      apply tequality_mkc_equality in q0; repnd.
      apply equality_in_mkc_equality in q1; exrepnd.

      pose proof (q0 (lsubstc A wT0 s1 cT) y1 y2) as w; destruct w as [w w']; clear w'.
      repeat (autodimp w hyp); dands; eauto 3 with nequality slow;[].
      repnd.
      apply equality_in_uni in w7; auto.
    }

    introv.
    split; introv h; repnd; dands;
      try (complete (eapply tequality_preserving_equality;[|eauto]; auto));
      try (complete (eapply tequality_preserving_equality;[|apply tequality_sym;eauto]; auto)).

    + eapply tequality_preserving_equality;[|eauto].
      vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as m; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in m1; repnd.
      clear m2 m3.
      rw @tequality_mkc_squash in m0; repnd.
      destruct m0 as [m0 m']; clear m'.
      autodimp m0 hyp.

      allrw @inhabited_mkc_or; repnd.

      SearchAbout type mkc_or.
      apply tequality_mkc_or in h0; repnd.
      rw @tequality_mkc_equality_sp in h2; repnd.
      allrw @fold_equorsq.
      apply inhabited_mkc_or in h1; repnd.

      repndors.

      * apply inhabited_mkc_equality in h1.
        eapply cequorsq_equality_trans2 in h1;[|eauto].
        left; auto.

      * rw @inhabited_cequiv in h1.
        destruct h2 as [d|d]; spcast.

        { eapply equality_respects_cequivc_left in d;[|apply cequivc_sym; eauto].
          left; auto. }

        { eapply cequivc_trans in d;[|eauto].
          right; spcast; auto. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in h1; repnd.
      clear h2 h3.
      rw @tequality_mkc_squash in h0.
      apply tequality_mkc_or in h0; repnd.
      rw @tequality_mkc_equality_sp in h2; repnd.
      allrw @fold_equorsq.
      apply inhabited_mkc_or in h1; repnd.

      repndors.

      * apply inhabited_mkc_equality in h1.
        eapply cequorsq_equality_trans2 in h1;[|eauto].
        left; auto.

      * rw @inhabited_cequiv in h1.
        destruct h2 as [d|d]; spcast.

        { eapply equality_respects_cequivc_left in d;[|apply cequivc_sym; eauto].
          left; auto. }

        { eapply cequivc_trans in d;[|eauto].
          right; spcast; auto. }
Qed.
*)