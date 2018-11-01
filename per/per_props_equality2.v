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



(*Require Export per_props_equality_more.*)
Require Export per_props_uni.
(*Require Export per_props_psquash.*)


Ltac ntsi :=
  match goal with
      [ p : POpid , H : context[nuprli ?lib ?i] |- _ ] =>
      pose proof (@nuprli_type_system p lib i) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprli_value_respecting_left {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> cequivc lib t1 t3
    -> nuprli lib i t3 t2 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli lib i t1 t3 eq) as eq13
      by (apply nts_tyv; auto; apply nts_tyt with (T2 := t2); auto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprli_value_respecting_right {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> cequivc lib t2 t3
    -> nuprli lib i t1 t3 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli lib i t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Ltac ceq_comp_nuprli_hyp :=
  match goal with
  | [ H1 : computes_to_valc _ ?T1 _,
           H2 : computes_to_valc _ ?T2 _,
                H3 : nuprli _ _ ?T1 ?T2 _ |- _ ] =>
    eapply nuprli_value_respecting_right in H3;[|apply computes_to_valc_implies_cequivc; exact H2];
    eapply nuprli_value_respecting_left in H3;[|apply computes_to_valc_implies_cequivc; exact H1]
  | [ H1 : computes_to_valc _ ?T _,
           H2 : nuprli _ _ ?T ?T _ |- _ ] =>
    eapply nuprli_value_respecting_right in H2;[|apply computes_to_valc_implies_cequivc; exact H1];
    eapply nuprli_value_respecting_left in H2;[|apply computes_to_valc_implies_cequivc; exact H1]
  end.

Ltac ceq_comp_nuprli_concl :=
  match goal with
  | [ H1 : computes_to_valc _ ?T1 _,
           H2 : computes_to_valc _ ?T2 _
      |- nuprli _ _ ?T1 ?T2 _ ] =>
    eapply nuprli_value_respecting_right;[|apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact H2];
    eapply nuprli_value_respecting_left;[|apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact H1]
  | [ H1 : computes_to_valc _ ?T _
      |- nuprli _ _ ?T ?T _ ] =>
    eapply nuprli_value_respecting_right;[|apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact H1];
    eapply nuprli_value_respecting_left;[|apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact H1]
  end.

Hint Resolve iscvalue_mkc_approx : slow.
Hint Resolve iscvalue_mkc_cequiv : slow.
Hint Resolve iscvalue_mkc_equality : slow.
Hint Resolve iscvalue_mkc_tequality : slow.
Hint Resolve iscvalue_mkc_pertype : slow.
Hint Resolve iscvalue_mkc_ipertype : slow.
Hint Resolve iscvalue_mkc_spertype : slow.
Hint Resolve iscvalue_mkc_texc : slow.
Hint Resolve iscvalue_mkc_union : slow.
Hint Resolve iscvalue_mkc_image : slow.
Hint Resolve iscvalue_mkc_partial : slow.
Hint Resolve iscvalue_mkc_admiss : slow.
Hint Resolve iscvalue_mkc_mono : slow.
Hint Resolve iscvalue_mkc_free_from_atom : slow.
Hint Resolve iscvalue_mkc_efree_from_atom : slow.
Hint Resolve iscvalue_mkc_free_from_atoms : slow.

Lemma eq_nuprl_in_nuprli_implies {o} :
  forall lib (T1 T2 : @CTerm o) (per per1 per2 : per(o)) i,
    nuprl lib T1 T2 per
    -> nuprli lib i T1 T1 per1
    -> nuprli lib i T2 T2 per2
    -> nuprli lib i T1 T2 per1.
Proof.
  unfold nuprl.
  introv cl.
  revert per1 per2.
  remember (univ lib) as u.
  revert Hequ.
  close_cases (induction cl using @close_ind') Case; subst; introv equ;
    try (introv cloa clob); eauto;
      try (complete (allunfold_per; exrepnd; spcast;
                     repeat ceq_comp_nuprli_hyp;
                     ceq_comp_nuprli_concl; auto)).

  - Case "CL_init".
    subst.
    duniv j h.
    allrw @univi_exists_iff; exrepnd; spcast.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

  - Case "CL_approx".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.
    apply CL_approx.
    exists a b c d; dands; spcast; eauto 3 with slow.
    inversion cloa; try not_univ.

  - Case "CL_cequiv".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.
    apply CL_cequiv.
    exists a b c d; dands; spcast; eauto 3 with slow.
    inversion cloa; try not_univ.

  - Case "CL_eq".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_eq.
    exists A1 A0 a4 a5 a0 a3 eqa.
    dands; spcast; eauto 3 with slow;[].

    introv; rw t1; rw c0; tcsp.

  - Case "CL_req".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_req.
    exists A1 A0 a4 a5 a0 a3 eqa.
    dands; spcast; eauto 3 with slow.

    eapply eq_term_equals_trans;[eauto|].
    apply close_type_sys_per_req.eq_term_equals_preserves_per_req_eq; auto.

  - Case "CL_teq".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c11.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl3; exact cl3].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl1 hyp);[].
    pose proof (IHcl1 eqa2 eqa1) as IHcl1.
    repeat (autodimp IHcl1 hyp);[].

    repeat (autodimp IHcl2 hyp);[].
    pose proof (IHcl2 eqa2 eqa1) as IHcl2.
    repeat (autodimp IHcl2 hyp);[].

    repeat (autodimp IHcl3 hyp);[].
    pose proof (IHcl3 eqa2 eqa2) as IHcl3.
    repeat (autodimp IHcl3 hyp);[].

    dup IHcl1 as np1.
    eapply nuprli_ext in np1;[|eauto].

    dup IHcl2 as np2.
    eapply nuprli_ext in np2;[|eauto].

    dup IHcl3 as np3.
    eapply nuprli_ext in np3;[|eauto].

    apply CL_teq.
    exists a4 a5 a0 a3 eqa.
    dands; spcast; eauto 3 with slow.

  - Case "CL_isect".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_isect.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_func".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_func.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_disect".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_disect.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_pertype".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    apply CL_pertype.
    exists R4 R0 eq6 eq3.
    dands; spcast; eauto 3 with slow.

    { introv.
      pose proof (rec2 x y) as rec2; repeat (autodimp rec2 hyp);[].
      pose proof (rec2 (eq4 x y) (eq4 x y)) as rec2; repeat (autodimp rec2 hyp);
        try apply c5.
      pose proof (c4 x y) as c4.
      applydup @nuprli_implies_nuprl in rec2.
      eapply nuprl_uniquely_valued in rec0;[|exact c4].
      apply eq_term_equals_sym in rec0.
      eapply nuprli_ext;eauto. }

    { introv.
      rw <- t.
      apply iff_inhabited_if_eq_term_equals.
      pose proof (c3 x y) as c3.
      pose proof (c9 x y) as c9.
      applydup @nuprli_implies_nuprl in c9.
      eapply nuprl_uniquely_valued in c0;[|exact c3].
      apply eq_term_equals_sym in c0; auto. }

  - Case "CL_ipertype".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    apply CL_ipertype.
    exists R4 R0 eq1.
    dands; spcast; eauto 3 with slow.

    { introv.
      pose proof (rec1 x y) as rec1; repeat (autodimp rec1 hyp);[].
      pose proof (rec1 (eq3 x y) (eq2 x y)) as rec1; repeat (autodimp rec1 hyp);
        try apply c7; try apply c4;[].
      pose proof (cl1 x y) as cl1.
      applydup @nuprli_implies_nuprl in rec1.
      apply nuprl_refl in rec0.
      eapply nuprl_uniquely_valued in rec0;[|apply nuprl_refl in cl1; exact cl1].
      apply eq_term_equals_sym in rec0.
      eapply nuprli_ext;eauto. }

    { introv.
      rw e1.
      apply iff_inhabited_if_eq_term_equals.
      pose proof (cl1 t1 t2) as cl1.
      pose proof (c7 t1 t2) as c7.
      applydup @nuprli_implies_nuprl in c7.
      eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl1; exact cl1].
      apply eq_term_equals_sym in c0; auto. }

  - Case "CL_spertype".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    apply CL_spertype.
    exists R4 R0 eq3.
    dands; spcast; eauto 3 with slow;[].

    introv.
    pose proof (rec1 x y) as rec1; repeat (autodimp rec1 hyp);[].
    pose proof (rec1 (eq3 x y) (eq2 x y)) as rec1; repeat (autodimp rec1 hyp);
      try apply c11; try apply c6.

  - Case "CL_w".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_w.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e2) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_m".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_m.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e2) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_pw".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c11.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c6.
    eapply nuprl_uniquely_valued in c9;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c9.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqp2 eqp1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_pw.
    exists eqp2 eqa2 eqb2.
    exists p0 p1 cp0 cp1 ca0 ca1 cb0 cb1; exists C0 C1.
    dands; auto;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    exists P0 P1 ap0 ap1 A0 A1 bp0 bp1; exists ba0 ba1 B0 B1.
    dands; spcast; eauto 3 with slow;[| | |].

    { introv.
      assert (eqp1 p2 p3) as e' by (apply c9; apply c0; auto).
      apply reca with (per2 := eqa1 _ _ e'); auto.

      { apply c0; auto. }

      { pose proof (c12 _ _ ep) as impa.
        apply nuprli_refl in impa; auto. }

      { pose proof (c7 _ _ e') as impa.
        apply nuprli_sym in impa.
        apply nuprli_refl in impa; auto. } }

    { introv.
      assert (eqp1 p2 p3) as ep1 by (apply c9; apply c0; auto).
      assert (eqp p2 p3) as ep2 by (apply c9; auto).
      assert (eqa1 p2 p3 ep1 a1 a2) as ea'.
      { pose proof (c12 _ _ ep) as w1.
        pose proof (c7 _ _ ep1) as w2.
        pose proof (cla _ _ ep2) as w3.
        apply @nuprli_implies_nuprl in w1.
        apply @nuprli_implies_nuprl in w2.
        apply nuprl_refl in w1.
        eapply nuprl_uniquely_valued in w1;[|apply nuprl_refl in w3; exact w3].
        apply nuprl_refl in w2.

        admit. }

      apply recb with (ep := ep2) (per2 := eqb1 p2 p3 ep1 a1 a2 ea'); auto.

      { admit. }

      { pose proof (c13 _ _ _ _ _ ea) as impa.
        apply nuprli_refl in impa; auto. }

      { pose proof (c8 _ _ _ _ _ ea') as impa.
        apply nuprli_sym in impa.
        apply nuprli_refl in impa; auto. } }

    { introv eb.

      admit. }

    { apply c0; auto. }

  - Case "CL_pm".
    admit.

  - Case "CL_texc".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl1; exact cl1].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c10.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_refl in cl2; exact cl2].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl1 hyp);[].
    pose proof (IHcl1 eqn2 eqn1) as IHcl1.
    repeat (autodimp IHcl1 hyp);[].

    repeat (autodimp IHcl2 hyp);[].
    pose proof (IHcl2 eqe2 eqe1) as IHcl2.
    repeat (autodimp IHcl2 hyp);[].

    dup IHcl1 as np1.
    eapply nuprli_ext in np1;[|eauto].

    dup IHcl2 as np2.
    eapply nuprli_ext in np2;[|eauto].

    apply CL_texc.
    exists eqn eqe N0 N1 E0 E1.
    dands; spcast; eauto 3 with slow.
    introv; rw e1.
    apply close_type_sys_per_texc.eq_term_equals_per_texc_eq_if; auto.

  - Case "CL_union".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl1; exact cl1].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c10.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_refl in cl2; exact cl2].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl1 hyp);[].
    pose proof (IHcl1 eqa2 eqa1) as IHcl1.
    repeat (autodimp IHcl1 hyp);[].

    repeat (autodimp IHcl2 hyp);[].
    pose proof (IHcl2 eqb2 eqb1) as IHcl2.
    repeat (autodimp IHcl2 hyp);[].

    dup IHcl1 as np1.
    eapply nuprli_ext in np1;[|eauto].

    dup IHcl2 as np2.
    eapply nuprli_ext in np2;[|eauto].

    apply CL_union.
    exists eqa2 eqb2 A0 A1 B0 B1.
    dands; spcast; eauto 3 with slow.

  - Case "CL_image".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c8.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_image.
    exists eqa2 A0 A1 f0 f1.
    dands; spcast; eauto 3 with slow.

  - Case "CL_partial".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_partial.
    exists A4 A0 eqa2.
    dands; spcast; eauto 3 with slow.

  - Case "CL_admiss".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_admiss.
    exists A4 A0 eqa2.
    dands; spcast; eauto 3 with slow.

  - Case "CL_mono".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_mono.
    exists A4 A0 eqa2.
    dands; spcast; eauto 3 with slow.

  - Case "CL_ffatom".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.
    repeat computes_to_eqval.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_ffatom.
    exists A4 A0 x4 x0 a4 a0 eqa2 u.
    dands; spcast; eauto 3 with slow.
    apply c0; auto.

  - Case "CL_effatom".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.
    repeat computes_to_eqval.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in c3; exact c3].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_effatom.
    exists A4 A0 x4 x0 a4 a0 eqa2.
    dands; spcast; eauto 3 with slow.
    eapply close_type_sys_per_effatom.name_not_in_upto_iff_respects_per;[eauto|].
    apply eq_term_equals_sym in c0; auto.

  - Case "CL_ffatoms".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.
    repeat computes_to_eqval.

    applydup @nuprli_implies_nuprl in c7.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in c3; exact c3].
    apply eq_term_equals_sym in c0.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np1.
    eapply nuprli_ext in np1;[|eauto].

    apply CL_ffatoms.
    exists A4 A0 x4 x0 eqa2.
    dands; spcast; eauto 3 with slow.
    apply c0; auto.

  - Case "CL_set".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_set.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_tunion".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_tunion.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e2) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }

  - Case "CL_product".
    subst.
    allunfold_per; exrepnd; spcast.
    repeat computes_to_eqval.
    repeat ceq_comp_nuprli_hyp.
    ceq_comp_nuprli_concl; auto.

    inversion cloa; try not_univ;[].
    inversion clob; try not_univ;[].
    clear cloa clob.
    allunfold_per; exrepnd; spcast.
    computes_to_value_isvalue; GC.

    applydup @nuprli_implies_nuprl in c9.
    eapply nuprl_uniquely_valued in c0;[|apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c0.

    applydup @nuprli_implies_nuprl in c5.
    eapply nuprl_uniquely_valued in c7;[|apply nuprl_sym in cl; apply nuprl_refl in cl; exact cl].
    apply eq_term_equals_sym in c7.

    repeat (autodimp IHcl hyp);[].
    pose proof (IHcl eqa2 eqa1) as IHcl.
    repeat (autodimp IHcl hyp);[].

    dup IHcl as np.
    eapply nuprli_ext in np;[|eauto].

    apply CL_product.
    exists eqa2 eqb2.
    dands; auto;[].

    exists A1 A0 v1 v0 B1 B0.
    dands; spcast; eauto 3 with slow;[].

    allfold (@nuprli o lib i).
    allfold (@nuprl o lib).

    introv.
    assert (eqa1 a a') as e' by (apply c7; apply c0; auto).
    apply recb with (per2 := eqb1 a a' e'); auto.

    { apply c0; auto. }

    { pose proof (c10 _ _ e2) as impa.
      apply nuprli_refl in impa; auto. }

    { pose proof (c6 _ _ e') as impa.
      apply nuprli_sym in impa.
      apply nuprli_refl in impa; auto. }
Admitted.

Lemma implies_equality_in_uni {o} :
  forall lib (T1 T2 : @CTerm o) i,
    tequality lib T1 T2
    -> member lib T1 (mkc_uni i)
    -> member lib T2 (mkc_uni i)
    -> equality lib T1 T2 (mkc_uni i).
Proof.
  introv teq mema memb.
  unfold member in *.
  unfold tequality in *.
  unfold equality, nuprl in *; exrepnd.
  inversion mema1; try not_univ;[].
  duniv j h.
  inversion memb1; try not_univ;[].
  duniv k q.
  allrw @univi_exists_iff; exrepnd.
  computes_to_value_isvalue; GC.
  exists eq; dands; auto.
  apply q0.
  exists eq1.
  allfold (@nuprli o lib j1).
  allfold (@nuprl o lib).
  apply h0 in mema0.
  apply q0 in memb0.
  clear h0 q0.
  exrepnd.
  applydup @nuprli_implies_nuprl in mema2.

  eapply nuprl_uniquely_valued in mema0;[|apply nuprl_refl in teq0; exact teq0].
  apply eq_term_equals_sym in mema0.
  eapply nuprli_ext in mema2;[|eauto].

  eapply eq_nuprl_in_nuprli_implies; eauto.
Qed.
