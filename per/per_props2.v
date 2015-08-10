(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export per_props.
Require Export subst_per.
Require Export sequents_tacs.
Require Import cequiv_tacs.
Require Import subst_tacs.


(*
Lemma tequality_mkc_erase :
  forall a b,
    tequality (mkc_erase a) (mkc_erase b)
    <=> tequality a b.
Proof.
  introv.
  repeat (rw mkc_erase_eq).
  rw tequality_mkc_ufun; split; sp.
  apply type_mkc_unit.
Qed.
*)

Lemma apply2_erasec_rel {o} :
  forall lib (A x y : @CTerm o),
    cequivc lib (mkc_apply2 (erasec_rel A) x y) A.
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  unfold erase_rel.
  remember (newvars2 [x1]); sp.
  betared.
  apply newvars2_prop2 in Heqp; repnd.
  rw @subst_mk_lam; auto.
  repeat (rw subst_trivial; eauto with isprog).
  betared.
  repeat (rw @subst_trivial; eauto with isprog).
  apply cequiv_refl.
  apply isprog_implies; auto.
Qed.

Lemma forall_apply_erase_rel {o} :
  forall lib (A : @CTerm o),
    (forall x y : CTerm, type lib (mkc_apply2 (erasec_rel A) x y))
    <=> type lib A.
Proof.
  introv; split; intro k; introv.

  generalize (k mkc_axiom mkc_axiom); clear k; intro k.
  generalize (apply2_erasec_rel lib A mkc_axiom mkc_axiom); intro j.
  apply type_respects_cequivc_left in j; auto.
  apply tequality_refl in j; rw @fold_type in j; auto.

  generalize (apply2_erasec_rel lib A x y); intro j.
  apply cequivc_sym in j.
  apply type_respects_cequivc_left in j; auto.
  apply tequality_refl in j; auto.
Qed.

Lemma is_per_type_erasec_rel {o} :
  forall lib (A : @CTerm o), is_per_type lib (erasec_rel A).
Proof.
  introv.
  unfold is_per_type; dands.

  unfold sym_type; introv inh.
  generalize (apply2_erasec_rel lib A x y); intro j1.
  generalize (apply2_erasec_rel lib A y x); intro j2.
  apply inhabited_type_cequivc in j1; auto.
  apply inhabited_type_cequivc with (a := A);
    auto; try (apply cequivc_sym; auto).

  unfold trans_type.
  introv inh1 inh2.
  generalize (apply2_erasec_rel lib A x y); intro j1.
  generalize (apply2_erasec_rel lib A y z); intro j2.
  generalize (apply2_erasec_rel lib A x z); intro j3.
  apply inhabited_type_cequivc in j1; auto.
  apply inhabited_type_cequivc in j2; auto.
  apply inhabited_type_cequivc with (a := A);
    auto; try (apply cequivc_sym; auto).
Qed.
Hint Immediate is_per_type_erasec_rel.

Lemma is_per_type_erasec_rel_iff {o} :
  forall lib (A : @CTerm o), is_per_type lib (erasec_rel A) <=> True.
Proof.
  introv; split; sp.
Qed.

Lemma inhabited_type_apply2_erasec_rel {o} :
  forall lib (A x y : @CTerm o),
    inhabited_type lib (mkc_apply2 (erasec_rel A) x y)
    <=> inhabited_type lib A.
Proof.
  introv; split; intro k.

  generalize (apply2_erasec_rel lib A x y); intro j.
  apply inhabited_type_cequivc in j; auto.

  generalize (apply2_erasec_rel lib A x y); intro j.
  apply inhabited_type_cequivc with (a := A);
    auto; try (apply cequivc_sym; auto).
Qed.

Lemma inhabited_type_apply2_erasec_rel_iff {o} :
  forall lib (A B : @CTerm o),
    (forall x y : CTerm,
       inhabited_type lib (mkc_apply2 (erasec_rel A) x y)
       <=>
       inhabited_type lib (mkc_apply2 (erasec_rel B) x y))
    <=>
    (inhabited_type lib A <=> inhabited_type lib B).
Proof.
  introv.
  split; intro k.

  generalize (k mkc_axiom mkc_axiom).
  repeat (rw @inhabited_type_apply2_erasec_rel); auto.

  introv.
  repeat (rw @inhabited_type_apply2_erasec_rel); auto.
Qed.

Lemma tequality_erase {o} :
  forall lib (A B : @CTerm o),
    tequality lib (erasec A) (erasec B)
    <=> ((inhabited_type lib A <=> inhabited_type lib B)
         # type lib A
         # type lib B).
Proof.
  introv.
  allrw @erasec_eq.
  rw @tequality_mkc_pertype.
  repeat (rw @forall_apply_erase_rel).
  rw @is_per_type_erasec_rel_iff.
  rw @inhabited_type_apply2_erasec_rel_iff.
  split; sp.
Qed.

Lemma type_erase {o} :
  forall lib (A : @CTerm o), type lib (erasec A) <=> type lib A.
Proof.
  introv.
  rw @tequality_erase; split; sp.
Qed.

Lemma inhabited_type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@inhabited_type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_cequivc lib) in aeq.
  apply @inhabited_type_cequivc with (a := a); auto.
Qed.
Hint Resolve inhabited_type_respects_alphaeqc : respects.

Lemma type_respects_cequivc {o} :
  forall lib, respects1 (cequivc lib) (@type o lib).
Proof.
  introv ceq typ.
  apply type_respects_cequivc_left in ceq; auto.
  apply tequality_refl in ceq; auto.
Qed.
Hint Resolve type_respects_cequivc : respects.

Lemma type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_cequivc lib) in aeq.
  apply type_respects_cequivc_left in aeq; auto.
  apply tequality_refl in aeq; auto.
Qed.
Hint Resolve type_respects_alphaeqc : respects.

Lemma type_apply2_erasec_rel {o} :
  forall lib (A x y : @CTerm o),
    type lib (mkc_apply2 (erasec_rel A) x y)
    <=> type lib A.
Proof.
  introv; split; intro k.

  generalize (apply2_erasec_rel lib A x y); intro j.
  apply type_respects_cequivc_left in j; auto.
  apply tequality_refl in j; auto.

  generalize (apply2_erasec_rel lib A x y); intro j.
  apply cequivc_sym in j.
  apply type_respects_cequivc_left in j; auto.
  apply tequality_refl in j; auto.
Qed.

Lemma equality_in_erasec {o} :
  forall lib (t1 t2 t : @CTerm o),
    equality lib t1 t2 (erasec t) <=> inhabited_type lib t.
Proof.
  introv; split; intro k; allunfold @inhabited_type; exrepnd;
  allrw @erasec_eq; allrw @equality_in_mkc_pertype; repnd;
  allrw @inhabited_type_apply2_erasec_rel; auto.

  dands; auto.
  exists t0; auto.
  introv.
  apply type_apply2_erasec_rel.
  apply inhabited_implies_tequality in k0; auto.
Qed.

Lemma inhabited_type_erasec {o} :
  forall lib (t : @CTerm o), inhabited_type lib (erasec t) <=> inhabited_type lib t.
Proof.
  introv; split; intro k; allunfold @inhabited_type; exrepnd.

  rw @equality_in_erasec in k0; allunfold @inhabited_type; exrepnd.
  exists t1; auto.

  exists (@mkc_axiom o).
  rw @equality_in_erasec.
  exists t0; auto.
Qed.

Lemma member_in_base_iff {o} :
  forall lib (t : @CTerm o), member lib t mkc_base <=> True.
Proof.
  intros; split; intro; auto; apply member_base.
Qed.

Lemma equality_in_isect2 {o} :
  forall lib (t u : @CTerm o) A v B,
    equality lib t u (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (equality lib t u (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

Lemma member_in_isect {o} :
  forall lib (t : @CTerm o) A v B,
    member lib t (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (member lib t (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

Lemma is_per_type_sqper_rel_change_subst {o} :
  forall lib v1 v2 R s1 s2 w c1 c2,
    (forall x y : @CTerm o,
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s1 c1) x y)
       <=>
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s2 c2) x y))
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s1 c1)
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s2 c2).
Proof.
  introv iff isper.
  allunfold @is_per_type.
  destruct isper as [sym trans].
  allunfold @sqper_rel; lsubst_tac.
  dands.

  - clear trans.
    allunfold @sym_type; introv inh.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (sym x y); clear sym; intro sym.
    autodimp sym hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y x); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

  - clear sym.
    allunfold @trans_type; introv inh1 inh2.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (trans x y z); clear trans; intro trans.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
Qed.

Lemma tequality_iff_mkc_tequality {o} :
  forall lib (A B : @CTerm o),
    type lib (mkc_tequality A B) <=> tequality lib A B.
Proof.
  introv.
  split; intro k.

  - unfold type, tequality in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    exists eqa; auto.

  - unfold tequality in k; exrepnd.
    exists (@true_per o).
    apply CL_teq; unfold per_teq.
    fold (@nuprl o).
    exists A B A B eq; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprl_refl in k0; auto.
    apply nuprl_sym in k0; apply nuprl_refl in k0; auto.
Qed.

Lemma tequality_mkc_tequality {o} :
  forall lib (A B C D : @CTerm o),
    tequality lib (mkc_tequality A B) (mkc_tequality C D)
    <=> (tequality lib A C # tequality lib B D # tequality lib A B).
Proof.
  introv.
  split; intro k.

  - unfold tequality in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    dands; exists eqa; auto.

  - unfold tequality in k; exrepnd.
    exists (@true_per o).
    apply CL_teq; unfold per_teq.
    fold (@nuprl o).

    assert (eq1 <=2=> eq)
      as eqs1
        by (apply nuprl_refl in k1; apply nuprl_refl in k2;
            generalize (nuprl_uniquely_valued lib A eq1 eq); intro k;
            repeat (autodimp k hyp)).

    assert (eq0 <=2=> eq)
      as eqs2
        by (apply nuprl_sym in k2; apply nuprl_refl in k3; apply nuprl_refl in k2;
            generalize (nuprl_uniquely_valued lib B eq0 eq); intro k;
            repeat (autodimp k hyp)).

    exists A B C D eq; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply @nuprl_ext with (eq1 := eq1); auto.
    apply @nuprl_ext with (eq1 := eq0); auto.
Qed.

Lemma mkc_tequality_equality_in_uni {o} :
  forall lib (A B C D : @CTerm o) i,
    tequalityi lib i (mkc_tequality A B) (mkc_tequality C D)
    <=> (tequalityi lib i A C # tequalityi lib i B D # tequalityi lib i A B).
Proof.
  introv.
  split; intro k.

  - unfold tequalityi, equality in k; exrepnd.
    inversion k1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    inversion h2; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    dands; exists eq; sp; allrw; exists eqa0; auto.

  - unfold tequalityi, equality in k; exrepnd.
    generalize (nuprl_uniquely_valued lib (mkc_uni i) eq0 eq k1 k3); intro eqs1.
    generalize (nuprl_uniquely_valued lib (mkc_uni i) eq1 eq k0 k3); intro eqs2.
    clear k0 k1.
    rw eqs1 in k4; clear eqs1.
    rw eqs2 in k5; clear eqs2.
    exists eq; dands; auto.
    inversion k3; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    fold (@nuprli o lib j0) in h2, h3, h4.
    rw h0; exists (@true_per o).
    dup h2 as na1; apply nuprli_refl in na1.
    dup h4 as na2; apply nuprli_refl in na2.
    generalize (nuprli_uniquely_valued lib j0 j0 A A eqa1 eqa na1 na2); clear na1 na2; intro eqs1.
    dup h3 as nb1; apply nuprli_refl in nb1.
    dup h4 as nb2; apply nuprli_sym in nb2; apply nuprli_refl in nb2.
    generalize (nuprli_uniquely_valued lib j0 j0 B B eqa0 eqa nb1 nb2); clear nb1 nb2; intro eqs2.
    apply CL_teq; fold (@nuprli o lib j0).
    exists A B C D eqa; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprli_ext with (eq1 := eqa1); auto.
    apply nuprli_ext with (eq1 := eqa0); auto.
Qed.

Lemma equality_in_mkc_tequality {o} :
  forall lib (a b A B : @CTerm o),
    equality lib a b (mkc_tequality A B) <=> tequality lib A B.
Proof.
  introv; split; intro k.

  - apply inhabited_implies_tequality in k.
    rw @tequality_iff_mkc_tequality in k; auto.

  - exists (@true_per o); dands; auto; try (complete (unfold true_per; auto)).
    unfold tequality in k; exrepnd.
    apply CL_teq.
    exists A B A B eq; fold (@nuprl o); sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprl_refl in k0; auto.
    apply nuprl_sym in k0; apply nuprl_refl in k0; auto.
Qed.
