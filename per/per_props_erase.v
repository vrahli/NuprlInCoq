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

  Authors: Vincent Rahli

 *)


Require Export cequiv_tacs.
Require Export per_props_pertype.
Require Export lift_lsubst_tacs.
Require Export subst_tacs.


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
  allunfold @sqper_rel.
  lift_lsubsts; dands.

  - clear trans.
    allunfold @sym_type; introv inh.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec.
    generalize (sym x y); clear sym; intro sym.
    autodimp sym hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y x); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.

  - clear sym.
    allunfold @trans_type; introv inh1 inh2.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    generalize (trans x y z); clear trans; intro trans.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.

    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubst).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lift_lsubsts).
    allrw @inhabited_type_erasec; auto.
Qed.
