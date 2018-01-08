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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_image.
Require Export csubst6.


Lemma equality_in_mkc_squash {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 (mkc_squash T)
    <=> (computes_to_valc_ex_bar lib t1 mkc_axiom
         # computes_to_valc_ex_bar lib t2 mkc_axiom
         # inhabited_type_bar lib T).
Proof.
  intros.
  rw @equality_in_mkc_image; split; intro e; exrepnd; dands; eauto 3 with slow.

  - eapply all_in_ex_bar_modus_ponens1;[|exact e]; clear e; introv x e.
    applydup @equal_in_image_prop in e; exrepnd.
    pose proof (e2 _ (lib_extends_refl lib')) as e2; cbv beta in *; spcast.
    pose proof (cequivc_beta lib' nvarx (mk_cv [nvarx] mkc_axiom) a1) as c1.

    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var.

    assert (cequivc lib' t1 mkc_axiom) as c3;
      [|eapply cequivc_axiom;[|apply cequivc_sym;eauto]; eauto 3 with slow];[].
    eapply cequivc_trans;[exact e2|]; auto.

  - eapply all_in_ex_bar_modus_ponens1;[|exact e]; clear e; introv x e.
    applydup @equal_in_image_prop in e; exrepnd.
    pose proof (e3 _ (lib_extends_refl lib')) as e3; cbv beta in *; spcast.
    pose proof (cequivc_beta lib' nvarx (mk_cv [nvarx] mkc_axiom) a2) as c2.

    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var.

    assert (cequivc lib' t2 mkc_axiom) as c3;
      [|eapply cequivc_axiom;[|apply cequivc_sym;eauto]; eauto 3 with slow];[].
    eapply cequivc_trans;[exact e3|]; auto.

  - eapply all_in_ex_bar_modus_ponens1;[|exact e]; clear e; introv x e.
    apply equal_in_image_prop in e; exrepnd.
    exists a1; auto.

  - eapply all_in_ex_bar_modus_ponens3;[|exact e0|exact e1|exact e];
      clear e0 e1 e; introv x e0 e1 e; spcast.

    unfold inhabited_type in e; exrepnd.
    applydup @inhabited_implies_tequality in e2; dands; auto.
    apply eq_in_image_eq with (a1 := t) (a2 := t); auto; introv y; spcast.

    {
      apply cequivc_trans with (b := mkc_axiom).
      { apply computes_to_valc_implies_cequivc; eauto 3 with slow. }
      apply cequivc_sym.
      generalize (cequivc_beta lib'0 nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
      allrw @mk_cv_as_cvterm_var.
      allrw @substc_cvterm_var; sp.
    }

    {
      apply cequivc_trans with (b := mkc_axiom).
      { apply computes_to_valc_implies_cequivc; eauto 3 with slow. }
      apply cequivc_sym.
      generalize (cequivc_beta lib'0 nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
      allrw @mk_cv_as_cvterm_var.
      allrw @substc_cvterm_var; sp.
    }
Qed.

Lemma tequality_mkc_squash {p} :
  forall lib (T1 T2 : @CTerm p),
    tequality lib (mkc_squash T1) (mkc_squash T2)
    <=> tequality lib T1 T2.
Proof.
  introv.
  rw @tequality_mkc_image; split; sp; spcast; eauto 3 with slow.
Qed.

Lemma implies_tequality_equality_mkc_squash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> inhabited_type lib t1
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv teq inh.
  rw @equality_in_mkc_squash.
  rw @tequality_mkc_squash.
  dands; auto; spcast; eauto 3 with slow.
Qed.

Lemma implies_tequality_equality_mkc_squash_and {o} :
  forall lib (t1 t2 : @CTerm o),
    (tequality lib t1 t2 # inhabited_type lib t1)
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv h.
  apply implies_tequality_equality_mkc_squash; sp.
Qed.

Lemma equality_in_mkc_squash_ax {o} :
  forall lib (t : @CTerm o),
    equality lib mkc_axiom mkc_axiom (mkc_squash t)
    <=> inhabited_type_bar lib t.
Proof.
  introv.
  rw @equality_in_mkc_squash; split; intro h; repnd; dands; auto; spcast; eauto 3 with slow.
Qed.

Lemma inhabited_squash {o} :
  forall lib (t : @CTerm o),
    inhabited_type lib (mkc_squash t) <=> inhabited_type_bar lib t.
Proof.
  introv.
  split; intro k; allunfold @inhabited_type; exrepnd.

  - allrw @equality_in_mkc_squash; repnd; auto.

  - exists (@mkc_axiom o).
    apply equality_in_mkc_squash; dands; spcast; auto; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_squash {o} :
  forall (T : @NTerm o) s vs,
    cover_vars_upto (mk_squash T) s vs
    <=> cover_vars_upto T s vs.
Proof.
  introv.
  unfold cover_vars_upto.
  simpl.
  allrw app_nil_r; allrw remove_nvars_nil_l; sp.
Qed.

Lemma lsubstc_vars_mk_squash_as_mkcv {o} :
  forall (T : @NTerm o) w s vs c,
    {w' : wf_term T
     & {c' : cover_vars_upto T s vs
     & lsubstc_vars (mk_squash T) w s vs c
       = mkcv_squash vs (lsubstc_vars T w' s vs c')}}.
Proof.
  introv.
  dup w as w'.
  rw @wf_squash in w'.
  dup c as c'.
  rw @cover_vars_upto_squash in c'.

  exists w' c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.
