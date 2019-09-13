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


  Website: http://nuprl.org/html/verification/
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export per_ceq_bar.
Require Export close_util_bar.


Lemma eq_term_equals_preserves_inhabited {o} :
  forall (e1 e2 : per(o)),
    (e1 <=2=> e2)
    -> inhabited e1
    -> inhabited e2.
Proof.
  unfold inhabited; introv h q; exrepnd; exists t; apply h; auto.
Qed.
Hint Resolve eq_term_equals_preserves_inhabited : slow.

Definition per_set_eq_bar_lib_per {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_set_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).
  repeat introv.
  unfold per_set_eq_bar, per_set_eq.
  split; intro h; exrepnd; apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h; simpl in *; exrepnd;
          unfold raise_ext_per in *; simpl in *.

  - pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as x.
    dup e1 as e2; apply x in e2; clear x.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.

  - pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as x.
    dup e1 as e2; apply x in e2; clear x.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.
Defined.

Lemma implies_eq_term_equals_per_set_eq_bar {o} :
  forall lib (eqa eqb : lib-per(lib,o)) (eqc : lib-per-fam(lib,eqa,o)) (eqd : lib-per-fam(lib,eqb,o)),
    (in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x)))
    -> (in_ext_ext lib (fun lib' x => forall a a' (u : eqa lib' x a a') (v : eqb lib' x a a'), (eqc lib' x a a' u) <=2=> (eqd lib' x a a' v)))
    -> (per_set_eq_bar lib eqa eqc) <=2=> (per_set_eq_bar lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_set_eq_bar, per_set_eq; introv; split; intro h;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h;
          exrepnd.

  - dup e0 as u; apply eqas in u.
    exists u.
    eapply eq_term_equals_preserves_inhabited; eauto.

  - dup e0 as u; apply eqas in u.
    exists u.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply eq_term_equals_sym; eauto.
Qed.

Lemma implies_eq_term_equals_per_set_eq {o} :
  forall (eqa eqb : per(o)) (eqc : per-fam(eqa)) (eqd : per-fam(eqb)),
    (eqa <=2=> eqb)
    -> (forall a a' (u : eqa a a') (v : eqb a a'), (eqc a a' u) <=2=> (eqd a a' v))
    -> (per_set_eq eqa eqc) <=2=> (per_set_eq eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_set_eq; introv; split; intro h; introv; exrepnd.

  - dup e as u.
    apply eqas in u.
    exists u.
    eapply eq_term_equals_preserves_inhabited;[|eauto]; eauto.

  - dup e as u.
    apply eqas in u.
    exists u.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply eq_term_equals_sym; eauto.
Qed.

Lemma per_bar_eq_per_set_eq_bar_lib_per {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) eqb,
    (per_bar_eq lib (per_set_eq_bar_lib_per eqa eqb))
    <=2=> (per_set_eq_bar lib eqa eqb).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_set_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_set_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_set_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).

  - unfold per_set_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_set_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_set_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).
Qed.
