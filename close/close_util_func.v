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


  Website: http://nuprl.org/html/verification/
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export per_ceq_bar.
Require Export close_util_bar.


Definition per_func_ext_eq_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_func_ext_eq lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).

  repeat introv.
  unfold per_func_ext_eq, raise_lib_per_fam, raise_lib_per, raise_ext_per, raise_ext_per_fam; simpl.
  split; intro h; exrepnd; apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h.

  - repeat introv.
    pose proof (h a a') as h; simpl in *.
    assert (eqa lib'0 (lib_extends_trans e0 e) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.

  - repeat introv.
    pose proof (h a a') as h; simpl in *.
    assert (eqa lib'0 (lib_extends_trans e0 y) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.
Defined.

Lemma implies_eq_term_equals_per_func_ext_eq {o} :
  forall lib (eqa eqb : lib-per(lib,o)) (eqc : lib-per-fam(lib,eqa,o)) (eqd : lib-per-fam(lib,eqb,o)),
    (in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x)))
    -> (in_ext_ext lib (fun lib' x => forall a a' (u : eqa lib' x a a') (v : eqb lib' x a a'), (eqc lib' x a a' u) <=2=> (eqd lib' x a a' v)))
    -> (per_func_ext_eq lib eqa eqc) <=2=> (per_func_ext_eq lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_ext_eq; introv; split; intro h;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h;
          repeat introv.

  - dup e0 as e'; apply eqas in e'.
    apply (eqbs _ _ a a' e' e0); simpl in *.
    eapply h; eauto 3 with slow.

  - dup e0 as e'; apply eqas in e'.
    apply (eqbs _ _ a a' e0 e'); simpl in *.
    eapply h; eauto 3 with slow.
Qed.

Lemma implies_eq_term_equals_per_func_eq {o} :
  forall (eqa eqb : per(o)) (eqc : per-fam(eqa)) (eqd : per-fam(eqb)),
    (eqa <=2=> eqb)
    -> (forall a a' (u : eqa a a') (v : eqb a a'), (eqc a a' u) <=2=> (eqd a a' v))
    -> (per_func_eq eqa eqc) <=2=> (per_func_eq eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_eq; introv; split; intro h; introv.

  - dup e as e'; apply eqas in e'.
    apply (eqbs a a' e' e); simpl in *.
    eapply h; eauto 3 with slow.

  - dup e as e'; apply eqas in e'.
    apply (eqbs a a' e e'); simpl in *.
    eapply h; eauto 3 with slow.
Qed.

Lemma per_bar_eq_per_func_ext_eq_lib_per {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) eqb,
    (per_bar_eq lib (per_func_ext_eq_lib_per eqa eqb))
    <=2=> (per_func_ext_eq lib eqa eqb).
Proof.
  introv; simpl; unfold per_bar_eq; split; intro h; eauto 3 with slow.

  - unfold per_func_ext_eq; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_func_ext_eq in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_func_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).

  - unfold per_func_ext_eq in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_func_ext_eq; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_func_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).
Qed.
