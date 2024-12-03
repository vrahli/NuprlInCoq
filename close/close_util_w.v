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
Require Export nuprl_mon_func.
Require Export close_util_bar.


(*
Definition weq_bar_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            weq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).

  repeat introv.
  unfold weq_bar; simpl;
  split; intro h; exrepnd;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h.

  - eapply weq_eq_term_equals; try exact h; try apply lib_per_cond.
    introv; apply lib_per_fam_cond.

  - eapply weq_eq_term_equals; try exact h; try apply lib_per_cond.
    introv; apply lib_per_fam_cond.
Defined.
*)

Lemma implies_eq_term_equals_weq_bar {o} :
  forall lib (eqa eqb : lib-per(lib,o)) (eqc : lib-per-fam(lib,eqa,o)) (eqd : lib-per-fam(lib,eqb,o)),
    (in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x)))
    -> (in_ext_ext lib (fun lib' x => forall a a' (u : eqa lib' x a a') (v : eqb lib' x a a'), (eqc lib' x a a' u) <=2=> (eqd lib' x a a' v)))
    -> (weq_bar lib eqa eqc) <=2=> (weq_bar lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold weq_bar; introv; split; intro h;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h;
          repeat introv.

  - eapply weq_eq_term_equals; eauto.

  - eapply weq_eq_term_equals; try exact h; introv; apply eq_term_equals_sym; eauto.
Qed.

Lemma implies_eq_term_equals_weq {o} :
  forall lib (eqa eqb : per(o)) (eqc : per-fam(eqa)) (eqd : per-fam(eqb)),
    (eqa <=2=> eqb)
    -> (forall a a' (u : eqa a a') (v : eqb a a'), (eqc a a' u) <=2=> (eqd a a' v))
    -> (weq lib eqa eqc) <=2=> (weq lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  split; intro h; eapply weq_eq_term_equals; try exact h; introv; auto;
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_bar_eq_weq_bar_lib_per {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) eqb,
    (per_bar_eq lib (weq_bar_lib_per lib eqa eqb))
    <=2=> (weq_bar lib eqa eqb).
Proof.
  introv; simpl; unfold per_bar_eq; split; intro h; eauto 3 with slow.

  - eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_weq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).

  - eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_weq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).
Qed.
