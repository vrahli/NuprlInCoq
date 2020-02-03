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



Require Export type_sys.
Require Export per_ceq_bar.
Require Export close_util_bar.
Require Export nuprl_mon_func.


Definition per_ffdefs_eq_bar_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (t   : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_ffdefs_eq_bar lib' (raise_lib_per eqa x) t).

  repeat introv.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq, raise_lib_per, raise_ext_per; simpl.
  split; intro h; exrepnd;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h; repnd;
        dands; auto; eauto 3 with slow.
Defined.

Lemma implies_eq_term_equals_per_ffdefs_eq {o} :
  forall lib (eqa eqb : per(o)) t,
    (eqa <=2=> eqb)
    -> (per_ffdefs_eq lib eqa t) <=2=> (per_ffdefs_eq lib eqb t).
Proof.
  introv eqas; introv.
  unfold per_ffdefs_eq; introv; split; intro h; introv; exrepnd;
    dands; auto; eauto 3 with slow.
  eapply ex_nodefsc_change_per;[|eauto]; apply eq_term_equals_sym; auto.
Qed.

(*Lemma implies_eq_term_equals_per_ffdefs_eq_bar {o} :
  forall lib (eqa eqb : lib-per(lib,o)) t,
    (forall lib' x, (eqa lib' x) <=2=> (eqb lib' x))
    -> (per_ffdefs_eq_bar lib eqa t) <=2=> (per_ffdefs_eq_bar lib eqb t).
Proof.
  introv eqas; introv.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq; introv; split; intro h; introv; exrepnd.
    exists bar; introv br ext; introv;
      pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd; dands;
        eauto; eauto 2 with slow.
  eapply ex_nodefsc_change_per;[|eauto]; introv; apply eq_term_equals_sym; auto.
Qed.*)

Lemma per_bar_eq_per_ffdefs_eq_bar_lib_per {o} :
  forall lib (eqa : lib-per(lib,o)) t,
    (per_bar_eq lib (per_ffdefs_eq_bar_lib_per eqa t))
    <=2=> (per_ffdefs_eq_bar lib eqa t).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_ffdefs_eq_bar.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_union_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h;
      try apply (lib_per_cond _ eqa).

  - unfold per_ffdefs_eq_bar in *.
    apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_union_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h;
      try apply (lib_per_cond _ eqa).
Qed.
