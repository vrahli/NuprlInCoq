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


Definition per_product_eq_bar_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_product_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).

  repeat introv.
  unfold per_product_eq_bar, raise_lib_per_fam, raise_lib_per, raise_ext_per, raise_ext_per_fam; simpl.
  split; intro h; exrepnd; apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h.

  - unfold per_product_eq in *; exrepnd.
    assert (eqa lib'0 (lib_extends_trans e0 y) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb); eauto.

  - unfold per_product_eq in *; exrepnd.
    assert (eqa lib'0 (lib_extends_trans e0 e) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb); eauto.
Defined.

Lemma implies_eq_term_equals_per_product_eq_bar {o} :
  forall lib (eqa eqb : lib-per(lib,o)) (eqc : lib-per-fam(lib,eqa,o)) (eqd : lib-per-fam(lib,eqb,o)),
    (in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x)))
    -> (in_ext_ext lib (fun lib' x => forall a a' (u : eqa lib' x a a') (v : eqb lib' x a a'), (eqc lib' x a a' u) <=2=> (eqd lib' x a a' v)))
    -> (per_product_eq_bar lib eqa eqc) <=2=> (per_product_eq_bar lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_product_eq_bar, per_product_eq; introv; split; intro h;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h;
          repeat introv; exrepnd.

  - dup h3 as u; apply eqas in u.
    exists a a' b b' u; dands; auto.
    apply (eqbs lib' e a a' e0 u); auto.

  - dup h3 as u; apply eqas in u.
    exists a a' b b' u; dands; auto.
    apply (eqbs lib' e a a' u e0); auto.
Qed.

Lemma implies_eq_term_equals_per_product_eq {o} :
  forall lib (eqa eqb : per(o)) (eqc : per-fam(eqa)) (eqd : per-fam(eqb)),
    (eqa <=2=> eqb)
    -> (forall a a' (u : eqa a a') (v : eqb a a'), (eqc a a' u) <=2=> (eqd a a' v))
    -> (per_product_eq lib eqa eqc) <=2=> (per_product_eq lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_product_eq; introv; split; intro h; introv; exrepnd.

  - dup e as u; apply eqas in u.
    exists a a' b b' u; dands; auto.
    apply (eqbs a a' e u); simpl in *; auto.

  - dup e as u; apply eqas in u.
    exists a a' b b' u; dands; auto.
    apply (eqbs a a' u e); simpl in *; auto.
Qed.

Lemma per_bar_eq_per_product_eq_bar_lib_per {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) eqb,
    (per_bar_eq lib (per_product_eq_bar_lib_per eqa eqb))
    <=2=> (per_product_eq_bar lib eqa eqb).
Proof.
  introv; simpl; unfold per_bar_eq in *; split; intro h; eauto 3 with slow.

  - unfold per_product_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_product_eq in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_product_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).

  - unfold per_product_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_product_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_product_eq; try exact h;
      try apply (lib_per_cond _ eqa);
      try apply (lib_per_fam_cond _ eqb).
Qed.
