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
Require Export nuprl_mon_func.
Require Export per_ceq_bar.
Require Export close_util_bar.


Lemma per_bar_eq_per_image_eq_bar_lib_per {o} :
  forall lib (bar : @BarLib o lib) (eqa : lib-per(lib,o)) f,
    (per_bar_eq bar (per_image_eq_bar_lib_per lib eqa f))
    <=2=> (per_image_eq_bar lib eqa f).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_bar_eq in h; simpl in *.
    unfold per_image_eq_bar in *; simpl in *.

    assert (all_in_bar_ext
              bar
              (fun lib' x =>
                 exists (bar : BarLib lib'),
                   all_in_bar_ext bar (fun lib'' y => per_image_eq lib'' (eqa lib'' (lib_extends_trans y x)) f t1 t2))) as q.
    {
      introv br ext; introv.
      pose proof (h _ br _ ext x) as h; simpl in h.
      unfold raise_ext_per in *.
      apply collapse2bars_ext.

      { introv; apply implies_eq_term_equals_eq_image_eq; apply lib_per_cond. }

      exrepnd; exists bar'.
      introv br' ext'; introv.
      pose proof (h0 _ br' _ ext' x0) as h0; simpl in *; exrepnd.
      exists bar0; introv br'' ext''; introv.
      pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
      eapply implies_eq_term_equals_eq_image_eq;[|eauto]; apply lib_per_cond.
    }
    clear h.

    apply all_in_bar_ext_exists_bar_implies in q; exrepnd; simpl in *.
    exists (bar_of_bar_fam fbar).
    introv br ext; introv; simpl in *; exrepnd.
    assert (lib_extends lib'0 lib2) as xt by eauto 3 with slow.
    pose proof (q0 _ br _ ext0 x0 _ br0 _ ext xt) as h0; simpl in *; auto.
    eapply implies_eq_term_equals_eq_image_eq;[|eauto]; apply lib_per_cond.

  - unfold per_image_eq_bar in *; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x); introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
    apply (h0 _ br'1 lib'3); eauto 3 with slow.
Qed.
