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
  split; intro h; exrepnd; introv; exists bar; introv br ext; repeat introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in h0.
    pose proof (h0 a a') as h0; simpl in *.
    assert (eqa lib'1 (lib_extends_trans x e) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h0 e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in h0.
    pose proof (h0 a a') as h0; simpl in *.
    assert (eqa lib'1 (lib_extends_trans x y) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h0 e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.
Defined.

Lemma implies_eq_term_equals_per_func_ext_eq {o} :
  forall lib (eqa eqb : lib-per(lib,o)) (eqc : lib-per-fam(lib,eqa,o)) (eqd : lib-per-fam(lib,eqb,o)),
    (in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x)))
    -> (in_ext_ext lib (fun lib' x => forall a a' (u : eqa lib' x a a') (v : eqb lib' x a a'), (eqc lib' x a a' u) <=2=> (eqd lib' x a a' v)))
    -> (per_func_ext_eq lib eqa eqc) <=2=> (per_func_ext_eq lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_ext_eq; introv; split; intro h; exrepnd; exists bar;
    introv br ext; repeat introv.

  - dup e as u.
    apply eqas in u.
    apply (eqbs lib'0 x a a' u e); simpl in *.
    eapply h0; eauto 3 with slow.

  - dup e as u.
    apply eqas in u.
    apply (eqbs lib'0 x a a' e u); simpl in *.
    eapply h0; eauto 3 with slow.
Qed.

Lemma implies_eq_term_equals_per_func_eq {o} :
  forall (eqa eqb : per(o)) (eqc : per-fam(eqa)) (eqd : per-fam(eqb)),
    (eqa <=2=> eqb)
    -> (forall a a' (u : eqa a a') (v : eqb a a'), (eqc a a' u) <=2=> (eqd a a' v))
    -> (per_func_eq eqa eqc) <=2=> (per_func_eq eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_eq; introv; split; intro h; introv.

  - dup e as u.
    apply eqas in u.
    apply (eqbs a a' u e); simpl in *.
    eapply h; eauto 3 with slow.

  - dup e as u.
    apply eqas in u.
    apply (eqbs a a' e u); simpl in *.
    eapply h; eauto 3 with slow.
Qed.

Lemma per_bar_eq_per_func_ext_eq_lib_per {o} :
  forall lib (bar : @BarLib o lib) (eqa : lib-per(lib,o)) eqb,
    (per_bar_eq bar (per_func_ext_eq_lib_per eqa eqb))
    <=2=> (per_func_ext_eq lib eqa eqb).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_bar_eq, per_func_ext_eq_lib_per, per_func_ext_eq in h; simpl in *.

    assert (all_in_bar_ext
              bar
              (fun lib' x =>
                 exists (bar : BarLib lib'),
                   all_in_bar_ext
                     bar
                     (fun lib'' y =>
                        per_func_eq
                          (raise_ext_per eqa x lib'' y)
                          (raise_ext_per_fam eqb x lib'' y)
                          t1 t2))) as q.
    {
      introv br ext; introv.
      pose proof (h _ br _ ext x) as h; simpl in h.
      unfold raise_ext_per in *.
      apply collapse2bars_ext.

      { introv; apply implies_eq_term_equals_per_func_eq; try apply (lib_per_cond _ eqa).
        introv; unfold raise_ext_per_fam; try apply (lib_per_fam_cond _ eqb). }

      exrepnd; exists bar'.
      introv br' ext'; introv.
      pose proof (h0 _ br' _ ext' x0) as h0; simpl in *; exrepnd.
      exists bar0; introv br'' ext''; introv.
      pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
      eapply implies_eq_term_equals_per_func_eq;[| |eauto].
      { apply (lib_per_cond _ eqa). }
      { introv; unfold raise_ext_per_fam; try apply (lib_per_fam_cond _ eqb). }
    }
    clear h.

    apply all_in_bar_ext_exists_bar_implies in q; exrepnd; simpl in *.
    exists (bar_of_bar_fam fbar).
    introv br ext; introv; simpl in *; exrepnd.
    assert (lib_extends lib'0 lib2) as xt by eauto 3 with slow.
    pose proof (q0 _ br _ ext0 x0 _ br0 _ ext xt) as h0; simpl in *; auto.
    eapply implies_eq_term_equals_per_func_eq;[| |eauto].
    { apply (lib_per_cond _ eqa). }
    { introv; unfold raise_ext_per_fam; try apply (lib_per_fam_cond _ eqb). }

  - unfold per_func_ext_eq in *; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x); introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
    apply (h0 _ br'1 lib'3); eauto 3 with slow.
Qed.
