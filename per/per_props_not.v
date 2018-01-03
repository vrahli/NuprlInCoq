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

  Authors: Vincent Rahli

 *)


Require Export per_props_false.
Require Export per_props_function.


Definition empty_lib_per_fam {o} {lib} (eqa : lib-per(lib,o)) : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) (a a' : CTerm) (e : eqa lib' x a a') (t t' : @CTerm o) => False).
  introv u v; tcsp.
Defined.

Lemma nuprl_mkc_not {o} :
  forall lib (a b : @CTerm o) eq,
    nuprl lib a b eq
    -> exists eq', nuprl lib (mkc_not a) (mkc_not b) eq'.
Proof.
  introv n.

  pose proof (nuprl_monotone_func lib a b eq n) as tya; exrepnd.
  rename eq' into eqa.

  exists (per_func_ext_eq lib eqa (empty_lib_per_fam eqa)).
  apply CL_func.
  exists eqa (empty_lib_per_fam eqa); dands; tcsp;[].

  unfold type_family.
  unfold mkc_not.
  repeat (rw <- @fold_mkc_fun).
  eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; eauto 3 with slow; try (fold (@nuprl o)).

  { introv; apply tya0. }

  introv.
  allrw @csubst_mk_cv; simpl.
  apply CL_approx.
  eexists; eexists; eexists; eexists; dands; auto; spcast;
    try (rw @mkc_void_eq_mkc_false; rw @mkc_false_eq);
    try (apply @computes_to_valc_refl; apply @iscvalue_mkc_approx).

  { introv; split; intro k; repnd; sp; spcast. }

  {
    introv; split; intro k; tcsp.
    unfold per_approx_eq_bar in k.
    exrepnd.
    pose proof (bar_non_empty bar) as q; exrepnd.
    pose proof (k0 _ q0 _ (lib_extends_refl lib'0)) as k0; simpl in *.
    unfold per_approx_eq in k0; repnd; spcast.
    apply not_axiom_approxc_bot in k0; sp.
  }
Qed.

Lemma tequality_void {p} :
  forall lib, @tequality p lib mkc_void mkc_void.
Proof.
  introv; rw @mkc_void_eq_mkc_false; eauto 3 with slow.
Qed.
Hint Resolve tequality_void : slow.

Lemma type_void {p} :
  forall lib, @type p lib mkc_void.
Proof.
  introv.
  unfold type; eauto 3 with slow.
Qed.
Hint Resolve type_void : slow.

Lemma tequality_not {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_not A1) (mkc_not A2)
    <=>
    tequality lib A1 A2.
Proof.
  intros.
  rw @tequality_fun; split; sp; eauto 3 with slow.
Qed.

Lemma equality_in_not {p} :
  forall lib (t1 t2 A : @CTerm p),
    equality lib t1 t2 (mkc_not A)
    <=>
    (type lib A # in_ext lib (fun lib => !inhabited_type lib A)).
Proof.
  introv.
  rw @equality_in_fun; split; intro e; repnd; dands; auto; tcsp; eauto 3 with slow;[|].

  {
    introv x inh.
    unfold inhabited_type in inh; exrepnd.
    pose proof (e _ x _ _ inh0) as e.
    allapply @equality_in_void; sp.
  }

  {
    introv x ea.
    apply equality_in_void.
    apply (e _ x).
    exists a.
    allapply @equality_refl; auto.
  }
Qed.
