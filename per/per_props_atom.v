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
           Abhishek Anand

*)


Require Export per_props_util.


Lemma dest_nuprl_atom {o} :
  forall (lib : @library o) eq,
    nuprl lib mkc_atom mkc_atom eq
    -> per_bar (per_atom nuprl) lib mkc_atom mkc_atom eq.
Proof.
  introv cl.
  eapply dest_close_per_atom_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
  unfold per_atom_bar in *; exrepnd.
  exists bar (equality_of_atom_bar_lib_per lib).
  dands; auto.

  {
    introv br ext; introv.
    unfold per_atom; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_atom_bar_lib_per.
  }
Qed.

Lemma dest_nuprl_atom2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_atom mkc_atom eq
    -> eq <=2=> (equality_of_atom_bar lib).
Proof.
  introv u.
  apply dest_nuprl_atom in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_equality_of_atom_bar_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_atom in *; exrepnd; spcast; auto.
Qed.

Lemma dest_nuprl_uatom {o} :
  forall (lib : @library o) eq,
    nuprl lib mkc_uatom mkc_uatom eq
    -> per_bar (per_uatom nuprl) lib mkc_uatom mkc_uatom eq.
Proof.
  introv cl.
  eapply dest_close_per_uatom_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
  unfold per_uatom_bar in *; exrepnd.
  exists bar (equality_of_uatom_bar_lib_per lib).
  dands; auto.

  {
    introv br ext; introv.
    unfold per_uatom; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_uatom_bar_lib_per.
  }
Qed.

Lemma dest_nuprl_uatom2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_uatom mkc_uatom eq
    -> eq <=2=> (equality_of_uatom_bar lib).
Proof.
  introv u.
  apply dest_nuprl_uatom in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_equality_of_uatom_bar_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_uatom in *; exrepnd; spcast; auto.
Qed.


Lemma tequality_uatom {p} :
  forall lib, @tequality p lib mkc_uatom mkc_uatom.
Proof.
  introv.
  unfold tequality.
  exists (@equality_of_uatom_bar p lib).
  unfold nuprl.
  apply CL_uatom.
  unfold per_uatom; sp; spcast; eauto 3 with slow.
Qed.

Lemma equality_in_uatom_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_uatom
    <=> all_in_ex_bar lib (fun lib => {a : get_patom_set p
        , t1 ===>(lib) (mkc_utoken a)
        # t2 ===>(lib) (mkc_utoken a)}).
Proof.
  intros; split; intro i; exrepnd.

  - unfold equality in i; exrepnd.
    apply dest_nuprl_uatom2 in i1.
    apply i1 in i0; auto.

  - exists (equality_of_uatom_bar lib); dands; auto.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; eauto 3 with slow.
Qed.

Lemma tequality_atom {p} :
  forall lib, @tequality p lib mkc_atom mkc_atom.
Proof.
  introv.
  unfold tequality.
  exists (@equality_of_atom_bar p lib).
  unfold nuprl.
  apply CL_atom.
  unfold per_atom; sp; spcast; eauto 3 with slow.
Qed.

Lemma equality_in_atom_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_atom
    <=> all_in_ex_bar lib (fun lib => {a : String.string
        , t1 ===>(lib) (mkc_token a)
        # t2 ===>(lib) (mkc_token a)}).
Proof.
  intros; split; intro i; exrepnd.

  - unfold equality in i; exrepnd.
    apply dest_nuprl_atom2 in i1.
    apply i1 in i0; auto.

  - exists (equality_of_atom_bar lib); dands; auto.
    apply CL_atom.
    unfold per_atom; dands; spcast; eauto 3 with slow.
Qed.
