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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


Lemma tequality_uatom {p} :
  forall lib, @tequality p lib mkc_uatom mkc_uatom.
Proof.
  introv.
  unfold tequality.
  exists (@equality_of_uatom_bar p lib).
  unfold nuprl.
  apply CL_uatom.
  unfold per_uatom; sp; spcast;
    try (apply computes_to_valc_refl);
    try (apply iscvalue_mkc_uatom; auto).
Qed.

Lemma equality_in_uatom_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_uatom
    <=> {a : get_patom_set p
        , t1 ===>(lib) (mkc_utoken a)
        # t2 ===>(lib) (mkc_utoken a)}.
Proof.
  intros; split; intro i; exrepnd.

  - unfold equality, nuprl in i; exrepnd.

    (* need the usual dest_nuprl_atom2... *)

XXXXXXX
    inversion i1; subst; try not_univ.
    allunfold @per_uatom; repnd.
    allunfold @eq_term_equals.
    discover.
    allunfold @equality_of_uatom; exrepnd.
    exists u; sp.
  - exists (@equality_of_uatom p lib); dands.
    apply CL_uatom; unfold per_uatom; sp;
    spcast; apply computes_to_value_isvalue_refl; repeat constructor; simpl; sp.
    exists a; sp.
Qed.

Lemma tequality_atom {p} :
  forall lib, @tequality p lib mkc_atom mkc_atom.
Proof.
  introv.
  unfold tequality.
  exists (@equality_of_atom p lib).
  unfold nuprl.
  apply CL_atom.
  unfold per_atom; sp; spcast;
  try (apply computes_to_valc_refl);
  try (apply iscvalue_mkc_atom; auto).
Qed.

Lemma equality_in_atom_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_atom
    <=> {a : String.string
        , t1 ===>(lib) (mkc_token a)
        # t2 ===>(lib) (mkc_token a)}.
Proof.
  intros; split; intro i; exrepnd.
  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    allunfold @per_atom; repnd.
    allunfold @eq_term_equals.
    discover.
    allunfold @equality_of_atom; exrepnd.
    exists s; sp.
  - exists (@equality_of_atom p lib); dands.
    apply CL_atom; unfold per_atom; sp;
    spcast; apply computes_to_value_isvalue_refl; repeat constructor; simpl; sp.
    exists a; sp.
Qed.
