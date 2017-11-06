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

  Authors: Abhishek Anand & Vincent Rahli

*)



Require Export dest_close_int.
Require Export dest_close_nat.
Require Export dest_close_csname.
Require Export dest_close_func.
Require Export dest_close_isect.
Require Export dest_close_product.
Require Export dest_close_w.
Require Export dest_close_m.
Require Export dest_close_pw.
Require Export dest_close_pm.
Require Export dest_close_disect.
Require Export dest_close_set.
Require Export dest_close_tunion.
Require Export dest_close_approx.
Require Export dest_close_cequiv.
Require Export dest_close_texc.
Require Export dest_close_union.
Require Export dest_close_image.
Require Export dest_close_partial.
Require Export dest_close_admiss.
Require Export dest_close_mono.
Require Export dest_close_ffatom.
Require Export dest_close_pertype.
Require Export dest_close_equality.
Require Export dest_close_requality.
Require Export dest_close_tequality.
Require Export dest_close_base.
Require Export dest_close_atom.
Require Export dest_close_uatom.
Require Export dest_close_uni.
Require Export dest_close_tuni.



Ltac dest_close_lr h :=
  match goal with

    (* function *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_function ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_function ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* function bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) (mkc_function ?A ?v ?B)),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_bar_l ts lib T A v B T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) (mkc_function ?A ?v ?B)),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_bar_r ts lib T A v B T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* function ext *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : in_ext ?lib (fun lib => ?T ===>(lib) (mkc_function ?A ?v ?B)),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_ext_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : in_ext ?lib (fun lib => ?T' ===>(lib) (mkc_function ?A ?v ?B)),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_ext_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* isect *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_isect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_isect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eisect *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eisect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eisect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h
 *)

    (* disect*)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_disect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_disect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* product *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_product ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_product ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* w *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_w ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_w ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* m *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_m ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_m ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pw *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_l ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_r ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pm *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_l ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_r ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  set *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_set ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_set ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  tunion *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tunion ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tunion ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* approx *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* approx ceq *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_l_ceq ts lib bar T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T' (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_r_ceq ts lib bar T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* cequiv *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* cequiv ceq *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_l_ceq ts lib bar T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T' (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_r_ceq ts lib bar T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* texc *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_texc ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_texc ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* union *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_union ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_union ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eunion *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eunion ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eunion ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h
*)

    (* image *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_image ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_image ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* partial *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_partial ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_partial ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* admiss *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_admiss ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_admiss ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* mono *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_mono ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_mono ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_l ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_r ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* efree_from_atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_l ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_r ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atoms *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atoms ?A ?x),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_l ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atoms ?A ?x),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_r ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* ipertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_ipertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_ipertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* spertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_spertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_spertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_l ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_r ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : all_in_bar ?bar (fun lib => ?T ===>(lib) (mkc_equality ?a ?b ?A)),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_bar_l ts lib bar T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : all_in_bar ?bar (fun lib => ?T' ===>(lib) (mkc_equality ?a ?b ?A)),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_bar_r ts lib bar T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_ceq_bar_l ts lib bar T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc_ceq_bar ?bar ?T' (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_ceq_bar_r ts lib bar T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* requality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_requality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_l ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_requality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_r ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tequality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tequality ?a ?b),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_l ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tequality ?a ?b),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_r ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* base *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_base,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_base,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* base bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_base),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_base),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* base ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_base,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_base,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* int *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_int,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_int,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* int bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_int),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_int),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* int ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_int,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_int,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* csname *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_csname,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_csname,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* csname bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_csname),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_csname),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* csname ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_csname,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_csname,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_csname_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* Nat *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_Nat,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_Nat,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* Nat bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_Nat),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_Nat),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* Nat ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_Nat,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_Nat,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_nat_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_atom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_atom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* atom bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_atom),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_atom),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* atom ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_atom,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_atom,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* uatom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_uatom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_uatom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uatom bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_uatom),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_uatom),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* uatom ceq bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T ==b==>(?bar) mkc_uatom,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_ceq_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : ?T' ==b==>(?bar) mkc_uatom,
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_ceq_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* uni *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_uni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_l ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_uni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_r ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tuni *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tuni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_l ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tuni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_r ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

  end.

Ltac dclose_lr := repeat (let h := fresh "h" in dest_close_lr h).
