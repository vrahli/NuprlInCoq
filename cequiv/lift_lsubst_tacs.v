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


Require Export csubst.
Require Export cequiv_props.
Require Export subst_per.
Require Export csubst3.
Require Export csubst5.
Require Export csubst_ref.
Require Export csubst_decide.
Require Export csubst_arith.
Require Export csubst_cft.
Require Export terms_union.
Require Export terms_image.
Require Export cequiv_arith_props.
Require Export compare_cterm.
Require Export terms_try.
Require Export csubst_fresh.
Require Export psquash.


Tactic Notation "one_lift_lsubst" constr(T) ident(name) tactic(tac) :=
  match T with
    (* Axiom *)
    | context [lsubstc mk_axiom ?w ?s ?c ] =>
      generalize (lsubstc_mk_axiom w s c);
        intro name; tac

    (* Bottom *)
    | context [lsubstc mk_bottom ?w ?s ?c ] =>
      generalize (lsubstc_mk_bottom w s c);
        intro name; tac

    (* Base *)
    | context [lsubstc mk_base ?w ?s ?c ] =>
      generalize (lsubstc_mk_base w s c);
        intro name; tac

    (* Int *)
    | context [lsubstc mk_int ?w ?s ?c ] =>
      generalize (lsubstc_mk_int w s c);
        intro name; tac

    (* QNat *)
    | context [lsubstc mk_qnat ?w ?s ?c ] =>
      generalize (lsubstc_mk_qnat w s c);
        intro name; tac

    (* Atom *)
    | context [lsubstc mk_atom ?w ?s ?c ] =>
      generalize (lsubstc_mk_atom w s c);
        intro name; tac

    (* UAtom *)
    | context [lsubstc mk_uatom ?w ?s ?c ] =>
      generalize (lsubstc_mk_uatom w s c);
        intro name; tac

    (* Top *)
    | context [lsubstc mk_top ?w ?s ?c ] =>
      generalize (lsubstc_mk_top w s c);
        intro name; tac

    (* Bot *)
    | context [lsubstc mk_bot ?w ?s ?c ] =>
      generalize (lsubstc_mk_bot w s c);
        intro name; tac

    (* Universe *)
    | context [lsubstc (mk_uni ?i) ?w ?s ?c ] =>
      generalize (lsubstc_mk_uni i w s c);
        intro name; tac

    (* integer *)
    | context [lsubstc (mk_integer ?i) ?w ?s ?c ] =>
      generalize (lsubstc_mk_integer i s w c);
        intro name; tac

    (* Token *)
    | context [lsubstc (mk_token ?t) ?w ?s ?c ] =>
      generalize (lsubstc_mk_token t w s c);
        intro name; tac

    (* UToken *)
    | context [@lsubstc ?o (mk_utoken ?t) ?w ?s ?c ] =>
      generalize (@lsubstc_mk_utoken o t w s c);
        intro name; tac

    (* Zero *)
    | context [lsubstc mk_zero ?w ?s ?c ] =>
      generalize (lsubstc_mk_zero w s c);
        intro name; tac

    (* EtaPair *)
    | context [lsubstc (mk_eta_pair ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_eta_pair_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Not *)
    | context [lsubstc (mk_not ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_not_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Pertype *)
    | context [lsubstc (mk_pertype ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_pertype_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* IPertype *)
    | context [lsubstc (mk_ipertype ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_ipertype_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* SPertype *)
    | context [lsubstc (mk_spertype ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_spertype_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Sleep *)
    | context [lsubstc (mk_sleep ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_sleep_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Exception *)
    | context [lsubstc (mk_exception ?a ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_exception_ex a x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* TUni *)
    | context [lsubstc (mk_tuni ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_tuni_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Erase_rel *)
    | context [lsubstc (erase_rel ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_erase_rel_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Erase *)
    | context [lsubstc (erase ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_erase_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Admiss *)
    | context [lsubstc (mk_admiss ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_admiss_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Mono *)
    | context [lsubstc (mk_mono ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_mono_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Partial *)
    | context [lsubstc (mk_partial ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_partial_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

(*    | context [lsubstc (mk_esquash ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_esquash_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr*)

    (* Fix *)
    | context [lsubstc (mk_fix ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_fix_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Halts *)
    | context [lsubstc (mk_halts ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_halts_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Isexc *)
    | context [lsubstc (mk_isexc ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_isexc_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* HaltsLike *)
    | context [lsubstc (mk_halts_like ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_halts_like_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Or *)
    | context [lsubstc (mk_or ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_or_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* EOr *)
    | context [lsubstc (mk_eor ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_eor_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Add *)
    | context [lsubstc (mk_add ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_add_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* ArithOp *)
    | context [lsubstc (mk_arithop ?op ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_arithop_ex op x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
    (* Minus *)
    | context [lsubstc (mk_minus ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_minus_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Apply *)
    | context [lsubstc (mk_apply ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_apply_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Apply2 *)
    | context [lsubstc (mk_apply2 ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_apply2_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* FreshFromAtom *)
    | context [lsubstc (mk_free_from_atom ?x ?y ?T) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let wt := fresh "wT" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let ct := fresh "cT" in
      generalize (lsubstc_mk_free_from_atom_ex x y T s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [wt name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [ct name];
        clear_irr; tac

    (* EFreshFromAtom *)
    | context [lsubstc (mk_efree_from_atom ?x ?y ?T) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let wt := fresh "wT" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let ct := fresh "cT" in
      generalize (lsubstc_mk_efree_from_atom_ex x y T s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [wt name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [ct name];
        clear_irr; tac

    (* FreshFromAtoms *)
    | context [lsubstc (mk_free_from_atoms ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_free_from_atoms_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Equality *)
    | context [lsubstc (mk_equality ?x ?y ?T) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let wt := fresh "wT" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let ct := fresh "cT" in
      generalize (lsubstc_mk_equality_ex x y T s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [wt name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [ct name];
        clear_irr; tac

    (* REquality *)
    | context [lsubstc (mk_requality ?x ?y ?T) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let wt := fresh "wT" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let ct := fresh "cT" in
      generalize (lsubstc_mk_requality_ex x y T s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [wt name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [ct name];
        clear_irr; tac

    (* TEquality *)
    | context [lsubstc (mk_tequality ?x ?y) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_tequality_ex x y s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* IsPair *)
    | context [lsubstc (mk_ispair ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_ispair_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* CanTest *)
    | context [lsubstc (mk_can_test ?test ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_can_test_ex test x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* IntEq *)
    | context [lsubstc (mk_int_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_int_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* AtomEq *)
    | context [lsubstc (mk_atom_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_atom_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Less *)
    | context [lsubstc (mk_less ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_less_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* le *)
    | context [lsubstc (mk_le ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      pose proof (lsubstc_mk_le_ex a b s w c) as name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* IsInl *)
    | context [lsubstc (mk_isinl ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_isinl_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac
    (* CanTest *)
    | context [lsubstc (mk_can_test ?test ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_can_test_ex test x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac
    (* IntEq *)
    | context [lsubstc (mk_int_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_int_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
   (* AtomEq *)
    | context [lsubstc (mk_atom_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_int_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
   (* Less *)
    | context [lsubstc (mk_less ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_less_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* IsInr *)
    | context [lsubstc (mk_isinr ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_isinr_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac
    (* CanTest *)
    | context [lsubstc (mk_can_test ?test ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_can_test_ex test x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac
    (* IntEq *)
    | context [lsubstc (mk_int_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_int_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
   (* AtomEq *)
    | context [lsubstc (mk_atom_eq ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_int_eq_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
   (* Less *)
    | context [lsubstc (mk_less ?m ?n ?x ?y) ?w ?s ?c] =>
      let wm := fresh "wm" in
      let wn := fresh "wn" in
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let cn := fresh "cn" in
      let cm := fresh "cm" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_less_ex m n x y s w c);
        intro name;
        destruct name as [wm name];
        destruct name as [wn name];
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [cm name];
        destruct name as [cn name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* IsAxiom *)
    | context [lsubstc (mk_isaxiom ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_isaxiom_ex2 x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* IsInt *)
    | context [lsubstc (mk_isint ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_isint_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* IsLambda *)
    | context [lsubstc (mk_islambda ?x ?y ?z) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_islambda_ex x y z s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* Member *)
    | context [lsubstc (mk_member ?x ?T) ?w ?s ?c] =>
      let wt := fresh "wt" in
      let wT := fresh "wT" in
      let ct := fresh "ct" in
      let cT := fresh "cT" in
      generalize (lsubstc_mk_member_ex x T s w c);
        intro name;
        destruct name as [wt name];
        destruct name as [wT name];
        destruct name as [ct name];
        destruct name as [cT name];
        clear_irr; tac

    (* RMember *)
    | context [lsubstc (mk_rmember ?x ?T) ?w ?s ?c] =>
      let wt := fresh "wt" in
      let wT := fresh "wT" in
      let ct := fresh "ct" in
      let cT := fresh "cT" in
      generalize (lsubstc_mk_rmember_ex x T s w c);
        intro name;
        destruct name as [wt name];
        destruct name as [wT name];
        destruct name as [ct name];
        destruct name as [cT name];
        clear_irr; tac

    (* Type *)
    | context [lsubstc (mk_type ?x) ?w ?s ?c] =>
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      generalize (lsubstc_mk_type_ex x s w c);
        intro name;
        destruct name as [wt name];
        destruct name as [ct name];
        clear_irr; tac

    (* Isect *)
    | context [lsubstc (mk_isect ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_isect_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Eisect *)
    | context [lsubstc (mk_eisect ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_eisect_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Disect *)
    | context [lsubstc (mk_disect ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_disect_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Set *)
    | context [lsubstc (mk_set ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_set_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* TUnion *)
    | context [lsubstc (mk_tunion ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_tunion_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Binary (non-disjoint) union *)
    | context [lsubstc (mk_bunion ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_bunion_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Spread *)
    | context [lsubstc (mk_spread ?a ?x ?y ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_spread_ex a x y b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* CallByValue *)
    | context [lsubstc (mk_cbv ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_cbv_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Try *)
    | context [lsubstc (mk_try ?a ?n ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_try_ex a n x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* LastCs *)
    | context [lsubstc (mk_last_cs ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_last_cs_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Inl *)
    | context [lsubstc (mk_inl ?a ) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_inl_ex a s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Inr *)
    | context [lsubstc (mk_inr ?a ) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_inr_ex a s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Outl  *)
    | context [lsubstc (mk_outl ?a ) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_outl_ex a s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Outr *)
    | context [lsubstc (mk_outr ?a ) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_outr_ex a s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Decide *)
    | context [lsubstc (mk_decide ?a ?x ?u ?y ?v) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      generalize (lsubstc_mk_decide_ex a x u y v s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        clear_irr; tac

    (* Function *)
    | context [lsubstc (mk_function ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_function_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Non-dependent Function *)
    | context [lsubstc (mk_fun ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_fun_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Subtype Relation *)
    | context [lsubstc (mk_subtype_rel ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_subtype_rel_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Uniform non-dependent Function *)
    | context [lsubstc (mk_ufun ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_ufun_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Extensional uniform non-dependent Function *)
    | context [lsubstc (mk_eufun ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_eufun_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Product *)
    | context [lsubstc (mk_product ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_product_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Non-dependent Product *)
    | context [lsubstc (mk_prod ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_prod_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Iff *)
    | context [lsubstc (mk_iff ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_iff_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* W type *)
    | context [lsubstc (mk_w ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_w_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* M type *)
    | context [lsubstc (mk_m ?a ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_m_ex a x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* pW type *)
    | context [lsubstc (mk_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p) ?w ?s ?c] =>
      let wP := fresh "wP" in
      let wA := fresh "wA" in
      let wB := fresh "wB" in
      let wC := fresh "wC" in
      let wp := fresh "wp" in
      let cvP := fresh "cvP" in
      let cvA := fresh "cvA" in
      let cvB := fresh "cvB" in
      let cvC := fresh "cvC" in
      let cvp := fresh "cvp" in
      generalize (lsubstc_mk_pw_ex P ap A bp ba B cp ca cb C p s w c);
        intro name;
        destruct name as [wP name];
        destruct name as [wA name];
        destruct name as [wB name];
        destruct name as [wC name];
        destruct name as [wp name];
        destruct name as [cvP name];
        destruct name as [cvA name];
        destruct name as [cvB name];
        destruct name as [cvC name];
        destruct name as [cvp name];
        clear_irr; tac

    (* pM type *)
    | context [lsubstc (mk_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p) ?w ?s ?c] =>
      let wP := fresh "wP" in
      let wA := fresh "wA" in
      let wB := fresh "wB" in
      let wC := fresh "wC" in
      let wp := fresh "wp" in
      let cvP := fresh "cvP" in
      let cvA := fresh "cvA" in
      let cvB := fresh "cvB" in
      let cvC := fresh "cvC" in
      let cvp := fresh "cvp" in
      generalize (lsubstc_mk_pm_ex P ap A bp ba B cp ca cb C p s w c);
        intro name;
        destruct name as [wP name];
        destruct name as [wA name];
        destruct name as [wB name];
        destruct name as [wC name];
        destruct name as [wp name];
        destruct name as [cvP name];
        destruct name as [cvA name];
        destruct name as [cvB name];
        destruct name as [cvC name];
        destruct name as [cvp name];
        clear_irr; tac

    (* Lambda *)
    | context [lsubstc (mk_lam ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_lam_ex x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Fresh *)
    | context [lsubstc (mk_fresh ?x ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_fresh_ex x b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* Cequiv *)
    | context [lsubstc (mk_cequiv ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_cequiv_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Approx *)
    | context [lsubstc (mk_approx ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_approx_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Pair *)
    | context [lsubstc (mk_pair ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_pair_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Sup *)
    | context [lsubstc (mk_sup ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_sup_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Refl *)
    | context [lsubstc (mk_refl ?a) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_refl_ex a s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* TExc *)
    | context [lsubstc (mk_texc ?a1 ?a2) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_texc_ex a1 a2 s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Union *)
    | context [lsubstc (mk_union ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_union_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* EUnion *)
    | context [lsubstc (mk_eunion ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_eunion_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Image *)
    | context [lsubstc (mk_image ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      generalize (lsubstc_mk_image_ex a b s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac

    (* Squash *)
    | context [lsubstc (mk_squash ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_squash_ex x s w c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac

    (* PSquash *)
    | context [lsubstc (mk_psquash ?x) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      generalize (lsubstc_mk_psquash_ex2 x w s c);
        intro name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac
  end.

Lemma implies_prod_left :
  forall c a b, (a -> b) -> ((a # c) -> (b # c)).
Proof. sp. Qed.

Lemma implies_prod_right :
  forall c a b, (a -> b) -> ((c # a) -> (c # b)).
Proof. sp. Qed.

Ltac build_al_exp al x y exp h :=
  match exp with
    (* respects2 *)
    | ?R y =>
      assert (respects1 alphaeqc R) as h by eauto with respects;
        generalize (h x y al);
        clear h;
        intro h

    (* respects2 *)
    | ?R ?a1 y =>
      assert (respects2 alphaeqc R) as h by eauto with respects;
        generalize (snd h a1 x y al);
        clear h;
        intro h

    | ?R y ?a1 =>
      assert (respects2 alphaeqc R) as h by eauto with respects;
        generalize (fst h x a1 y al);
        clear h;
        intro h

    (* respects3 *)
    | ?R ?a1 ?a2 y =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (snd (snd h) a1 a2 x y al);
        clear h;
        intro h

    | ?R ?a1 y ?a2 =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (fst (snd h) a1 x a2 y al);
        clear h;
        intro h

    | ?R y ?a1 ?a2 =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (fst h x a1 a2 y al);
        clear h;
        intro h

    (* product *)
    | ?a # ?b =>
      build_al_exp al x y b h;
        match type of h with
          | ?t1 -> ?t2 =>
            generalize (implies_prod_right a t1 t2 h);
              clear h;
              intro h
        end

    | ?a # ?b =>
      build_al_exp al x y a h;
        match type of h with
          | ?t1 -> ?t2 =>
            generalize (implies_prod_left b t1 t2 h);
              clear h;
              intro h
        end
  end.

Ltac build_al_exp_h al x y exp h :=
  match exp with
    (* respects1 *)
    | ?R x =>
      assert (respects1 alphaeqc R) as h by eauto with respects;
        generalize (h x y al);
        clear h;
        intro h

    (* respects2 *)
    | ?R ?a1 x =>
      assert (respects2 alphaeqc R) as h by eauto with respects;
        generalize (snd h a1 x y al);
        clear h;
        intro h

    | ?R x ?a1 =>
      assert (respects2 alphaeqc R) as h by eauto with respects;
        generalize (fst h x a1 y al);
        clear h;
        intro h

    (* respects3 *)
    | ?R ?a1 ?a2 x =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (snd (snd h) a1 a2 x y al);
        clear h;
        intro h

    | ?R ?a1 x ?a2 =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (fst (snd h) a1 x a2 y al);
        clear h;
        intro h

    | ?R x ?a1 ?a2 =>
      assert (respects3 alphaeqc R) as h by eauto with respects;
        generalize (fst h x a1 a2 y al);
        clear h;
        intro h

    (* product *)
    | ?a # ?b =>
      build_al_exp_h al x y b h;
        match type of h with
          | ?t1 -> ?t2 =>
            generalize (implies_prod_right a t1 t2 h);
              clear h;
              intro h
        end

    | ?a # ?b =>
      build_al_exp_h al x y a h;
        match type of h with
          | ?t1 -> ?t2 =>
            generalize (implies_prod_left b t1 t2 h);
              clear h;
              intro h
        end
  end.

Ltac rwal_c al :=
  let h := fresh "h" in
  match type of al with
    | alphaeqc ?x ?y =>
      match goal with
        | [ |- context[?y] ] =>
          match goal with
            | [ |- ?exp ] =>
              build_al_exp al x y exp h;
                apply h;
                clear h
          end
      end
  end.

Ltac rwal_h al H :=
  let h := fresh "h" in
  match type of al with
    | alphaeqc ?x ?y =>
      let exp := type of H in
      match exp with
        | context[?x] =>
          build_al_exp_h al x y exp h;
            apply h in H;
            clear h
      end
  end.

Ltac rwal al :=
  let h := fresh "h" in
  match type of al with
    | alphaeqc ?x ?y =>
      match goal with
        | [ |- context[?y] ] =>
          match goal with
            | [ |- ?exp ] =>
              build_al_exp al x y exp h;
                apply h;
                clear h
          end

        | [ H : context[?x] |- _ ] =>
          let exp := type of H in
          build_al_exp_h al x y exp h;
            apply h in H;
            clear h
      end
  end.

(*
Require Import nuprl_props.

Lemma xxx :
  forall a b A B w s c,
    True # (False # equality a b (lsubstc (mk_fun A B) w s c)).
Proof.
  introv.
  one_lift_lsubst (equality a b (lsubstc (mk_fun A B) w s c)) xxx.
  apply alphaeqc_sym in xxx.
  rwal xxx.

Abort.

Lemma xxx :
  forall b A B w s c,
    True # (False # tequality b (lsubstc (mk_fun A B) w s c)).
Proof.
  introv.
  one_lift_lsubst (tequality b (lsubstc (mk_fun A B) w s c)) xxx.
  apply alphaeqc_sym in xxx.
  rwal xxx.

Abort.

Lemma xxx :
  forall a b A B w s c,
    True # (False # equality a b (lsubstc (mk_fun A B) w s c)) -> True.
Proof.
  introv X.
  one_lift_lsubst (equality a b (lsubstc (mk_fun A B) w s c)) xxx.
  rwal xxx.

Abort.
*)

Ltac one_lift_lsubst_concl :=
  match goal with
    | [ |- ?T ] =>
      let name := fresh "eq" in
      one_lift_lsubst
        T
        name
        (first [ rewrite name
               | progress (apply alphaeqc_sym in name; rwal_c name)
               ]);
        clear name
  end.

Ltac one_lift_lsubst_hyp H :=
  let T := type of H in
  let name := fresh "eq" in
  one_lift_lsubst
    T name
    (first [ rewrite name in H
           | progress (rwal_h name H)
           ]); clear name.

Ltac lift_lsubsts :=
  repeat (match goal with
            | [ H : context [lsubstc _ _ _ _ ] |- _ ] => one_lift_lsubst_hyp H
            | [ |- context [lsubstc _ _ _ _ ] ] => one_lift_lsubst_concl
          end).

Ltac lift_lsubst_concl := repeat one_lift_lsubst_concl.
Ltac lift_lsubst_hyp H := repeat (one_lift_lsubst_hyp H).

Tactic Notation "lift_lsubst" := lift_lsubst_concl.
Tactic Notation "lift_lsubst" "in" ident(H) := lift_lsubst_hyp H.

Ltac one_lift_lsubst2_concl :=
  match goal with
    | [ |- ?T ] =>
      let name := fresh "eq" in
      one_lift_lsubst2
        T
        name
        (first [ rewrite name
               | progress (apply alphaeqc_sym in name; rwal_c name)
               ]);
        clear name
  end.

Ltac one_lift_lsubst2_hyp H :=
  let T := type of H in
  let name := fresh "eq" in
  one_lift_lsubst2
    T name
    (first [ rewrite name in H
           | progress (rwal_h name H)
           ]); clear name.

Ltac lift_lsubsts2 :=
  repeat (match goal with
            | [ H : context [lsubstc _ _ _ _ ] |- _ ] => one_lift_lsubst2_hyp H
            | [ |- context [lsubstc _ _ _ _ ] ] => one_lift_lsubst2_concl
          end).

Tactic Notation "one_lift_lsubst_squash" constr(T) ident(name) tactic(tac) :=
  match T with
    | context [lsubstc (mk_psquash ?a) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      pose proof (lsubstc_mk_psquash_ex2 a w s c) as name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac
  end.

Ltac one_lift_lsubst_squash_concl :=
  match goal with
    | [ |- ?T ] =>
      let name := fresh "eq" in
      one_lift_lsubst_squash
        T
        name
        (first [ rewrite name
               | progress (apply alphaeqc_sym in name; rwal_c name)
               ]);
        clear name
  end.

Ltac one_lift_lsubst_squash_hyp H :=
  let T := type of H in
  let name := fresh "eq" in
  one_lift_lsubst_squash
    T name
    (first [ rewrite name in H
           | progress (rwal_h name H)
           ]); clear name.

Ltac lift_lsubsts_squash :=
  repeat (match goal with
            | [ H : context [lsubstc _ _ _ _ ] |- _ ] => one_lift_lsubst_squash_hyp H
            | [ |- context [lsubstc _ _ _ _ ] ] => one_lift_lsubst_squash_concl
          end).
