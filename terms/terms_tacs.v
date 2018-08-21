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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import terms2.


Lemma deq_nvar_refl :
  forall v, deq_nvar v v = left eq_refl.
Proof.
  introv.
  destruct (deq_nvar v v); sp.
  generalize (@UIPReflDeq NVar deq_nvar v e); intro k.
  rw k; auto.
Qed.

Ltac boolvar_step :=
  match goal with
    | [ |- context[beq_var ?v ?v] ] => rewrite <- beq_var_refl
    | [ |- context[deq_nvar ?v ?v] ] => rewrite deq_nvar_refl
    | [ |- context[deq_nvar ?v1 ?v2] ] =>
      destruct (deq_nvar v1 v2);[try(subst v1)|];try(complete auto)
    | [ |- context[memvar ?v ?s] ] =>
        let name := fresh "b" in
          remember (memvar v s) as name;
        match goal with
          | [ H : name = memvar v s |- _ ] =>
              symmetry in H;
              destruct name;
              [ rewrite fold_assert in H;
                  trw_h assert_memvar H;
                  simpl in H
              | trw_h not_of_assert H;
                  trw_h assert_memvar H;
                  simpl in H
              ]
        end
    | [ |- context[beq_var ?v1 ?v2] ] =>
        let name := fresh "b" in
          remember (beq_var v1 v2) as name;
        match goal with
          | [ H : name = beq_var v1 v2 |- _ ] =>
            destruct name;
              [ apply beq_var_true in H; try subst
              | apply beq_var_false in H
              ]
        end

    | [ H : context[beq_var ?v ?v] |- _ ] => rewrite <- beq_var_refl in H
    | [ H : context[deq_nvar ?v ?v] |- _ ] => rewrite deq_nvar_refl in H
    | [ H : context[deq_nvar ?v1 ?v2] |- _ ] =>
      destruct (deq_nvar v1 v2);[try(subst v1)|];try(complete auto)
    | [ H : context[memvar ?v ?s] |- _ ] =>
      let name := fresh "b" in
      remember (memvar v s) as name;
        match goal with
          | [ J : name = memvar v s |- _ ] =>
            symmetry in J;
              destruct name;
              [ rewrite fold_assert in J;
                trw_h assert_memvar J;
                simpl in J
              | trw_h not_of_assert J;
                trw_h assert_memvar J;
                simpl in J
              ]
        end
    | [ H : context[beq_var ?v1 ?v2] |- _ ] =>
        let name := fresh "b" in
        remember (beq_var v1 v2) as name;
          match goal with
            | [ J : name = beq_var v1 v2 |- _ ] =>
              destruct name;
                [ apply beq_var_true in J; try subst
                | apply beq_var_false in J
                ]
          end

    | [ |- context[if ?x then _ else _] ] =>
      match type of x with
        | {_} + {_} => destruct x
      end
    | [ |- context[if ?x then _ else _] ] =>
      match type of x with
        | sum _ _ => destruct x
      end
    | [ |- context[if ?x then _ else _] ] =>
      match type of x with
        | decidable _ => destruct x
      end
    | [ |- context[d2b ?x] ] =>
      match type of x with
        | decidable _ => destruct x
      end

    | [H : context[if ?x then _ else _] |- _ ] =>
      match type of x with
        | {_} + {_} => destruct x
      end
    | [H : context[if ?x then _ else _] |- _ ] =>
      match type of x with
        | sum _ _ => destruct x
      end
    | [H : context[if ?x then _ else _] |- _ ] =>
      match type of x with
        | decidable _ => destruct x
      end
    | [H : context[d2b ?x] |- _ ] =>
      match type of x with
        | decidable _ => destruct x
      end

    | [ |- context[deq_nat           ?x ?y] ] => destruct (deq_nat           x y)
    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y)
    | [ |- context[opsign_dec        ?x ?y] ] => destruct (opsign_dec        x y)
    | [ |- context[Z_noteq_dec       ?x ?y] ] => destruct (Z_noteq_dec       x y)
    | [ |- context[parameter_dec     ?x ?y] ] => destruct (parameter_dec     x y)
    | [ |- context[parameters_dec    ?x ?y] ] => destruct (parameters_dec    x y)

    | [ H : context[deq_nat           ?x ?y] |- _ ] => destruct (deq_nat           x y)
    | [ H : context[String.string_dec ?x ?y] |- _ ] => destruct (String.string_dec x y)
    | [ H : context[opsign_dec        ?x ?y] |- _ ] => destruct (opsign_dec        x y)
    | [ H : context[Z_noteq_dec       ?x ?y] |- _ ] => destruct (Z_noteq_dec       x y)
    | [ H : context[parameter_dec     ?x ?y] |- _ ] => destruct (parameter_dec     x y)
    | [ H : context[parameters_dec    ?x ?y] |- _ ] => destruct (parameters_dec    x y)

    | [ H : context[if memberb _ _ _ then _ else _] |- _ ] => rewrite memberb_din in H
    | [ |- context[if memberb _ _ _ then _ else _] ] => rewrite memberb_din
  end.

Ltac boolvar := repeat boolvar_step.


Lemma fold_mk_prod {o} :
  forall (a : @NTerm o) v b,
    v = newvar b
    -> mk_product a v b = mk_prod a b.
Proof.
  introv e; subst; sp.
Qed.

Lemma fold_mk_fun {o} :
  forall (a : @NTerm o) v b,
    v = newvar b
    -> mk_function a v b = mk_fun a b.
Proof.
  introv e; subst; sp.
Qed.

Lemma fold_mk_ufun {o} :
  forall (a : @NTerm o) v b,
    v = newvar b
    -> mk_isect a v b = mk_ufun a b.
Proof.
  introv e; subst; sp.
Qed.

Lemma int_zero {o} :
  @mk_integer o 0 = mk_zero.
Proof. sp. Qed.

Definition absolute_value {o} (t : @NTerm o) :=
  mk_less t mk_zero (mk_minus t) t.

Ltac fold_terms_step :=
  match goal with
    | [ |- context[@oterm ?p (Can NAxiom) []] ] => fold (@mk_axiom p)
    | [ |- context[@oterm ?p (Can NInt) []] ] => fold (@mk_int p)
    | [ |- context[@oterm ?p (Can (NUTok ?a)) []] ] => fold (@mk_utoken p a)
    | [ |- context[@oterm ?p (Can (NTok ?a)) []] ] => fold (@mk_token p a)
    | [ |- context[@mk_approx ?p mk_axiom mk_axiom] ] => fold (@mk_true p)
    | [ |- context[@mk_approx ?p mk_axiom mk_bot] ] => fold (@mk_false p)
    | [ |- context[@mk_lam ?p nvarx (mk_var nvarx)] ] => fold (@mk_id p)
    | [ |- context[@mk_fix ?p mk_id] ] => fold (@mk_bottom p)
    | [ |- context[@mk_bottom ?p] ] => fold (@mk_bot p)
    | [ |- context[@bterm ?p [] ?x] ] => fold (@nobnd p x)
    | [ |- context[@vterm ?p ?v] ] => fold (@mk_var p v)
    | [ |- context[@oterm ?p (Can (Nint ?z)) []] ] => fold (@mk_integer p z)
    | [ |- context[@mk_integer ?p (Z.of_nat ?n)] ] => fold (@mk_nat p n)
    | [ |- context[@mk_nat ?p 0] ] => fold (@mk_zero p)
    | [ |- context[oterm (Can NLambda) [bterm [?v] ?t]] ] => fold (mk_lam v t)
    | [ |- context[oterm (Can NApprox) [nobnd ?a, nobnd ?b]] ] => fold (mk_approx a b)
    | [ |- context[oterm (Can NEquality) [nobnd ?a, nobnd ?b, nobnd ?c]] ] => fold (mk_equality a b c)
    | [ |- context[oterm (Can NREquality) [nobnd ?a, nobnd ?b, nobnd ?c]] ] => fold (mk_requality a b c)
    | [ |- context[oterm (Can NFreeFromAtom) [nobnd ?a, nobnd ?b, nobnd ?c]] ] => fold (mk_free_from_atom a b c)
    | [ |- context[oterm (Can NEFreeFromAtom) [nobnd ?a, nobnd ?b, nobnd ?c]] ] => fold (mk_efree_from_atom a b c)
    | [ |- context[oterm (Can NFreeFromAtoms) [nobnd ?a, nobnd ?b]] ] => fold (mk_free_from_atoms a b)
    | [ |- context[oterm (Can NFreeFromDefs) [nobnd ?a, nobnd ?b]] ] => fold (mk_free_from_defs a b)
    | [ |- context[oterm (Can NFunction) [nobnd ?a, bterm [?v] ?b]] ] => fold (mk_function a v b)
    | [ |- context[oterm (Can NProduct) [nobnd ?a, bterm [?v] ?b]] ] => fold (mk_product a v b)
    | [ |- context[oterm (Can NUnion) [nobnd ?x, nobnd ?y]] ] => fold (mk_union x y)
    | [ |- context[oterm (Can NEUnion) [nobnd ?x, nobnd ?y]] ] => fold (mk_eunion x y)
    | [ |- context[oterm (Can NTExc) [nobnd ?x, nobnd ?y]] ] => fold (mk_texc x y)
    | [ |- context[oterm (NCan NApply) [nobnd ?x, nobnd ?y]] ] => fold (mk_apply x y)
    | [ |- context[oterm (NCan NEApply) [nobnd ?x, nobnd ?y]] ] => fold (mk_eapply x y)
(*    | [ |- context[oterm (NCan (NApseq ?f)) [nobnd ?x] ] ] => fold (mk_apseq f x)*)
    | [ |- context[oterm (NCan NDecide) [nobnd ?d, bterm [?x] ?f, bterm [?y] ?g]] ] => fold (mk_decide d x f y g)
    | [ |- context[oterm (NCan NSpread) [nobnd ?p, bterm [?x,?y] ?f]] ] => fold (mk_spread p x y f)
    | [ |- context[oterm (NCan NTryCatch) [nobnd ?a, nobnd ?b, bterm [?v] ?c]] ] => fold (mk_try a b v c)
    | [ |- context[oterm (NCan NFix) [nobnd ?x]] ] => unfold nobnd; fold (mk_fix x); try (fold nobnd)
    | [ |- context[oterm (NCan NCbv) [nobnd ?a, bterm [?v] ?b]] ] => fold (mk_cbv a v b)
    | [ |- context[oterm (NCan NFresh) [bterm [?v] ?b]] ] => fold (mk_fresh v b)
    | [ |- context[oterm (NCan (NCompOp CompOpLess)) [nobnd ?a, nobnd ?b, nobnd ?c, nobnd ?d]] ] => fold (mk_less a b c d)
    | [ |- context[oterm Exc [nobnd ?a, nobnd ?x]] ] => fold (mk_exception a x)
    | [ |- context[oterm (Can NIsect) [nobnd ?a, bterm [?v] ?b] ] ] => fold (mk_isect a v b)
    | [ |- context[oterm (Can NSet) [nobnd ?a, bterm [?v] ?b] ] ] => fold (mk_set a v b)
    | [ |- context[oterm (NCan NMinus) [nobnd ?a] ] ] => fold (mk_minus a)
    | [ |- context[mk_equality ?t ?t ?T] ] => fold (mk_member t T)
    | [ |- context[mk_less ?t mk_zero (mk_minus ?t) ?t] ] => fold (absolute_value t)
    | [ |- context[mk_less ?a ?b mk_true mk_false] ] => fold (mk_less_than a b)
    | [ |- context[@mk_integer ?o 0] ] => rewrite (@int_zero o)
    | [ |- context[@mk_false ?o] ] => fold (@mk_void o)
    | [ |- context[mk_fun ?a mk_void] ] => fold (mk_not a)
    | [ |- context[mk_not (mk_less_than ?b ?a)] ] => fold (mk_le a b)

    | [ H : ?v = newvar ?b |- context[mk_product ?a ?v ?b] ] => rewrite (fold_mk_prod a v b H)
    | [ H : ?v = newvar ?b |- context[mk_function ?a ?v ?b] ] => rewrite (fold_mk_fun a v b H); auto
    | [ H : ?v = newvar ?b |- context[mk_isect ?a ?v ?b] ] => rewrite (fold_mk_ufun a v b H); auto

    | [ H : context[@oterm ?p (Can NAxiom) []] |- _ ] => fold (@mk_axiom p) in H
    | [ H : context[@oterm ?p (Can NInt) []] |- _ ] => fold (@mk_int p) in H
    | [ H : context[@oterm ?p (Can (NUTok ?a)) []] |- _ ] => fold (@mk_utoken p a) in H
    | [ H : context[@oterm ?p (Can (NTok ?a)) []] |- _ ] => fold (@mk_token p a) in H
    | [ H : context[@mk_approx ?p mk_axiom mk_axiom] |- _ ] => fold (@mk_true p) in H
    | [ H : context[@mk_approx ?p mk_axiom mk_bot] |- _ ] => fold (@mk_false p) in H
    | [ H : context[@mk_lam ?p nvarx (mk_var nvarx)] |- _ ] => fold (@mk_id p) in H
    | [ H : context[@mk_fix ?p mk_id] |- _ ] => fold (@mk_bottom p) in H
    | [ H : context[@mk_bottom ?p] |- _ ] => fold (@mk_bot p) in H
    | [ H : context[@bterm ?p [] ?x] |- _ ] => fold (@nobnd p x) in H
    | [ H : context[@vterm ?p ?v] |- _ ] => fold (@mk_var p v) in H
    | [ H : context[@oterm ?p (Can (Nint ?z)) []] |- _ ] => fold (@mk_integer p z) in H
    | [ H : context[@mk_integer ?p (Z.of_nat ?n)] |- _ ] => fold (@mk_nat p n) in H
    | [ H : context[@mk_nat ?p 0] |- _ ] => fold (@mk_zero p) in H
    | [ H : context[oterm (Can NLambda) [bterm [?v] ?t]] |- _ ] => fold (mk_lam v t) in H
    | [ H : context[oterm (Can NApprox) [nobnd ?a, nobnd ?b]] |- _ ] => fold (mk_approx a b) in H
    | [ H : context[oterm (Can NEquality) [nobnd ?a, nobnd ?b, nobnd ?c]] |- _ ] => fold (mk_equality a b c) in H
    | [ H : context[oterm (Can NREquality) [nobnd ?a, nobnd ?b, nobnd ?c]] |- _ ] => fold (mk_requality a b c) in H
    | [ H : context[oterm (Can NFreeFromAtom) [nobnd ?a, nobnd ?b, nobnd ?c]] |- _ ] => fold (mk_free_from_atom a b c) in H
    | [ H : context[oterm (Can NEFreeFromAtom) [nobnd ?a, nobnd ?b, nobnd ?c]] |- _ ] => fold (mk_efree_from_atom a b c) in H
    | [ H : context[oterm (Can NFreeFromAtoms) [nobnd ?a, nobnd ?b]] |- _ ] => fold (mk_free_from_atoms a b) in H
    | [ H : context[oterm (Can NFreeFromDefs) [nobnd ?a, nobnd ?b]] |- _ ] => fold (mk_free_from_defs a b) in H
    | [ H : context[oterm (Can NFunction) [nobnd ?a, bterm [?v] ?b]] |- _ ] => fold (mk_function a v b) in H
    | [ H : context[oterm (Can NProduct) [nobnd ?a, bterm [?v] ?b]] |- _ ] => fold (mk_product a v b) in H
    | [ H : context[oterm (Can NUnion) [nobnd ?x, nobnd ?y]] |- _ ] => fold (mk_union x y) in H
    | [ H : context[oterm (Can NEUnion) [nobnd ?x, nobnd ?y]] |- _ ] => fold (mk_eunion x y) in H
    | [ H : context[oterm (Can NTExc) [nobnd ?x, nobnd ?y]] |- _ ] => fold (mk_texc x y) in H
    | [ H : context[oterm (NCan NApply) [nobnd ?x, nobnd ?y]] |- _ ] => fold (mk_apply x y) in H
    | [ H : context[oterm (NCan NEApply) [nobnd ?x, nobnd ?y]] |- _ ] => fold (mk_eapply x y) in H
(*    | [ H : context[oterm (NCan (NApseq ?f)) [nobnd ?x] ] |- _ ] => fold (mk_apseq f x) in H*)
    | [ H : context[oterm (NCan NDecide) [nobnd ?d, bterm [?x] ?f, bterm [?y] ?g]] |- _ ] => fold (mk_decide d x f y g) in H
    | [ H : context[oterm (NCan NSpread) [nobnd ?p, bterm [?x,?y] ?f]] |- _ ] => fold (mk_spread p x y f) in H
    | [ H : context[oterm (NCan NTryCatch) [nobnd ?a, nobnd ?b, bterm [?v] ?c]] |- _ ] => fold (mk_try a b v c) in H
    | [ H : context[oterm (NCan NFix) [nobnd ?x]] |- _ ] => unfold nobnd in H; fold (mk_fix x) in H; try (fold nobnd in H)
    | [ H : context[oterm (NCan NCbv) [nobnd ?a, bterm [?v] ?b]] |- _ ] => fold (mk_cbv a v b) in H
    | [ H : context[oterm (NCan NFresh) [bterm [?v] ?b]] |- _ ] => fold (mk_fresh v b) in H
    | [ H : context[oterm (NCan (NCompOp CompOpLess)) [nobnd ?a, nobnd ?b, nobnd ?c, nobnd ?d]] |- _ ] => fold (mk_less a b c d) in H
    | [ H : context[oterm Exc [nobnd ?a, nobnd ?x]] |- _ ] => fold (mk_exception a x) in H
    | [ H : context[oterm (Can NIsect) [nobnd ?a, bterm [?v] ?b] ] |- _ ] => fold (mk_isect a v b) in H
    | [ H : context[oterm (Can NSet) [nobnd ?a, bterm [?v] ?b] ] |- _ ] => fold (mk_set a v b) in H
    | [ H : context[oterm (NCan NMinus) [nobnd ?a] ] |- _ ] => fold (mk_minus a) in H
    | [ H : context[mk_equality ?t ?t ?T] |- _ ] => fold (mk_member t T) in H
    | [ H : context[mk_less ?t mk_zero (mk_minus ?t) ?t] |- _ ] => fold (absolute_value t) in H
    | [ H : context[mk_less ?a ?b mk_true mk_false] |- _ ] => fold (mk_less_than a b) in H
    | [ H : context[@mk_integer ?o 0] |- _ ] => rewrite (@int_zero o) in H
    | [ H : context[@mk_false ?o] |- _ ] => fold (@mk_void o) in H
    | [ H : context[mk_fun ?a mk_void] |- _ ] => fold (mk_not a) in H
    | [ H : context[mk_not (mk_less_than ?b ?a)] |- _ ] => fold (mk_le a b) in H

    | [ H : ?v = newvar ?b, J : context[mk_product ?a ?v ?b] |- _ ] => rewrite (fold_mk_prod a v b H) in J; auto
    | [ H : ?v = newvar ?b, J : context[mk_function ?a ?v ?b] |- _ ] => rewrite (fold_mk_fun a v b H) in J; auto
    | [ H : ?v = newvar ?b, J : context[mk_isect ?a ?v ?b] |- _ ] => rewrite (fold_mk_ufun a v b H) in J; auto

  end.

Ltac fold_terms := repeat fold_terms_step.
