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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.



(* This is basically 'functionEquality' *)
Lemma tequality_function {p} :
  forall lib (A1 A2 : @cterm p) v1 v2 B1 B2,
    tequality lib
              (mkcn_function A1 v1 B1)
              (mkcn_function A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # forall a a', equality lib a a' A1 -> tequality lib (substcn a v1 B1) (substcn a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; sp.

    exists eqa; sp.

    assert (eqa a a') as xa
      by (generalize (equality_eq1 lib A A' a a' eqa); intro e;
          dest_imp e hyp;
          try (exists i; auto);
          apply e; auto).
    exists (eqb a a' xa); sp.
    apply c2.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teqa; rename e into teqb.
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.
    generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : cterm,
              forall e : eqa a1 a2,
                f a1
                  a2
                  (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)
                  (mkcn_apply t1 a1)
                  (mkcn_apply t2 a2)).
    apply CL_func; fold (@nuprl p lib).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valcn_refl; eauto 3 with slow)).
Qed.



Lemma if_member_function {p} :
  forall lib (f : @cterm p) A v B,
    member lib f (mkcn_function A v B)
    -> forall x y,
         equality lib x y A
         -> equality lib (mkcn_apply f x) (mkcn_apply f y) (substcn x v B).
Proof.
  unfold member, equality, nuprl; introv m e; exrepnd.
  inversion m1; subst; try not_univ.

  allunfold_per; spcast; computes_to_eqval.
  allfold (@nuprl p lib).
  computes_to_value_isvalue.
  discover.

  generalize (nuprl_uniquely_valued lib A0 eqa eq); intro k; repeat (dest_imp k hyp).
  rw <- k in e0.

  exists (eqb x y e0); sp.

  apply nuprl_refl with (t2 := substcn y v0 B0); sp.
Qed.

(* This is 'functionExtensionality' *)
Lemma implies_member_function {p} :
  forall lib (f : @cterm p) g A v B,
    type lib A
    -> (forall a a', equality lib a a' A -> tequality lib (substcn a v B) (substcn a' v B))
    -> (forall a a',
          equality lib a a' A
          -> equality lib (mkcn_apply f a) (mkcn_apply g a') (substcn a v B))
    -> equality lib f g (mkcn_function A v B).
Proof.
  introv ty teq eqap.
  unfold member, equality.
  unfold type, tequality in ty; exrepnd.
  rename eq into eqa.

  generalize (choice_eq lib A v B (fun a => mkcn_apply f a) (fun a => mkcn_apply g a) eqap);
    intro n; exrepnd.

  exists (fun t1 t2 =>
            forall a1 a2 : cterm,
            forall e : eqa a1 a2,
              f0 a1
                 a2
                 (eq_equality1 lib a1 a2 A eqa e ty0)
                 (mkcn_apply t1 a1)
                 (mkcn_apply t2 a2)); sp.

  unfold nuprl; apply CL_func; fold @nuprl; unfold per_func.
  exists eqa.

  exists (fun a1 a2 e => f0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.

  unfold type_family.
  exists A A v v B B; sp;
  try (complete (spcast; apply computes_to_valcn_refl; eauto 3 with slow)).

  generalize (n0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro n; repnd.

  generalize (choice_teq lib A v B v B teq); intro m; exrepnd.
  generalize (m0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro m.

  apply nuprl_trans with (t2 := substcn a v B)
                           (eq2 := f1 a a' (eq_equality1 lib a a' A eqa e ty0)); sp.

  generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.
Qed.

(**

  As another example, we can prove that two terms [f] and [g] are
  equal in the function type [mkcn_function A v B] if and only if [A]
  is a type, [B] is functional over [A], and forall [a] and [a'] equal
  in [A], [mkcn_apply f a] and [mkcn_apply g a'] are equals in [substc a
  v B].

  This is one of the lemmas where we need the [FunctionalChoice_on]
  axiom. Let us explain that issue.  Let us assume that we want to
  prove the left-hand-side of [<=>] from its right-hand-side.  To
  prove that [f] and [g] are equal in [mkcn_function A v B], we have to
  provide the equality of the function type, and in particular, we
  have to provide the equality of its co-domain.  We obtain that
  equality from the third clause in the right-hand-side of the [<=>].
  However, in our current [Prop] metatheory, that clause is (roughly)
  a [forall] of a propositional [exists].  From such a formula, we
  need to build a [per-fam] function (the equality of the co-domain),
  which is exactly what [FunctionalChoice_on] gives us.  This axiom is
  necessary because in general we cannot access the witness of a
  propositional existential.

 *)

(* This is the <=> verison of 'implies_member_function' *)
Lemma equality_in_function {p} :
  forall lib (f : @cterm p) g A v B,
    equality lib f g (mkcn_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substcn a v B) (substcn a' v B))
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkcn_apply f a) (mkcn_apply g a') (substcn a v B))).
Proof.
  introv; sp_iff Case; introv e; try (complete (apply implies_member_function; sp)).

  unfold equality in e; exrepnd.
  inversion e1; subst; try not_univ.

  one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
  allunfold_per; spcast; computes_to_eqval; allfold (@nuprl p lib).
  computes_to_value_isvalue; dands.

  exists eqa; sp.

  introv e.
  unfold equality in e; exrepnd.
  generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
  rw <- k in e2.
  generalize (tsb a a' e2); intro n.
  exists (feqb a a' e2); sp.

  introv e.
  discover.
  unfold equality in e; exrepnd.
  generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
  rw <- k in e2.
  generalize (tsb a a' e2); intro n.
  exists (feqb a a' e2); sp.
  allapply @nuprl_refl; sp.
Qed.

Lemma equality_function {p} :
  forall lib (A1 A2 : @cterm p) v1 v2 B1 B2 i,
    equality lib (mkcn_function A1 v1 B1)
             (mkcn_function A2 v2 B2)
             (mkcn_uni i)
    <=>
    (equality lib A1 A2 (mkcn_uni i)
     # forall a a',
         equality lib a a' A1
         -> equality lib (substcn a v1 B1) (substcn a' v2 B2) (mkcn_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality, nuprl in teq; exrepnd.
    inversion teq1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue; GC.
    dands.

    exists eq; sp.
    allrw.
    exists eqa; sp.

    introv e.
    exists eq; sp.
    allfold (@nuprli p lib j0).
    allrw.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp);
      try (complete (apply nuprli_implies_nuprl with (i := j0); sp;
                     allapply @nuprli_refl; sp)).
    rw <- k in e0.
    generalize (tsb a a' e0); intro n.
    exists (feqb a a' e0); sp.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : cterm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                  (mkcn_apply t1 a1) (mkcn_apply t2 a2)).
    unfold nuprli.
    apply CL_func; fold (@nuprli p lib j0).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valcn_refl; eauto 3 with slow)).
Qed.

Lemma equality_in_function2 {p} :
  forall lib (f g : @cterm p) A v B,
    equality lib f g (mkcn_function A v B)
    <=>
    (type lib (mkcn_function A v B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkcn_apply f a) (mkcn_apply g a') (substcn a v B))).
Proof.
  introv.
  rw @equality_in_function; split; intro k; repnd; dands; try (complete sp).

  unfold type; rw @tequality_function; sp.

  rw @tequality_function in k0; sp.

  rw @tequality_function in k0; sp.
Qed.

Lemma inhabited_function {p} :
  forall lib (A : @cterm p) v B,
    inhabited_type lib (mkcn_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substcn a v B) (substcn a' v B))
     # {f : cterm
        , forall a a',
            equality lib a a' A
            -> equality lib (mkcn_apply f a) (mkcn_apply f a') (substcn a v B)}).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_function in k0; repnd; dands; try (complete sp).
    exists t; sp.

  - exrepnd.
    exists f.
    rw @equality_in_function; sp.
Qed.

Lemma equality_in_function3 {p} :
  forall lib (f g : @cterm p) A v B,
    equality lib f g (mkcn_function A v B)
    <=>
    (type lib A
     # (forall a a',
          equality lib a a' A
          -> tequality lib (substcn a v B) (substcn a' v B)
             # equality lib (mkcn_apply f a) (mkcn_apply g a') (substcn a v B))).
Proof.
  introv; rw @equality_in_function; split; sp; discover; sp.
Qed.

Lemma tequality_function_fun {p} :
  forall lib (A : @cterm p) v B,
    (type lib (mkcn_function A v (mk_cvn [v] B)) {+} type lib (mkcn_fun A B))
    -> tequality lib (mkcn_function A v (mk_cvn [v] B))
                 (mkcn_fun A B).
Proof.
  introv o; repdors.

  apply tequality_respects_alphaeqcn_right with (T2 := mkcn_function A v (mk_cvn [v] B)); sp; eauto 3 with slow.

  apply tequality_respects_alphaeqcn_left with (T1 := mkcn_fun A B); sp.
  apply alphaeqcn_sym; sp; eauto 3 with slow.
Qed.

Lemma tequality_mkcn_fun_dom {p} :
  forall lib (A1 A2 B : @cterm p),
    tequality lib A1 A2
    -> type lib (mkcn_fun A1 B)
    -> tequality lib (mkcn_fun A1 B) (mkcn_fun A2 B).
Proof.
  introv teqa teqf.
  allrw <- @fold_mkcn_fun.
  allrw @tequality_function; repnd; dands; auto.
Qed.

Lemma tequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @cterm p),
    tequality lib (mkcn_fun A1 B1) (mkcn_fun A2 B2)
    <=>
    (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  intros.
  allrw <- @fold_mkcn_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq t t); intro k; autodimp k hyp.
    repeat (rw @cnsubst_mk_cv in k); sp.

  - autodimp teq hyp.
    exists a; allapply @equality_refl; sp.
    repeat (rw @cnsubst_mk_cv); sp.
Qed.

Lemma tequality_mkcn_fun_l {p} :
  forall lib (A1 A2 B1 B2 : @cterm p),
    tequality lib (mkcn_fun A1 B1) (mkcn_fun A2 B2)
    -> tequality lib A1 A2.
Proof.
  introv Hpart1.
  rw @tequality_fun in Hpart1; sp.
Qed.

Lemma equality_in_fun {p} :
  forall lib (f g A B : @cterm p),
    equality lib f g (mkcn_fun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkcn_apply f a) (mkcn_apply g a') B)).
Proof.
  introv.
  rw <- @fold_mkcn_fun.
  rw @equality_in_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k1 t t); intro j; autodimp j hyp.
  repeat (rw @cnsubst_mk_cv in j); sp.

  introv e.
  apply k in e.
  repeat (rw @cnsubst_mk_cv in e); sp.

  introv e.
  repeat (rw @cnsubst_mk_cv); sp.
  autodimp k1 hyp.
  exists a; allapply @equality_refl; sp.

  introv e.
  repeat (rw @cnsubst_mk_cv); sp.
Qed.

Lemma tequality_mkcn_fun {p} :
  forall lib (A1 A2 B1 B2 : @cterm p),
    tequality lib (mkcn_fun A1 B1) (mkcn_fun A2 B2)
              <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkcn_fun.
  rw @tequality_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @cnsubst_mk_cv; auto.

  introv e.
  allrw @cnsubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

Lemma type_mkcn_fun {p} :
  forall lib (A B : @cterm p),
    type lib (mkcn_fun A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkcn_fun; sp.
Qed.
