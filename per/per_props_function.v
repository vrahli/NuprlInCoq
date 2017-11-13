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
Require Export nuprl_mon.



Lemma choice_ext_lib_teq {o} :
  forall lib (A B : @CTerm o),
    (forall lib', lib_extends lib' lib -> tequality lib' A B)
    -> {eqa : lib-per(lib,o),
        forall lib' (e : lib_extends lib' lib), nuprl lib' A B (eqa lib' e) }.
Proof.
  introv F.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun a b => nuprl (projT1 a) A B b)) as C.
  autodimp C hyp.

  {
    unfold tequality in F.
    introv; exrepnd; simpl in *; auto.
  }

  exrepnd.

  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).
  introv.
  pose proof (C0 (existT (fun lib' => lib_extends lib' lib) lib' e)) as C.
  simpl in *; auto.
Qed.

Lemma choice_ext_lib_teq_fam {o} :
  forall lib (A1 : @CTerm o) v1 B1 A2 v2 B2 eqa,
    (forall lib' e, nuprl lib' A1 A2 (eqa lib' e))
    -> (forall lib',
           lib_extends lib' lib
           -> forall a a' : CTerm,
             equality lib' a a' A1
             -> exists eq, nuprl lib' (B1)[[v1\\a]] (B2)[[v2\\a']] eq)
    -> {eqb : lib-per-fam(lib,eqa,o),
              forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
                nuprl lib' (B1)[[v1\\a]] (B2)[[v2\\a']] (eqb lib' x a a' e) }.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             exists eq, nuprl lib' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']] eq) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A1 A2 a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprl
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v1 B1)
                              (substc (projT1 (projT2 (projT2 (projT2 a)))) v2 B2)
                              b)) as C.
  autodimp C hyp.
  {
    introv; exrepnd; simpl in *.
    eapply F; eauto.
  }

  clear F.
  exrepnd.

  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))) as C.
  simpl in *; auto.
Qed.

Hint Resolve computes_to_valc_refl : slow.


(* This is basically 'functionEquality' *)
Lemma tequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib
              (mkc_function A1 v1 B1)
              (mkc_function A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # forall lib' a a', lib_extends lib' lib -> equality lib' a a' A1 -> tequality lib' (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    rename_hyp_with @per_func_ext pera.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; dands.

    { exists (eqa lib (lib_extends_refl lib)); sp.
      apply i; eauto 3 with slow. }

    introv ext ea.
    assert (eqa lib' ext a a') as xa.
    {
      pose proof (equality_eq1 lib' A A' a a' (eqa lib' ext)) as x.
      repeat (autodimp x hyp); try (apply i; eauto 3 with slow).
      apply x; auto.
    }

    exists (eqb lib' ext a a' xa); sp.
    apply i0; eauto 3 with slow.

  - Case "<-".
    introv e; exrepnd.

    assert (forall lib', lib_extends lib' lib -> tequality lib' A1 A2) as teqa by eauto 3 with slow.
    clear e0.

    rename e into teqb.

    assert (forall (lib' : library) (e : lib_extends lib' lib) (a a' : CTerm),
               equality lib' a a' A1 -> tequality lib' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']]) as teqb' by tcsp.
    clear teqb; rename teqb' into teqb.
    unfold tequality in *.

    apply choice_ext_lib_teq in teqa; exrepnd.
    eapply choice_ext_lib_teq_fam in teqb;[|eauto]; exrepnd.

    exists (per_func_ext_eq lib eqa eqb).
    apply CL_func.
    exists eqa eqb.
    dands; eauto 3 with slow.
    exists A1 A2 v1 v2 B1 B2.
    dands; spcast; eauto 3 with slow.
Qed.

Lemma if_member_function {p} :
  forall lib (f : @CTerm p) A v B,
    member lib f (mkc_function A v B)
    ->
    forall lib' (x : lib_extends lib' lib) x y,
      equality lib' x y A
      -> equality lib' (mkc_apply f x) (mkc_apply f y) (substc x v B).
Proof.
  unfold member, equality, nuprl; introv m x e; exrepnd.
  inversion m1; subst; try not_univ.

  allunfold_per; spcast; computes_to_eqval.
  allfold (@nuprl p).
  computes_to_value_isvalue.

  assert (eq <=2=> (eqa lib' x)) as eqas.
  {
    pose proof (i lib' x) as i; simpl in i.
    eapply nuprl_uniquely_valued in i;[|exact e1]; auto.
  }
  dup e0 as w.
  apply eqas in w.

  exists (eqb lib' x x0 y w); dands; auto.

  {
    pose proof (i0 lib' x x0 y w) as i0; simpl in i0.
    eapply nuprl_refl; eauto.
  }

  apply e in m0; apply m0.
Qed.

(* This is 'functionExtensionality' *)
Lemma implies_member_function {p} :
  forall lib (f : @CTerm p) g A v B,
    type lib A
    -> (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> tequality lib' (substc a v B) (substc a' v B))
    -> (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))
    -> equality lib f g (mkc_function A v B).
Proof.
  introv ty teq eqap.
  unfold member, equality.
  unfold type, tequality in ty; exrepnd.
  rename eq into eqa.

  generalize (choice_eq lib A v B (fun a => mkc_apply f a) (fun a => mkc_apply g a) eqap);
    intro n; exrepnd.

  exists (fun t1 t2 =>
            forall a1 a2 : CTerm,
            forall e : eqa a1 a2,
              f0 a1
                 a2
                 (eq_equality1 lib a1 a2 A eqa e ty0)
                 (mkc_apply t1 a1)
                 (mkc_apply t2 a2)); sp.

  {
    unfold nuprl; apply CL_func; fold @nuprl; unfold per_func.
    exists eqa.

  exists (fun a1 a2 e => f0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.

  unfold type_family.
  exists A A v v B B; sp;
  try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

  generalize (n0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro n; repnd.

  generalize (choice_teq lib A v B v B teq); intro m; exrepnd.
  generalize (m0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro m.

  apply nuprl_trans with (t2 := substc a v B)
                           (eq2 := f1 a a' (eq_equality1 lib a a' A eqa e ty0)); sp.

  generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.
Qed.

(**

  As another example, we can prove that two terms [f] and [g] are
  equal in the function type [mkc_function A v B] if and only if [A]
  is a type, [B] is functional over [A], and forall [a] and [a'] equal
  in [A], [mkc_apply f a] and [mkc_apply g a'] are equals in [substc a
  v B].

  This is one of the lemmas where we need the [FunctionalChoice_on]
  axiom. Let us explain that issue.  Let us assume that we want to
  prove the left-hand-side of [<=>] from its right-hand-side.  To
  prove that [f] and [g] are equal in [mkc_function A v B], we have to
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
  forall lib (f : @CTerm p) g A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
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
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_function A1 v1 B1)
             (mkc_function A2 v2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # forall a a',
         equality lib a a' A1
         -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i)).
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
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                  (mkc_apply t1 a1) (mkc_apply t2 a2)).
    unfold nuprli.
    apply CL_func; fold (@nuprli p lib j0).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).
Qed.

Lemma equality_in_function2 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib (mkc_function A v B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv.
  rw @equality_in_function; split; intro k; repnd; dands; try (complete sp).

  unfold type; rw @tequality_function; sp.

  rw @tequality_function in k0; sp.

  rw @tequality_function in k0; sp.
Qed.

Lemma inhabited_function {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {f : CTerm
        , forall a a',
            equality lib a a' A
            -> equality lib (mkc_apply f a) (mkc_apply f a') (substc a v B)}).
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
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a',
          equality lib a a' A
          -> tequality lib (substc a v B) (substc a' v B)
             # equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; rw @equality_in_function; split; sp; discover; sp.
Qed.

Lemma tequality_function_fun {p} :
  forall lib (A : @CTerm p) v B,
    (type lib (mkc_function A v (mk_cv [v] B)) {+} type lib (mkc_fun A B))
    -> tequality lib (mkc_function A v (mk_cv [v] B))
                 (mkc_fun A B).
Proof.
  introv o; repdors.

  apply tequality_respects_alphaeqc_right with (T2 := mkc_function A v (mk_cv [v] B)); sp.

  apply tequality_respects_alphaeqc_left with (T1 := mkc_fun A B); sp.
  apply alphaeqc_sym; sp.
Qed.

Lemma tequality_mkc_fun_dom {p} :
  forall lib (A1 A2 B : @CTerm p),
    tequality lib A1 A2
    -> type lib (mkc_fun A1 B)
    -> tequality lib (mkc_fun A1 B) (mkc_fun A2 B).
Proof.
  introv teqa teqf.
  allrw <- @fold_mkc_fun.
  allrw @tequality_function; repnd; dands; auto.
Qed.

Lemma tequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=>
    (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  intros.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp.

  - autodimp teq hyp.
    exists a; allapply @equality_refl; sp.
    repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_mkc_fun_l {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    -> tequality lib A1 A2.
Proof.
  introv Hpart1.
  rw @tequality_fun in Hpart1; sp.
Qed.

Lemma equality_in_fun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_fun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') B)).
Proof.
  introv.
  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k1 t t); intro j; autodimp j hyp.
  repeat (rw @csubst_mk_cv in j); sp.

  introv e.
  apply k in e.
  repeat (rw @csubst_mk_cv in e); sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
  autodimp k1 hyp.
  exists a; allapply @equality_refl; sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_mkc_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
              <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @csubst_mk_cv; auto.

  introv e.
  allrw @csubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

Lemma type_mkc_fun {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_fun A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkc_fun; sp.
Qed.
