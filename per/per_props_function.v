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



Definition pair2lib_per {o}
           {lib A  B}
           (f : {lib' : library $ lib_extends lib' lib} -> per(o))
           (p : forall a, nuprl (projT1 a) A B (f a)): lib-per(lib,o).
Proof.
  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).

  introv.
  pose proof (p (exI(lib',e))) as a.
  pose proof (p (exI(lib',y))) as b.
  apply nuprl_refl in a.
  apply nuprl_refl in b.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

Lemma choice_ext_lib_teq {o} :
  forall lib (A B : @CTerm o),
    in_ext lib (fun lib' => tequality lib' A B)
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
  exists (pair2lib_per f C0); simpl.
  introv.
  pose proof (C0 (existT (fun lib' => lib_extends lib' lib) lib' e)) as C.
  simpl in *; auto.
Qed.

Definition pair_dep2lib_per {o}
           {lib : library}
           {eqa : lib-per(lib,o)}
           {v1 v2 B1 B2}
           (f : {lib' : library $ {ext : lib_extends lib' lib $ {a1, a2 : CTerm $ eqa lib' ext a1 a2}}} -> per(o))
           (p : forall a, nuprl (projT1 a) (B1)[[v1\\projT1(projT2(projT2 a))]] (B2)[[v2\\projT1(projT2(projT2(projT2 a)))]] (f a))
  : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).

  introv.
  pose proof (p (exI( lib', exI( e, exI( a, exI( b, p0)))))) as w.
  pose proof (p (exI( lib', exI( y, exI( a, exI( b, q)))))) as z.
  apply nuprl_refl in w.
  apply nuprl_refl in z.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

Lemma choice_ext_lib_teq_fam {o} :
  forall lib (A1 : @CTerm o) v1 B1 A2 v2 B2 (eqa : lib-per(lib,o)),
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

  exists (pair_dep2lib_per f C0); simpl.
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))) as C.
  simpl in *; auto.
Qed.

Hint Resolve computes_to_valc_refl : slow.

Lemma type_extensionality_per_func_ext_nuprl {o} :
  @type_extensionality o (per_func_ext nuprl).
Proof.
  introv per e.
  unfold per_func_ext in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_func_ext_nuprl : slow.

Lemma uniquely_valued_per_func_ext_nuprl {o} :
  @uniquely_valued o (per_func_ext nuprl).
Proof.
  introv pera perb.
  unfold per_func_ext in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd; spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_func_ext_eq.

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprl_refl in pera4.
    apply nuprl_refl in perb4.
    eapply nuprl_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v) as perb0.
    simpl in *.
    apply nuprl_refl in pera0.
    apply nuprl_refl in perb0.
    eapply nuprl_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_func_ext_nuprl : slow.

Lemma local_per_bar_per_func_ext_nuprl {o} :
  @local_ts o (per_bar (per_func_ext nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_func_ext_nuprl : slow.

Lemma dest_nuprl_per_func_l {o} :
  forall (ts : cts(o)) lib T A v B T' eq,
    ts = univ
    -> computes_to_valc lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_function {o} :
  forall (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprl lib (mkc_function A v B) (mkc_function C w D) eq
    -> per_bar (per_func_ext nuprl) lib (mkc_function A v B) (mkc_function C w D) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_func_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_approx2 {o} :
  forall lib (eq : per(o)) A v B C w D,
    nuprl lib (mkc_function A v B) (mkc_function C w D) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq bar (per_func_ext_eq_bar_lib_per lib eqa eqb)).
Proof.
  introv u.
  apply dest_nuprl_function in u.
  unfold per_bar in u; exrepnd.
  exists bar.

  (* We now have to get hold of [eqa] and [eqb]...
     Like I did in choice.choice_teqi? *)

XXXXXXX

  eapply eq_term_equals_trans;[eauto|].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_approx in *; exrepnd; spcast.
  computes_to_value_isvalue.
Qed.


(* This is basically 'functionEquality' *)
Lemma tequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib
              (mkc_function A1 v1 B1)
              (mkc_function A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # in_ext lib (fun lib' => forall a a', equality lib' a a' A1 -> tequality lib' (substc a v1 B1) (substc a' v2 B2))).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.


XXXXXXXX
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

(* !!MOVE to nuprl_mon *)
Definition type_monotone3 {o} (ts : cts(o)) :=
  forall lib T1 T2 eq,
    ts lib T1 T2 eq
    ->
    exists (eq' : lib-per(lib,o)),
    forall lib' (x : lib_extends lib' lib),
      ts lib' T1 T2 (eq' lib' x) # sub_per eq (eq' lib' x).

(* !!MOVE to nuprl_mon *)
Lemma type_monotone2_implies_type_monotone3 {o} :
  forall (ts : cts(o)), type_monotone2 ts -> type_monotone3 ts.
Proof.
  introv mon tsts.
  pose proof (mon lib) as mon.

  assert (forall (T1 T2 : CTerm) (eq : per(o)),
             ts lib T1 T2 eq
             ->
             forall (lib' : library),
               lib_extends lib' lib
               -> exists eq', ts lib' T1 T2 eq' # sub_per eq eq') as mon'.
  { introv h ext; eapply mon in h; eauto. }
  clear mon; rename mon' into mon.

  pose proof (mon T1 T2 eq) as mon; autodimp mon hyp.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun a b => ts (projT1 a) T1 T2 b # sub_per eq b)) as mon'.
  autodimp mon' hyp.
  { introv; exrepnd; simpl in *; auto. }

  clear mon; rename mon' into mon.
  exrepnd.

  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).
  introv.
  pose proof (mon0 (existT (fun lib' => lib_extends lib' lib) lib' x)) as mon.
  simpl in *; auto.
Qed.

Lemma choice_ext_lib_eq_fam {o} :
  forall lib (A A' : @CTerm o) v B eqa F1 F2,
    (forall lib' e, nuprl lib' A A' (eqa lib' e))
    -> (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> equality lib' (F1 a) (F2 a') (B)[[v\\a]])
    -> {eqb : lib-per-fam(lib,eqa,o),
              forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
                nuprl lib' (B)[[v\\a]] (B)[[v\\a]] (eqb lib' x a a' e)
                      # eqb lib' x a a' e (F1 a) (F2 a')}.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             equality lib' (F1 a) (F2 a') (B)[[v\\a]]) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A A' a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprl
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v B)
                              (substc (projT1 (projT2 (projT2 a))) v B)
                              b
                              # b (F1 (projT1 (projT2 (projT2 a))))
                                  (F2 (projT1 (projT2 (projT2 (projT2 a))))))) as C.
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

(* This is 'functionExtensionality' *)
Lemma implies_member_function {o} :
  forall lib (f : @CTerm o) g A v B,
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

  pose proof (@nuprl_monotone2 o) as mon.
  apply type_monotone2_implies_type_monotone3 in mon.
  pose proof (mon lib A A eqa ty0) as tya; exrepnd.
  rename eq' into eqa'.

  eapply choice_ext_lib_teq_fam in teq;[|apply tya0].
  exrepnd.

  eapply choice_ext_lib_eq_fam in eqap;[|apply tya0].
  exrepnd.
  rename eqb0 into eqb'.

  exists (per_func_ext_eq lib eqa' eqb).
  dands;[|].

  {
    apply CL_func.
    exists eqa' eqb.
    dands; auto;[].
    exists A A v v B B; dands; spcast; eauto 3 with slow;[].

    fold (@nuprl o) in *.
    introv; apply tya0.
  }

  introv.
  pose proof (eqap0 lib' e a a' e0) as q;repnd.
  pose proof (teq0 lib' e a a' e0) as h.
  apply nuprl_refl in h.
  eapply nuprl_uniquely_valued in h;[|exact q0].
  apply h; auto.
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
Lemma equality_in_function {o} :
  forall lib (f : @CTerm o) g A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> tequality lib' (substc a v B) (substc a' v B))
     # (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; sp_iff Case; introv e; try (complete (apply implies_member_function; sp));[].

  unfold equality in e; exrepnd.
  inversion e1; subst; try not_univ;[].

  one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
  allunfold_per; spcast; computes_to_eqval; allfold (@nuprl o).
  computes_to_value_isvalue; dands.

  { exists (eqa lib (lib_extends_refl lib)); sp. }

  {
    introv x e.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib' A1 (eqa lib' x) eq0); intro k; repeat (autodimp k hyp);[].
    rw <- k in e2.
    generalize (tsb lib' x a a' e2); intro n.
    exists (feqb lib' x a a' e2); sp.
  }

  {
    introv x e.
    apply eqt in e0.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib' A1 (eqa lib' x) eq0); intro k; repeat (dest_imp k hyp).
    rw <- k in e2.
    generalize (tsb lib' x a a' e2); intro n.
    exists (feqb lib' x a a' e2); sp; try (complete (allapply @nuprl_refl; sp)).
  }
Qed.

Lemma equality_in_function2 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib (mkc_function A v B)
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv.
  rw @equality_in_function; split; intro k; repnd; dands; try (complete sp).

  { unfold type; rw @tequality_function; sp. }

  { rw @tequality_function in k0; sp. }

  { rw @tequality_function in k0; sp. }
Qed.

Lemma inhabited_function {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_function A v B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib) a a', equality lib' a a' A -> tequality lib' (substc a v B) (substc a' v B))
     # {f : CTerm
        , forall lib' (x : lib_extends lib' lib) a a',
            equality lib' a a' A
            -> equality lib' (mkc_apply f a) (mkc_apply f a') (substc a v B)}).
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
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> tequality lib' (substc a v B) (substc a' v B)
             # equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; rw @equality_in_function; split; introv h; repnd;
    dands; tcsp; introv x e; eapply h; eauto.
Qed.

Lemma tequality_function_fun {p} :
  forall lib (A : @CTerm p) v B,
    (type lib (mkc_function A v (mk_cv [v] B)) {+} type lib (mkc_fun A B))
    -> tequality lib (mkc_function A v (mk_cv [v] B))
                 (mkc_fun A B).
Proof.
  introv o; repdors.

  { apply tequality_respects_alphaeqc_right with (T2 := mkc_function A v (mk_cv [v] B)); sp. }

  { apply tequality_respects_alphaeqc_left with (T1 := mkc_fun A B); sp.
    apply alphaeqc_sym; sp. }
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
    (tequality lib A1 A2
      # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A1 -> tequality lib' B1 B2)).
Proof.
  intros.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv x e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq lib' x t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp.

  - pose proof (teq lib' x) as teq.
    autodimp teq hyp.
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
     # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A -> type lib' B)
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') B)).
Proof.
  introv.
  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  split; intro k; repnd; dands; auto.

  {
    introv x i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 lib' x t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.
  }

  {
    introv x e.
    apply k in e; auto.
    repeat (rw @csubst_mk_cv in e); sp.
  }

  {
    introv x e.
    repeat (rw @csubst_mk_cv); sp.
    pose proof (k1 lib' x) as k1.
    autodimp k1 hyp.
    exists a; allapply @equality_refl; sp.
  }

  {
    introv x e.
    repeat (rw @csubst_mk_cv); sp.
  }
Qed.

Lemma tequality_mkc_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=> (tequality lib A1 A2
         # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A1 -> tequality lib' B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro k; repnd; dands; auto; introv x.

  {
    introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k lib' x t t i0); intro teq.
    allrw @csubst_mk_cv; auto.
  }

  {
    introv e.
    allrw @csubst_mk_cv; auto.
    apply equality_refl in e.
    pose proof (k lib' x) as k.
    autodimp k hyp.
    exists a; auto.
  }
Qed.

Lemma type_mkc_fun {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_fun A B) <=> (type lib A # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A -> type lib' B)).
Proof.
  introv.
  rw @tequality_mkc_fun; sp.
Qed.

Lemma choice_ext_teqi {o} :
  forall lib i (A A' : @CTerm o) v1 B1 v2 B2 (eqa : lib-per(lib,o)),
    (forall lib' e, nuprl lib' A A' (eqa lib' e))
    -> (forall lib' (x : lib_extends lib' lib) a1 a2,
           equality lib' a1 a2 A
           -> equality lib' (substc a1 v1 B1) (substc a2 v2 B2) (mkc_uni i))
    -> {eqb : lib-per-fam(lib,eqa,o),
         forall lib' (x : lib_extends lib' lib) a1 a2 (e : eqa lib' x a1 a2),
            nuprli i lib' (substc a1 v1 B1) (substc a2 v2 B2) (eqb lib' x a1 a2 e)}.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             equality lib' (B1)[[v1\\a]] (B2)[[v2\\a']] (mkc_uni i)) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A A' a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprli
                              i
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v1 B1)
                              (substc (projT1 (projT2 (projT2 (projT2 a)))) v2 B2)
                              b)) as C.
  autodimp C hyp.
  {
    introv; exrepnd; simpl in *.
    pose proof (F lib' ext a0 a1 a3) as G.
    unfold equality in G; exrepnd.
    inversion G1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli o j0).
    exists eqa0; sp.
  }
  clear F.
  exrepnd.

  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a1 (existT _ a2 e))))) as C.
  simpl in *; auto.
Qed.

Lemma equality_function {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_function A1 v1 B1)
      (mkc_function A2 v2 B2)
      (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # forall lib' (x : lib_extends lib' lib) a a',
         equality lib' a a' A1
         -> equality lib' (substc a v1 B1) (substc a' v2 B2) (mkc_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.

    dands.

    {
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      inversion teq1; subst; try not_univ;[].
      duniv j h.
      allrw @univi_exists_iff; exrepd.
      computes_to_value_isvalue; GC.
      discover; exrepnd.
      rename eqa into eqi.
      ioneclose; subst; try not_univ;[].

      one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
      computes_to_value_isvalue; GC.

      exists eq; sp.
      allrw.
      exists (eqa lib (lib_extends_refl lib)); sp.
    }

    {
      introv x ea.
      eapply equality_monotone in teq;[|eauto].

      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      inversion teq1; subst; try not_univ;[].
      duniv j h.
      allrw @univi_exists_iff; exrepd.
      computes_to_value_isvalue; GC.
      discover; exrepnd.
      rename eqa into eqi.
      ioneclose; subst; try not_univ;[].

      one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
      computes_to_value_isvalue; GC.

      exists eq; sp; try (complete (apply teq1'0));[].

      allfold (@nuprli o j0).
      allrw.
      unfold equality in ea; exrepnd.

      eapply nuprl_uniquely_valued in ea1;
        [|eapply nuprli_implies_nuprl;eapply nuprli_refl;eapply (tsa lib' (lib_extends_refl lib'))];[].
      apply ea1 in ea0.
      pose proof (tsb lib' (lib_extends_refl lib') a a' ea0) as n.
      exists (feqb lib' (lib_extends_refl lib') a a' ea0); sp.
    }

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli o j0).

    exists eq; sp.
    allrw.

    pose proof (@nuprli_monotone2 o j0) as mon.
    apply type_monotone2_implies_type_monotone3 in mon.
    pose proof (mon lib A1 A2 eqa h0) as tya; exrepnd.
    rename eq' into eqa'.

    eapply choice_ext_teqi in eqb;
      [|introv;eapply nuprli_implies_nuprl;apply (tya0 lib' e)].

    exrepnd.
    rename eqb0 into eqb'.

    exists (per_func_ext_eq lib eqa' eqb').
    apply CL_func.
    exists eqa' eqb'.
    dands; auto;[].
    exists A1 A2 v1 v2 B1 B2; dands; spcast; eauto 3 with slow;
      try (complete (introv; apply tya0)).
Qed.
