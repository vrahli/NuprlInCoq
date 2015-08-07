(*

  Copyright 2014 Cornell University

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


Require Export nuprl_type_sys.
Require Export univ_tacs.


(* ------ Here is another possible definition of the Nuprl type system ------ *)

(** In this nuprl2 type system, we know the universes of the types *)
Definition nuprl2 (T T' : CTerm) (eq : term-equality) :=
  {i : nat & nuprli i T T' eq}.

Lemma nuprl_implies_nuprl2 :
  forall T T' eq,
    nuprl T T' eq -> nuprl2 T T' eq.
Proof.
  introv n; unfold nuprl in n; unfold nuprl2.
  remember univ as u; revert Hequ.
  close_cases (induction n using close_ind') SCase; sp; subst.

  - SCase "CL_init".
    destruct X.
    exists x.
    apply CL_init; auto.

  - SCase "CL_int".
    destruct per; sp.
    exists 0.
    apply CL_int; unfold per_int; sp.

  - SCase "CL_base".
    destruct per; sp.
    exists 0.
    apply CL_base; unfold per_base; sp.

  - SCase "CL_sqle".
    destruct per; sp.
    exists 0.
    apply CL_sqle; unfold per_sqle; sp.
    exists x b c d; sp.

  - SCase "CL_sqeq".
    destruct per; sp.
    exists 0.
    apply CL_sqeq; unfold per_sqequal; sp.
    exists x b c d; sp.

  - SCase "CL_eq".
    exists i.
    apply CL_eq; unfold per_eq; sp.
    exists A B a1 a2 b1 b2 eqa; sp.

  - SCase "CL_isect".
Abort.

Lemma nuprl2_implies_nuprl :
  forall T T' eq,
    nuprl2 T T' eq -> nuprl T T' eq.
Proof.
  introv n; unfold nuprl2, nuprli in n; unfold nuprl; exrepnd.
  remember (univi i) as u; revert Hequ.
  close_cases (induction n0 using close_ind') SCase; sp; subst.

  - SCase "CL_init".
    apply CL_init.
    rw univi_iff_univ.
    exists i; sp.

  - SCase "CL_eq".
    apply CL_eq; unfold per_eq.
    exists A B a1 a2 b1 b2 eqa; sp.

  - SCase "CL_isect".
    apply CL_isect; unfold per_isect.
    exists eqa eqb; sp.
    unfold type_family.
    exists A A' v v' B B'; sp.

  - SCase "CL_func".
    apply CL_func; unfold per_func.
    exists eqa eqb; sp.
    unfold type_family.
    exists A A' v v' B B'; sp.

  - SCase "CL_disect".
    apply CL_disect; unfold per_disect.
    exists eqa eqb; sp.
    unfold type_family.
    exists A A' v v' B B'; sp.

  - SCase "CL_pertype".
    apply CL_pertype; unfold per_pertype.
    exists R1 R2 eq1 eq2; sp.
Qed.


(* ------ A few useful abstractions ------ *)

Definition tequality2 T1 T2 :=
  { eq : term-equality & nuprl2 T1 T2 eq }.

Definition type2 T := tequality2 T T.

Definition equality2 t1 t2 T :=
  { eq : term-equality & nuprl2 T T eq # eq t1 t2 }.

Definition member2 t T := equality2 t t T.


(* ------ We prove that nuprl2 is a type system ------ *)

Lemma nuprl2_type_system : type_system nuprl2.
Proof.
  unfold type_system, nuprl2; sp.

  - unfold uniquely_valued; sp.
    apply nuprli_uniquely_valued with (i1 := i0) (i2 := i) (T := T) (T' := T'); sp.

  - unfold type_extensionality; sp.
    exists i; sp.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p0 with (eq := eq); sp.

  - unfold type_symmetric; sp.
    exists i.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p1; sp.

  - unfold type_transitive; sp.
    generalize (nuprli_type_transitive i0 i T1 T2 T3 eq); intro k.
    repeat (dest_imp k hyp); exrepnd.
    exists i1; sp.

  - unfold type_value_respecting; sp.
    exists i.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p3; sp.

  - unfold term_symmetric; sp.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p4 with (T := T) (T' := T'); sp.

  - unfold term_transitive; sp.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p5 with (T := T) (T' := T'); sp.

  - unfold term_value_respecting; sp.
    generalize (nuprli_type_system i); intro ts; destruct ts; repnd.
    apply p with (T := T); sp.
Qed.

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac nts2 :=
  generalize nuprl2_type_system; intro nts;
  destruct nts as [ nts_uv nts ];
  destruct nts as [ nts_ext nts ];
  destruct nts as [ nts_tys nts ];
  destruct nts as [ nts_tyt nts ];
  destruct nts as [ nts_tyv nts ];
  destruct nts as [ nts_tes nts ];
  destruct nts as [ nts_tet nts_tev ].

Lemma nuprl2_refl :
  forall t1 t2 eq,
    nuprl2 t1 t2 eq -> nuprl2 t1 t1 eq.
Proof.
  intros.
  nts2.
  apply nts_tyt with (T2 := t2); sp.
Qed.

Lemma nuprl2_sym :
  forall t1 t2 eq,
    nuprl2 t1 t2 eq -> nuprl2 t2 t1 eq.
Proof.
  intros; nts2; sp.
Qed.

Lemma nuprl2_trans :
  forall t1 t2 t3 eq1 eq2,
    nuprl2 t1 t2 eq1 -> nuprl2 t2 t3 eq2 -> nuprl2 t1 t3 eq1.
Proof.
  intros; nts2.
  apply nts_tyt with (T2 := t2); sp.
  apply nts_ext with (eq := eq2); sp.
  apply uniquely_valued_eq with (ts := nuprl2) (T := t2) (T1 := t3) (T2 := t1); sp.
Qed.

Lemma nuprl2_uniquely_valued :
  forall t eq1 eq2,
    nuprl2 t t eq1
    -> nuprl2 t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  intros; nts2.
  apply nts_uv with (T := t) (T' := t); sp.
Qed.

Lemma nuprl2_value_respecting_left :
  forall t1 t2 t3 eq,
    nuprl2 t1 t2 eq
    -> cequivc t1 t3
    -> nuprl2 t3 t2 eq.
Proof.
  intros; nts2.
  apply nts_tyt with (T2 := t1); sp.
  apply nuprl2_sym.
  apply nts_tyv; sp.
  apply nuprl2_refl with (t2 := t2); sp.
Qed.

Lemma nuprl2_value_respecting_right :
  forall t1 t2 t3 eq,
    nuprl2 t1 t2 eq
    -> cequivc t2 t3
    -> nuprl2 t1 t3 eq.
Proof.
  intros; nts2.
  apply nts_tyt with (T2 := t2); sp.
  apply nts_tyv; sp.
  apply nuprl2_sym in X.
  apply nuprl2_refl in X; sp.
Qed.


(* ------ Properties ------ *)

Lemma equality_eq_n2 :
  forall A a b eq,
    nuprl2 A A eq
    -> (eq a b <=> equality2 a b A).
Proof.
  sp; split; sp.
  unfold equality2; exists eq; sp.
  unfold equality2 in X0; sp.
  assert (eq_term_equals eq eq0) as eqt.
  apply nuprl2_uniquely_valued with (t := A); sp.
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma equality_eq1_n2 :
  forall A B a b eq,
    nuprl2 A B eq
    -> (eq a b <=> equality2 a b A).
Proof.
  sp; split; sp.
  unfold equality2; exists eq; sp.
  apply nuprl2_refl in X; sp.
  unfold equality2 in X0; sp.
  assert (eq_term_equals eq eq0) as eqt.
  apply nuprl2_uniquely_valued with (t := A); sp.
  apply nuprl2_refl in X; sp.
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma eq_equality1_n2 :
  forall a b A eq,
    eq a b
    -> nuprl2 A A eq
    -> equality2 a b A.
Proof.
  sp.
  generalize (equality_eq_n2 A a b eq); sp.
  apply X1; sp.
Qed.

Lemma eq_equality2_n2 :
  forall a b A B eq,
    eq a b
    -> nuprl2 A B eq
    -> equality2 a b A.
Proof.
  sp.
  apply nuprl2_refl in X0.
  apply eq_equality1_n2 with (eq := eq); sp.
Qed.

Lemma tequality2_function :
  forall A1 A2 v1 v2 B1 B2,
    tequality2 (mkc_function A1 v1 B1)
               (mkc_function A2 v2 B2)
    <=>
    (tequality2 A1 A2
     # forall a a',
         equality2 a a' A1
         -> tequality2 (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality2, nuprl2 in teq; exrepd.
    inversion n; subst; try not_univ.
    inversion X; exrepd.
    inversion t; exrepd.
    computes_to_value_isvalue.
    unfold tequality2, nuprl2; sp.

    exists x; sp.
    exists i; sp.

    assert (x a a') as xa
      by (generalize (equality_eq1_n2 x0 A' a a' x); intro e;
          dest_imp e hyp;
          try (exists i; auto);
          apply e; auto).
    exists (eqb a a' xa); sp.
    allfold (nuprli i).
    exists i; sp.

  - Case "<-".
    sp.
    rename X0 into teqa; rename X into teqb.
    unfold tequality2 in teqa; sp.
    rename eq into eqa.
    exists (fun t t' : CTerm =>
              forall a a',
              forall e : eqa a a',
                (projT1 (teqb a a' (eq_equality2_n2 a a' A1 A2 eqa e n)))
                  (mkc_apply t a)
                  (mkc_apply t' a'));
      allsimpl; sp.
    unfold nuprl2 in n; sp.
    unfold nuprl2.
Abort.
