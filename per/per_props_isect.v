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



Lemma tequality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_isect A1 v1 B1)
              (mkc_isect A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    dands.

    unfold tequality.
    exists eqa; sp.

    introv e.
    unfold tequality.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp); try (complete (allapply @nuprl_refl; sp)).
    rw <- k in e0.
    generalize (tsb a a' e0); intro n.
    exists (feqb a a' e0); sp.

  - Case "<-".
    introv eqs.
    destruct eqs as [teqa teqb].
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)
                  t1 t2).
    apply CL_isect; fold (@nuprl p lib).
    unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).
Qed.

Lemma equality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_isect A1 v1 B1)
             (mkc_isect A2 v2 B2)
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
                  t1 t2).
    apply CL_isect; fold (@nuprli p lib j0).
    unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).
Qed.

Lemma equality_in_isect {p} :
  forall lib (t u : @CTerm p) A v B,
    equality lib t u (mkc_isect A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # (forall a a',
          equality lib a a' A
          -> equality lib t u (substc a v B))).
Proof.
  sp; sp_iff Case; introv e.

  - Case "->".
    unfold equality in e; exrepd.
    inversion n; subst; try not_univ.
    one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    dands.

    exists eqa; sp.

    introv ea.
    unfold equality in ea; exrepnd.
    assert (eq_term_equals eq0 eqa) as eqta
      by (apply (nuprl_uniquely_valued lib) with (t := A1); sp).
    unfold eq_term_equals in eqta.
    discover.
    generalize (tsb a a' h); sp.
    exists (feqb a a' h); sp.

    introv ea.
    unfold equality in ea; exrepnd.
    assert (eq_term_equals eq0 eqa) as eqta
      by (apply (nuprl_uniquely_valued lib) with (t := A1); sp).
    unfold eq_term_equals in eqta.
    discover.
    assert (eqa a a) as eqaa
      by (apply term_equality_refl with (t2 := a'); sp;
          try (complete (nts; apply nts_tes with (T := A1) (T' := A1); auto));
          try (complete (nts; apply nts_tet with (T := A1) (T' := A1); auto))).
    exists (feqb a a eqaa); sp.

  - Case "<-".
    repnd.
    unfold equality.
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_eq lib A v B (fun a => t) (fun a => u) e);
      intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality1 lib a1 a2 A eqa e e2)
                  t1 t2); sp.

    unfold nuprl; apply CL_isect; fold @nuprl; unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality1 lib a1 a2 A eqa e e2)); sp.

    unfold type_family.
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).

    generalize (n0 a a' (eq_equality1 lib a a' A eqa e0 e2)); intro n; repnd.

    generalize (choice_teq lib A v B v B e1); intro m; exrepnd.
    generalize (m0 a a' (eq_equality1 lib a a' A eqa e0 e2)); intro m.

    apply nuprl_trans with (t2 := substc a v B)
                             (eq2 := f0 a a' (eq_equality1 lib a a' A eqa e0 e2)); sp.

    generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e0 e2)); sp.
Qed.

Lemma tequality_mkc_ufun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_ufun A1 B1) (mkc_ufun A2 B2)
    <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_ufun.
  rw @tequality_isect.
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

Lemma equality_in_isect2 {o} :
  forall lib (t u : @CTerm o) A v B,
    equality lib t u (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (equality lib t u (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

Lemma member_in_isect {o} :
  forall lib (t : @CTerm o) A v B,
    member lib t (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (member lib t (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

Lemma equality_in_ufun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_ufun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (inhabited_type lib A -> equality lib f g B)).
Proof.
  introv.
  rw <- @fold_mkc_ufun.
  rw @equality_in_isect.
  split; intro k; repnd; dands; auto.

  - introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.

  - introv e.
    unfold inhabited_type in e; exrepnd.
    unfold member in e0.
    apply k in e0.
    repeat (rw @csubst_mk_cv in e0); sp.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp.
    exists a; apply equality_refl in e; auto.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    apply k.
    exists a; apply equality_refl in e; auto.
Qed.
