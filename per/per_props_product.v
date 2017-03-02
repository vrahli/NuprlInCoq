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


Require Export per_props.


Lemma equality_in_product {p} :
  forall lib (p1 p2 : @CTerm p) A v B,
    equality lib p1 p2 (mkc_product A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {a1, a2, b1, b2 : CTerm
        , p1 ===>(lib) (mkc_pair a1 b1)
        # p2 ===>(lib) (mkc_pair a2 b2)
        # equality lib a1 a2 A
        # equality lib b1 b2 (substc a1 v B)}).
Proof.
  introv; split; intro e; exrepnd.

  - unfold equality in e; exrepnd.
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

    rw eqt in e0.
    unfold per_product_eq in e0; exrepnd.
    exists a a' b b'; dands; auto.
    exists eqa; sp.
    exists (feqb a a' e); sp.
    generalize (tsb a a' e); intro n.
    allapply @nuprl_refl; sp.

  - unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_teq1 lib A eqa v B v B e6 e1);
      intro n; exrepnd.
    rename f into eqb.

    exists (per_product_eq lib eqa eqb).

    dands.

    apply CL_product; fold (@nuprl p lib); unfold per_product.
    exists eqa eqb.

    dands; sp.

    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).

    unfold equality in e5; exrepnd.
    generalize (nuprl_uniquely_valued lib A eq eqa); intro k; repeat (dest_imp k hyp).
    rw k in e0.

    exists a1 a2 b1 b2 e0; dands; auto.

    generalize (n0 a1 a2 e0); intro n1.
    unfold equality in e3; exrepnd.
    generalize (nuprl_uniquely_valued lib (substc a1 v B) eq0 (eqb a1 a2 e0)); intro j; repeat (dest_imp j hyp).
    allapply @nuprl_refl; auto.
    rw j in e7; auto.
Qed.

Lemma equality_in_prod {p} :
  forall lib (p1 p2 A B : @CTerm p),
    equality lib p1 p2 (mkc_prod A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # {a1, a2, b1, b2 : CTerm
        , p1 ===>(lib) (mkc_pair a1 b1)
        # p2 ===>(lib) (mkc_pair a2 b2)
        # equality lib a1 a2 A
        # equality lib b1 b2 B}).
Proof.
  introv.
  rw <- @fold_mkc_prod.
  rw @equality_in_product.
  split; intro k; exrepnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k1 t t); intro j; autodimp j hyp.
  repeat (rw @csubst_mk_cv in j); sp.

  exists a1 a2 b1 b2; dands; auto.
  allrw @csubst_mk_cv; sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
  autodimp k1 hyp.
  exists a; allapply @equality_refl; sp.

  exists a1 a2 b1 b2; dands; auto.
  repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_product A1 v1 B1)
              (mkc_product A2 v2 B2)
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
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; sp.

    exists eqa; sp.

    assert (eqa a a') as xa
      by (generalize (equality_eq1 lib A A' a a' eqa); intro h;
          dest_imp h hyp;
          try (exists i; auto);
          apply h; auto).
    exists (eqb a a' xa); sp.
    apply c2.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teqa; rename e into teqb.
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.
    applydup @nuprl_refl in teqa0.
    generalize (choice_teq1 lib A1 eqa v1 B1 v2 B2 teqa1 teqb); intro n; exrepnd.
    rename f into eqb.

    exists (per_product_eq lib eqa eqb).
    apply CL_product; fold @nuprl.
    unfold per_product.
    exists eqa eqb; dands; sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).
Qed.

Lemma tequality_mkc_prod {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_prod A1 B1) (mkc_prod A2 B2)
              <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_prod.
  rw @tequality_product.
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

Lemma type_mkc_prod {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_prod A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkc_prod; sp.
Qed.

Lemma equality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_product A1 v1 B1)
             (mkc_product A2 v2 B2)
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

    exists ( per_product_eq lib eqa 
                         (fun a1 a2 (e:eqa a1 a2) => 
                           f a1 a2 
                           (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                         )).
    unfold nuprli.
    apply CL_product; fold (@nuprli p lib j0).
    unfold per_product.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).
Qed.
