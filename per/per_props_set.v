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

Lemma tequality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_set A1 v1 B1)
              (mkc_set A2 v2 B2)
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
    allfold (@nuprl p).
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
              {e : eqa t1 t2
               , inhabited (f t1 t2 (eq_equality2 lib t1 t2 A1 A2 eqa e teqa0))}).
    apply CL_set; fold (@nuprl p lib).
    unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_set))).
Qed.

Lemma equality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_set A1 v1 B1)
             (mkc_set A2 v2 B2)
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
              {e : eqa t1 t2
               , inhabited (f t1 t2 (eq_equality3 lib t1 t2 A1 A2 eqa j0 e h0))}).
    apply CL_set; fold (@nuprli p lib j0).
    unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_set))).
Qed.

Lemma equality_in_set {p} :
  forall lib (t u : @CTerm p) A v B,
    equality lib t u (mkc_set A v B)
    <=>
    ((forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # equality lib t u A
     # inhabited_type lib (substc t v B)).
Proof.
  sp; sp_iff Case; introv e.

  - Case "->".
    unfold equality in e; exrepd.
    inversion n; subst; try not_univ.
    one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    dands.

    + introv ea.
      unfold equality in ea; exrepnd.
      assert (eq_term_equals eq0 eqa)
        as eqta by (eapply nuprl_uniquely_valued; eauto).
      unfold eq_term_equals in eqta.
      discover.
      generalize (tsb a a' h); sp.
      exists (feqb a a' h); sp.

    + exists eqa; dands; auto.
      rw eqt in e; exrepnd; auto.

    + rw eqt in e; exrepnd.
      eapply inhabited_type_if_inhabited; eauto.

  - Case "<-".
    repnd.
    unfold equality.
    unfold equality in e1; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A v B v B e0);
      intro n; exrepnd.
    rename f into eqb.

    exists (fun t1 t2 =>
              {e : eqa t1 t2
               , inhabited (eqb t1 t2 (eq_equality1 lib t1 t2 A eqa e e1))});
      dands; auto.

    unfold nuprl; apply CL_set; fold @nuprl; unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => eqb a1 a2 (eq_equality1 lib a1 a2 A eqa e e1)); sp.

    unfold type_family.
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_set))).

    generalize (n0 a a' (eq_equality1 lib a a' A eqa e3 e1)); intro n; repnd.

    generalize (choice_teq lib A v B v B e0); intro m; exrepnd.
    generalize (m0 a a' (eq_equality1 lib a a' A eqa e3 e1)); intro m; auto.

    exists e2.
    eapply inhabited_if_inhabited_type; eauto.
Qed.
