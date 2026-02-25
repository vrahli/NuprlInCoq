(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

 *)

Require Export per_props_atom.


Lemma tequality_free_from_atom {o} :
  forall lib (T1 T2 : @CTerm o) x1 x2 a1 a2,
    tequality
      lib
      (mkc_free_from_atom T1 x1 a1)
      (mkc_free_from_atom T2 x2 a2)
      <=> (tequality lib T1 T2
           # equality lib x1 x2 T1
           # equality lib a1 a2 mkc_uatom).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; dands; tcsp.

    + exists eqa; auto.

    + exists eqa; dands; auto.
      allapply @nuprl_refl; auto.

    + rw @equality_in_uatom_iff.
      exists u; dands; spcast; auto.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teq.
    rename e1 into eqx.
    rename e into equ.
    unfold tequality in teq; exrepnd.
    allrw @equality_in_uatom_iff; exrepnd; spcast.
    exists (per_ffatom_eq lib eq a x1).
    apply CL_ffatom.
    unfold per_ffatom.
    exists T1 T2 x1 x2 a1 a2 eq a.

    dands; spcast; auto;
    try (complete (spcast; apply computes_to_valc_refl;
                   try (apply iscvalue_mkc_free_from_atom))).
    eapply equality_eq1 in teq0; apply teq0; auto.
Qed.

Hint Resolve iscvalue_mkc_uatom : slow.

Lemma equality_free_from_atom_in_uni {o} :
  forall lib (T1 T2 : @CTerm o) x1 x2 a1 a2 i,
    equality
      lib
      (mkc_free_from_atom T1 x1 a1)
      (mkc_free_from_atom T2 x2 a2)
      (mkc_uni i)
      <=> (equality lib T1 T2 (mkc_uni i)
           # equality lib x1 x2 T1
           # equality lib a1 a2 mkc_uatom).
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

    unfold per_ffatom in *; exrepnd; spcast.
    computes_to_value_isvalue; GC.
    dands.

    {
      exists eq; sp.
      allrw.
      exists eqa; sp.
    }

    {
      exists eqa; sp.
      allfold (@nuprli o lib j0).
      apply nuprli_implies_nuprl with (i := j0); sp.
      allapply @nuprli_refl; sp.
    }

    {
      exists (equality_of_uatom lib).
      dands; auto.
      - apply CL_uatom; unfold per_uatom; dands; spcast; auto;
          apply computes_to_valc_refl; eauto 2 with slow.
      - exists u; dands; spcast; auto.
    }

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    destruct eqb as [eqb eqc].

    unfold equality in eqb; exrepnd.
    rename eq into eqT.
    apply equality_in_uatom_iff in eqc; exrepnd; spcast.

    unfold equality in eqa; exrepnd.
    rename eq into eqi.

    exists eqi; dands; auto.
    inversion eqa1; subst; try not_univ;[].
    duniv j h.
    allrw @univi_exists_iff; exrepd; spcast.
    computes_to_value_isvalue; GC.
    discover; exrepnd.

    allrw.
    exists (per_ffatom_eq lib eqT a x1).
    apply CL_ffatom.
    unfold per_ffatom.
    exists T1 T2 x1 x2 a1 a2 eqT a.

    dands; spcast; auto;
    try (complete (spcast; apply computes_to_valc_refl;
                   try (apply iscvalue_mkc_free_from_atom))).

    fold (nuprli lib j0) in *.
    applydup @nuprli_implies_nuprl in h0.
    pose proof (nuprl_uniquely_valued lib T1 eqT eqa) as q.
    repeat (autodimp q hyp);[eapply nuprl_refl; eauto|].
    eapply nuprli_ext;[exact h0|].
    apply eq_term_equals_sym; auto.
Qed.

Lemma tequality_free_from_atoms {o} :
  forall lib (T1 T2 : @CTerm o) x1 x2,
    tequality
      lib
      (mkc_free_from_atoms T1 x1)
      (mkc_free_from_atoms T2 x2)
      <=> (tequality lib T1 T2
           # equality lib x1 x2 T1).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; dands; tcsp.

    + exists eqa; auto.

    + exists eqa; dands; auto.
      allapply @nuprl_refl; auto.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teq.
    rename e into eqx.
    unfold tequality in teq; exrepnd.
    allrw @equality_in_uatom_iff; exrepnd; spcast.
    exists (per_ffatoms_eq lib eq x1).
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists T1 T2 x1 x2 eq.

    dands; spcast; auto;
    try (complete (spcast; apply computes_to_valc_refl;
                   try (apply iscvalue_mkc_free_from_atoms))).
    eapply equality_eq1 in teq0; apply teq0; auto.
Qed.

Definition name_not_in_upto_eq {o} lib (a x T : @CTerm o) :=
  {u : get_patom_set o
   , {y : CTerm
   , a ===>(lib) (mkc_utoken u)
   # equality lib x y T
   # !LIn u (getc_utokens y)}}.

Lemma name_not_in_utpo_iff_eq {o} :
  forall lib (A1 A2 : @CTerm o) eqa a x,
    nuprl lib A1 A2 eqa
    -> (name_not_in_upto lib a x eqa <=> name_not_in_upto_eq lib a x A1).
Proof.
  introv n.
  unfold name_not_in_upto.
  unfold name_not_in_upto_eq.
  split; intro h; exrepnd.

  - exists u y; dands; auto.
    eapply equality_eq1 in n; apply n; auto.

  - exists u y; dands; auto.
    eapply equality_eq1 in n; apply n; auto.
Qed.

Lemma tequality_efree_from_atom {o} :
  forall lib (T1 T2 : @CTerm o) x1 x2 a1 a2,
    tequality
      lib
      (mkc_efree_from_atom T1 x1 a1)
      (mkc_efree_from_atom T2 x2 a2)
      <=> (tequality lib T1 T2
           # (name_not_in_upto_eq lib a1 x1 T1 <=> name_not_in_upto_eq lib a2 x2 T2)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; dands; tcsp.

    + exists eqa; auto.

    + pose proof (name_not_in_utpo_iff_eq lib A1 A2 eqa a0 x0) as i1.
      autodimp i1 hyp.
      pose proof (name_not_in_utpo_iff_eq lib A2 A1 eqa a3 x3) as i2.
      autodimp i2 hyp.
      { apply nuprl_sym; auto. }
      rw <- i1; rw <- i2; auto.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teq.
    rename e into eqx.
    unfold tequality in teq; exrepnd.
    exists (per_effatom_eq lib eq a1 x1).
    apply CL_effatom.
    unfold per_effatom.
    exists T1 T2 x1 x2 a1 a2 eq.

    dands; spcast; auto;
    try (complete (spcast; apply computes_to_valc_refl;
                   try (apply iscvalue_mkc_efree_from_atom))).
    pose proof (name_not_in_utpo_iff_eq lib T1 T2 eq a1 x1) as i1.
    autodimp i1 hyp.
    pose proof (name_not_in_utpo_iff_eq lib T2 T1 eq a2 x2) as i2.
    autodimp i2 hyp.
    { apply nuprl_sym; auto. }
    rw i1; rw i2; auto.
Qed.

Lemma equality_in_free_from_atom {o} :
  forall lib (t1 t2 T t a : @CTerm o),
    equality lib t1 t2 (mkc_free_from_atom T t a)
    <=> {y : CTerm
         , {u : get_patom_set o
         , t1 ===>(lib) mkc_axiom
         # t2 ===>(lib) mkc_axiom
         # a ===>(lib) (mkc_utoken u)
         # type lib T
         # equality lib t y T
         # !LIn u (getc_utokens y)}}.
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv equ.
    unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    match goal with
      | [ H : per_ffatom _ _ _ _ _ |- _ ] => rename H into h
    end.
    unfold per_ffatom in h; exrepnd; spcast.
    allfold (@nuprl o lib).
    computes_to_value_isvalue.
    apply h1 in equ0.
    unfold per_ffatom_eq in equ0; exrepnd.
    exists y u; dands; spcast; auto.

    + exists eqa; auto.

    + eapply equality_eq in h3; apply h3; auto.

  - Case "<-".
    introv equ; repnd; spcast.
    unfold member, equality in equ; exrepnd; spcast.

    exists (per_ffatom_eq lib eq u t).
    dands.

    + apply CL_ffatom.
      exists T T t t a a eq u; dands; auto; spcast; auto;
      try (apply computes_to_valc_refl; try (apply iscvalue_mkc_free_from_atom)).
      eapply equality_eq_refl; eauto.

    + unfold per_ffatom_eq; dands; spcast; auto.
      exists y.
      dands; auto.
Qed.

Lemma equality_in_free_from_atoms {o} :
  forall lib (a b T t : @CTerm o),
    equality lib a b (mkc_free_from_atoms T t)
    <=> {u : CTerm
         , a ===>(lib) mkc_axiom
         # b ===>(lib) mkc_axiom
         # type lib T
         # equality lib t u T
         # noutokensc u}.
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv equ.
    unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    match goal with
      | [ H : per_ffatoms _ _ _ _ _ |- _ ] => rename H into h
    end.
    unfold per_ffatoms in h; exrepnd; spcast.
    allfold (@nuprl o lib).
    computes_to_value_isvalue.
    apply h0 in equ0.
    unfold per_ffatoms_eq in equ0; exrepnd.
    exists y; dands; auto.

    + exists eqa; auto.

    + eapply equality_eq in h3; apply h3; auto.

  - Case "<-".
    introv equ; repnd; spcast.
    unfold member, equality in equ; exrepnd.

    exists (per_ffatoms_eq lib eq t).
    dands.

    + apply CL_ffatoms.
      exists T T t t eq; dands; auto; spcast;
      try (apply computes_to_valc_refl; try (apply iscvalue_mkc_free_from_atoms)).
      eapply equality_eq_refl; eauto.

    + unfold per_ffatoms_eq; dands; spcast; auto.
      exists u.
      dands; auto.
Qed.

Lemma inhabited_free_from_atoms {o} :
  forall lib (T t : @CTerm o),
    inhabited_type lib (mkc_free_from_atoms T t)
    <=> {u : CTerm
         , type lib T
         # equality lib t u T
         # noutokensc u}.
Proof.
  introv.
  unfold inhabited_type.
  sp_iff Case; introv h; exrepnd.
  - apply equality_in_free_from_atoms in h0; exrepnd.
    exists u; dands; auto.
  - exists (@mkc_axiom o).
    apply equality_in_free_from_atoms.
    exists u; dands; spcast; auto;
    try (apply computes_to_valc_refl; try (apply iscvalue_mkc_axiom)).
Qed.

Lemma equality_in_efree_from_atom {o} :
  forall lib (t1 t2 T t a : @CTerm o),
    equality lib t1 t2 (mkc_efree_from_atom T t a)
    <=> {y : CTerm
         , {u : get_patom_set o
         , t1 ===>(lib) mkc_axiom
         # t2 ===>(lib) mkc_axiom
         # a ===>(lib) (mkc_utoken u)
         # type lib T
         # equality lib t y T
         # !LIn u (getc_utokens y)}}.
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv equ.
    unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    match goal with
      | [ H : per_effatom _ _ _ _ _ |- _ ] => rename H into h
    end.
    unfold per_effatom in h; exrepnd; spcast.
    allfold (@nuprl o lib).
    computes_to_value_isvalue.
    apply h0 in equ0.
    unfold per_effatom_eq in equ0; exrepnd.
    allunfold @name_not_in_upto; exrepnd.
    exists y u; dands; spcast; auto.

    + exists eqa; auto.

    + eapply equality_eq in h3; apply h3; auto.

  - Case "<-".
    introv equ; repnd; spcast.
    unfold member, equality in equ; exrepnd; spcast.

    exists (per_effatom_eq lib eq a t).
    dands.

    + apply CL_effatom.
      exists T T t t a a eq; dands; auto; spcast; auto;
      try (apply computes_to_valc_refl; try (apply iscvalue_mkc_efree_from_atom)); tcsp.

    + unfold per_effatom_eq; dands; spcast; auto.
      exists u y.
      dands; spcast; auto.
Qed.
