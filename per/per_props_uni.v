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


Require Export per_props_nat.


Lemma equality_in_uni {p} :
  forall lib a b i,
    @equality p lib a b (mkc_uni i)
    -> tequality lib a b.
Proof.
  unfold tequality, equality, nuprl; introv e; exrepnd.

  inversion e1; subst; try not_univ.
  duniv j h.
  induction j; allsimpl; sp.
  discover; exrepnd.
  exists eqa; sp.
  allapply @nuprli_implies_nuprl; auto.
Qed.

Lemma member_in_uni {p} :
  forall lib a i, @member p lib a (mkc_uni i) -> type lib a.
Proof.
  unfold member, type; introv e.
  apply equality_in_uni in e; sp.
Qed.

(* This is not provable, because in general we can't find the type level
 * of a type family. *)
Lemma equality_in_uni_iff {p} :
  forall lib a b,
    {i : nat , @equality p lib a b (mkc_uni i)}
    <=> tequality lib a b.
Proof.
  sp; split; introv e; exrepnd.
  apply equality_in_uni in e0; sp.

  allunfold @tequality; allunfold @equality; exrepnd.
  unfold nuprl in e0; sp.
  remember (univ lib) as T.
  generalize HeqT; clear HeqT.
  close_cases (induction e0 using @close_ind') Case; intros HeqT; subst.

  - Case "CL_init".
    duniv i h.
    exists i (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    unfold nuprl.
    apply CL_init; unfold univ.
    exists (S i); simpl; left; sp; try (spcast; computes_to_value_refl).
    exists eq; sp.

  - Case "CL_int".
    exists 1 (fun A A' => {eqa : per(p) , close lib (univi lib 1) A A' eqa}); sp.
    unfold nuprl, univ.
    apply CL_init.
    exists 2; left; sp; try (spcast; computes_to_value_refl).
    exists eq; apply CL_int.
    allunfold @per_int; sp.

  - Case "CL_atom".
    admit.

  - Case "CL_uatom".
    admit.

  - Case "CL_base".
    admit.

  - Case "CL_approx".
    admit.

  - Case "CL_cequiv".
    admit.

  - Case "CL_eq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_req".
    admit.

  - Case "CL_teq".
    admit.

  - Case "CL_isect".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_func".
    admit.

  - Case "CL_disect".
    admit.

  - Case "CL_pertype".
    admit.
(*Error: Universe inconsistency.*)
Abort.

Lemma computes_to_valc_tuni_implies {o} :
  forall lib (t : @CTerm o) v,
    computes_to_valc lib (mkc_tuni t) v
    -> {k : nat
        & computes_to_valc lib t (mkc_nat k)
        # v = mkc_uni k}.
Proof.
  introv comp.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd.
  unfold reduces_to in comp0; exrepnd.
  rename x0 into t.
  revert dependent t.
  induction k; introv isp r.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion comp; subst; allsimpl; tcsp.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; allsimpl.
    destruct t as [v|f|op bs]; allsimpl; ginv.
    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.
    + apply compute_step_tuni_success in r1; exrepnd; subst; GC; fold_terms.
      exists n; dands; eauto 3 with slow.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      apply cterm_eq; simpl; auto.
    + remember (compute_step lib (oterm (NCan ncan) bs)) as c; destruct c; allsimpl; ginv.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; eauto 3 with slow.
      apply IHk in r0; clear IHk; eauto 3 with slow; exrepnd.
      inversion r1; subst.
      exists k0; dands; eauto 3 with slow.
      eapply reduces_to_if_split2; eauto.
    + apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      inversion comp; subst; allsimpl; tcsp.
    + remember (compute_step lib (oterm (Abs abs) bs)) as c; destruct c; allsimpl; ginv.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; eauto 3 with slow.
      apply IHk in r0; clear IHk; eauto 3 with slow; exrepnd.
      inversion r1; subst.
      exists k0; dands; eauto 3 with slow.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma tequality_mkc_tuni {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_tuni a) (mkc_tuni b)
    <=> equality_of_nat lib a b.
Proof.
  introv.
  split; intro k.

  - unfold tequality in k; exrepnd.
    inversion k0; subst; try not_univ;
    try (complete (allunfold_per; computes_to_value_isvalue; allfold (@nuprl o);
                   allapply @computes_to_valc_tuni_implies; exrepnd; ginv;
                   match goal with [ H : _ |- _ ] => complete (eqconstr H) end)).
    clear k0.
    duniv j h.
    allrw @univi_exists_iff; exrepd; spcast.
    allapply @computes_to_valc_tuni_implies; exrepnd; ginv.
    exists k0; dands; spcast; auto.

  - unfold equality_of_nat in k; exrepnd; spcast.
    unfold tequality.
    pose proof (computes_to_valc_tuni lib a (Z.of_nat k0)) as c1.
    pose proof (computes_to_valc_tuni lib b (Z.of_nat k0)) as c2.
    allrw @Znat.Nat2Z.id; fold_terms.
    repeat (autodimp c1 hyp); try omega.
    repeat (autodimp c2 hyp); try omega.
    exists (fun A A' => (exists eqa, close lib (univi lib k0) A A' eqa)).
    apply CL_init.
    exists (S k0).
    left.
    dands; spcast; auto.
Qed.

Lemma mkc_uni_in_nuprl {p} :
  forall lib (i : nat),
    nuprl lib (mkc_uni i)
          (mkc_uni i)
          (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}).
Proof.
  introv.
  apply CL_init.
  exists (S i); simpl.
  left; sp; spcast; apply computes_to_valc_refl; sp.
Qed.

Lemma uni_in_uni {o} :
  forall lib i j, i < j -> @member o lib (mkc_uni i) (mkc_uni j).
Proof.
  introv h.
  unfold member, equality, nuprl.
  exists (fun A A' => {eqa : per , close lib (univi lib j) A A' eqa}).
  dands.

  { apply mkc_uni_in_nuprl. }

  {
    exists (fun A A' => {eqa : per , close lib (univi lib i) A A' eqa}).
    apply CL_init.
    apply univi_exists_iff.
    exists i; dands; spcast; tcsp; try (apply computes_to_valc_refl; eauto 3 with slow).
  }
Qed.

Lemma cumulativity {o} :
  forall lib i j (A B : @CTerm o),
    i < j
    -> equality lib A B (mkc_uni i)
    -> equality lib A B (mkc_uni j).
Proof.
  introv h equ.
  unfold member, equality, nuprl in *; destruct equ as [eqa equ]; repnd.
  exists (fun A A' => {eqa : per , close lib (univi lib j) A A' eqa}).
  dands.

  { apply mkc_uni_in_nuprl. }

  {
    dup equ0 as n.
    eapply nuprl_uniquely_valued in equ0;[|apply mkc_uni_in_nuprl].
    apply equ0 in equ; exrepnd; clear equ0.
    fold (nuprli lib i) in equ1.
    exists eqa0.
    fold (nuprli lib j).
    pose proof (typable_in_higher_univ lib i A B eqa0 equ1 (j - i)) as q.
    rewrite minus_plus_n in q; auto; try omega.
  }
Qed.


Lemma nuprl_mkc_uni {p} :
  forall lib (i : nat),
    {eq : per(p) , nuprl lib (mkc_uni i) (mkc_uni i) eq}.
Proof.
  intros.
  exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}).
  apply mkc_uni_in_nuprl.
Qed.

Lemma tequality_mkc_uni {p} :
  forall lib (i : nat), @tequality p lib (mkc_uni i) (mkc_uni i).
Proof.
  generalize (@nuprl_mkc_uni p); sp.
Qed.

Lemma equality_nuprli {p} :
  forall lib (A B C : @CTerm p) i eq,
    equality lib A B (mkc_uni i)
    -> nuprli lib i A C eq
    -> nuprli lib i A B eq.
Proof.
  introv e n.
  unfold equality, nuprl in e; exrepnd.
  inversion e1; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepnd.
  computes_to_value_isvalue; GC.
  discover; exrepnd.
  allfold (@nuprli p lib j0).
  generalize (nuprli_uniquely_valued lib j0 j0 A A eqa eq); intro k.
  repeat (autodimp k hyp).
  apply nuprli_refl in h2; auto.
  apply nuprli_refl in n; auto.
  apply (nuprli_ext lib j0 A B eqa eq); auto.
Qed.
