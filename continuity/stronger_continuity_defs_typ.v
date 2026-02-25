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

Require Export Coq.Logic.ConstructiveEpsilon.
Require Export stronger_continuity_defs.
Require Export stronger_continuity_defs0.
Require Export per_props_atom.
Require Export terms5.
Require Export per_props_nat2.


Lemma equality_mkc_union_tnat_unit {o} :
  forall lib (a b : @CTerm o),
    equality lib a b (mkc_union mkc_tnat mkc_unit)
    <=>
    ({k : nat
      , ccequivc lib a (mkc_inl (mkc_nat k))
      # ccequivc lib b (mkc_inl (mkc_nat k))}
     {+}
     (ccequivc lib a (mkc_inr mkc_axiom)
      # ccequivc lib b (mkc_inr mkc_axiom))).
Proof.
  introv.
  rw @equality_mkc_union.
  split; intro k; exrepnd; repndors; exrepnd; spcast; dands; eauto 3 with slow.

  - allrw @equality_in_tnat.
    allunfold @equality_of_nat; exrepnd; spcast.
    left.
    exists k; dands; spcast.
    + eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; exact k2|].
      apply cequivc_mkc_inl_if.
      apply computes_to_valc_implies_cequivc; auto.
    + eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; exact k4|].
      apply cequivc_mkc_inl_if.
      apply computes_to_valc_implies_cequivc; auto.

  - allrw @equality_in_unit; repnd; spcast.
    right; dands; spcast.
    + eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; exact k2|].
      apply cequivc_mkc_inr_if.
      apply computes_to_valc_implies_cequivc; auto.
    + eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; exact k4|].
      apply cequivc_mkc_inr_if.
      apply computes_to_valc_implies_cequivc; auto.

  - left.
    apply cequivc_sym in k2; apply cequivc_mkc_inl_implies in k2.
    apply cequivc_sym in k1; apply cequivc_mkc_inl_implies in k1.
    exrepnd.
    exists b1 b0; dands; spcast; auto.
    eapply equality_respects_cequivc_left;[exact k4|].
    eapply equality_respects_cequivc_right;[exact k3|].
    apply equality_in_tnat.
    unfold equality_of_nat.
    exists k0; dands; spcast; auto;
    apply computes_to_valc_refl; eauto 3 with slow.

  - right.
    apply cequivc_sym in k0; apply cequivc_mkc_inr_implies in k0.
    apply cequivc_sym in k; apply cequivc_mkc_inr_implies in k.
    exrepnd.
    exists b1 b0; dands; spcast; auto.
    eapply equality_respects_cequivc_left;[exact k3|].
    eapply equality_respects_cequivc_right;[exact k1|].
    apply equality_in_unit.
    dands; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma equality_in_mkc_texc {o} :
  forall lib (a b N E : @CTerm o),
    equality lib a b (mkc_texc N E)
    <=> {n1 : CTerm
         , {n2 : CTerm
         , {e1 : CTerm
         , {e2 : CTerm
         , a ===e>(lib,n1) e1
         # b ===e>(lib,n2) e2
         # equality lib n1 n2 N
         # equality lib e1 e2 E }}}}.
Proof.
  introv.
  split; introv k; exrepnd; spcast.

  - unfold equality in k; exrepnd.
    inversion k1; subst; try not_univ.
    clear k1.
    match goal with
      | [ H : per_texc _ _ _ _ _ |- _ ] => rename H into p
    end.
    allunfold @per_texc; exrepnd; spcast; computes_to_value_isvalue.
    apply p1 in k0.
    unfold per_texc_eq in k0; exrepnd; spcast.
    exists n1 n2 e1 e2; dands; spcast; auto.

    + eapply eq_equality1; eauto.

    + eapply eq_equality1; eauto.

  - allunfold @equality; exrepnd.
    rename eq0 into eqn.
    rename eq into eqe.
    exists (per_texc_eq lib eqn eqe).
    dands; auto.

    + apply CL_texc.
      unfold per_texc.
      exists eqn eqe N N E E.
      dands; spcast; auto;
      try (apply computes_to_valc_refl; apply iscvalue_mkc_texc).

    + unfold per_texc_eq.
      exists n1 n2 e1 e2; dands; spcast; auto.
Qed.

Lemma tequality_mkc_texc {o} :
  forall lib (N1 E1 N2 E2 : @CTerm o),
    tequality lib (mkc_texc N1 E1) (mkc_texc N2 E2)
    <=> (tequality lib N1 N2 # tequality lib E1 E2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    inversion teq0; try not_univ; allunfold @per_texc; exrepnd.
    computes_to_value_isvalue; sp; try (complete (spcast; sp)).
    + exists eqn; sp.
    + exists eqe; sp.

  - unfold tequality in teq0; exrepnd.
    rename eq into eqn.
    unfold tequality in teq; exrepnd.
    rename eq into eqe.
    exists (per_texc_eq lib eqn eqe); apply CL_texc; unfold per_texc.
    exists eqn eqe N1 N2 E1 E2; sp; spcast;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_texc).
Qed.

Lemma disjoint_nat_exc {o} :
  forall lib (a b : @CTerm o),
    disjoint_types lib mkc_tnat (mkc_texc a b).
Proof.
  introv mem; repnd.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_mkc_texc; exrepnd; spcast.
  eapply computes_to_valc_and_excc_false in mem0; eauto.
Qed.

Lemma tequality_mkc_singleton_uatom {o} :
  forall lib (n1 n2 : @get_patom_set o),
    tequality lib (mkc_singleton_uatom n1) (mkc_singleton_uatom n2)
    <=> n1 = n2.
Proof.
  introv.
  unfold mkc_singleton_uatom.
  rw @tequality_set; split; introv k; repnd; subst; tcsp.

  - clear k0.
    pose proof (k (mkc_utoken n1) (mkc_utoken n1)) as h; clear k.
    autodimp h hyp.
    { apply equality_in_uatom_iff.
      exists n1; dands; spcast;
      try (apply computes_to_valc_refl; apply iscvalue_mkc_utoken). }
    allrw @mkcv_cequiv_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_utoken_substc.
    allrw @tequality_mkc_cequiv.
    destruct h as [h h2]; clear h2.
    autodimp h hyp; spcast; eauto 3 with slow.
    allrw @cequivc_mkc_utoken; auto.

  - dands;[apply tequality_uatom|].
    introv e.
    apply equality_in_uatom_iff in e; exrepnd; spcast.
    allrw @mkcv_cequiv_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_utoken_substc.
    allrw @tequality_mkc_cequiv.
    allapply @computes_to_valc_implies_cequivc.
    split; intro k; spcast.
    + eapply cequivc_trans in k;[|apply cequivc_sym;exact e1].
      allrw @cequivc_mkc_utoken; subst; auto.
    + eapply cequivc_trans in k;[|apply cequivc_sym;exact e0].
      allrw @cequivc_mkc_utoken; subst; auto.
Qed.

Lemma tequality_mkc_ntexc {o} :
  forall lib n1 n2 (E1 E2 : @CTerm o),
    tequality lib (mkc_ntexc n1 E1) (mkc_ntexc n2 E2)
    <=> (n1 = n2 # tequality lib E1 E2).
Proof.
  introv.
  unfold mkc_ntexc.
  rw @tequality_mkc_texc.
  rw @tequality_mkc_singleton_uatom; tcsp.
Qed.

Lemma type_mkc_ntexc {o} :
  forall lib n (E : @CTerm o),
    type lib (mkc_ntexc n E) <=> (type lib E).
Proof.
  introv.
  rw @tequality_mkc_ntexc; split; sp.
Qed.

Lemma inhabited_type_mkc_cequiv {o} :
  forall lib (t1 t2 : @CTerm o),
    inhabited_type lib (mkc_cequiv t1 t2) <=> ccequivc lib t1 t2.
Proof.
  introv.
  unfold inhabited_type; split; introv k; exrepnd.

  - allunfold @member; allunfold @equality; allunfold @nuprl; exrepnd.
    inversion k0; subst; try not_univ.

    allunfold @per_cequiv; sp.
    uncast; computes_to_value_isvalue.
    discover; sp.

  - exists (@mkc_axiom o).
    apply member_cequiv_iff; auto.
Qed.

Lemma equality_in_mkc_singleton_uatom {o} :
  forall lib a b (n : @get_patom_set o),
    equality lib a b (mkc_singleton_uatom n)
    <=> (a ===>(lib) (mkc_utoken n) # b ===>(lib) (mkc_utoken n)).
Proof.
  introv.
  unfold mkc_singleton_uatom.
  rw @equality_in_set.
  allrw @mkcv_cequiv_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_utoken_substc.
  allrw @inhabited_type_mkc_cequiv.
  allrw @equality_in_uatom_iff.
  split; intro k; exrepnd; spcast; dands; tcsp.

  - eapply close_type_sys_per_ffatom.cequivc_utoken in k;[|exact k1].
    apply computes_to_valc_isvalue_eq in k; try (eqconstr k); eauto 3 with slow.
    dands; spcast; auto.

  - eapply close_type_sys_per_ffatom.cequivc_utoken in k;[|exact k1].
    apply computes_to_valc_isvalue_eq in k; try (eqconstr k); eauto 3 with slow.
    dands; spcast; auto.

  - introv e.
    allrw @mkcv_cequiv_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_utoken_substc.
    allrw @equality_in_uatom_iff; exrepnd; spcast.
    apply tequality_mkc_cequiv.
    allapply @computes_to_valc_implies_cequivc.
    split; intro h; spcast.
    + eapply cequivc_trans in h;[|apply cequivc_sym;exact e1].
      allrw @cequivc_mkc_utoken; subst; auto.
    + eapply cequivc_trans in h;[|apply cequivc_sym;exact e0].
      allrw @cequivc_mkc_utoken; subst; auto.

  - exists n; dands; spcast; auto.

  - spcast.
    allapply @computes_to_valc_implies_cequivc; auto.
Qed.

Lemma equality_in_mkc_ntexc {o} :
  forall lib n (a b E : @CTerm o),
    equality lib a b (mkc_ntexc n E)
    <=> {n1 : CTerm
         , {n2 : CTerm
         , {e1 : CTerm
         , {e2 : CTerm
         , n1 ===>(lib) (mkc_utoken n)
         # n2 ===>(lib) (mkc_utoken n)
         # a ===e>(lib,n1) e1
         # b ===e>(lib,n2) e2
         # equality lib e1 e2 E }}}}.
Proof.
  introv.
  rw @equality_in_mkc_texc; split; intro k; exrepnd; spcast.

  - allrw @equality_in_mkc_singleton_uatom; repnd; spcast.
    exists n1 n2 e1 e2; dands; spcast; auto.

  - exists n1 n2 e1 e2; dands; spcast; auto.
    allrw @equality_in_mkc_singleton_uatom; dands; spcast; auto.
Qed.

Lemma equality_in_natE {o} :
  forall lib n (a b : @CTerm o),
    equality lib a b (natE n)
    <=> (equality_of_nat lib a b
         {+} (ccequivc lib a (spexcc n) # ccequivc lib b (spexcc n))).
Proof.
  introv.
  unfold natE, with_nexc_c.

  pose proof (equality_in_disjoint_bunion lib a b mkc_tnat (mkc_ntexc n mkc_unit)) as h.
  autodimp h hyp.
  { unfold mkc_ntexc; apply disjoint_nat_exc. }
  rw h; clear h.
  rw @type_mkc_ntexc.

  split; intro k; repnd; dands; eauto 3 with slow; repndors; tcsp;
  allrw @equality_in_tnat;
  allrw @equality_in_mkc_ntexc;
  exrepnd; spcast; tcsp;
  allrw @equality_in_unit;
  repnd; spcast.

  - allapply @computes_to_excc_implies_cequivc.
    allapply @computes_to_valc_implies_cequivc.
    right; dands; spcast.
    + eapply cequivc_trans;[exact k5|].
      apply continuity_defs_ceq.cequivc_mkc_exception; auto.
    + eapply cequivc_trans;[exact k6|].
      unfold spexc.
      apply continuity_defs_ceq.cequivc_mkc_exception; auto.

  - left; allrw @equality_in_tnat; auto.

  - right; allrw @equality_in_mkc_ntexc.
    allunfold @spexc.
    apply cequivc_sym in k0; apply cequivc_sym in k.
    apply cequivc_exception_implies in k0.
    apply cequivc_exception_implies in k.
    exrepnd.
    allapply @cequivc_axiom_implies.
    allapply @cequivc_utoken_implies.
    exists x0 x c0 c; dands; spcast; auto.
    allrw @equality_in_unit; dands; spcast; auto.
Qed.

Lemma dec_reduces_ksteps_excc {o} :
  forall lib k (t v : @CTerm o),
    (forall x, decidable (x = get_cterm v))
    -> decidable (reduces_ksteps_excc lib t v k).
Proof.
  introv d.
  destruct_cterms; allsimpl.
  pose proof (dec_reduces_in_atmost_k_steps_exc lib k x0 x d) as h.
  destruct h as [h|h];[left|right].
  - spcast; tcsp.
  - intro r; spcast; tcsp.
Qed.

Lemma reduces_ksteps_excc_spexcc_decompose {o} :
  forall lib (k : nat) a (t : @CTerm o),
    reduces_ksteps_excc lib t (spexcc a) k
    -> {k1 : nat
        & {k2 : nat
        & {k3 : nat
        & {a' : CTerm
        & {e' : CTerm
        & k1 + k2 + k3 <= k
        # reduces_in_atmost_k_stepsc lib t (mkc_exception a' e') k1
        # reduces_in_atmost_k_stepsc lib a' (mkc_utoken a) k2
        # reduces_in_atmost_k_stepsc lib e' mkc_axiom k3 }}}}}.
Proof.
  introv r.
  pose proof (dec_reduces_in_atmost_k_steps_excc lib k t (spexcc a)) as h; allsimpl.
  try (fold (spexc a) in h).
  autodimp h hyp; eauto 3 with slow.
  destruct h as [d|d].
  - apply reduces_in_atmost_k_steps_excc_decompose in d; eauto 2 with slow.
  - provefalse; spcast; sp.
Qed.

Lemma reduces_ksteps_excc_impossible1 {o} :
  forall lib k1 k2 (t : @CTerm o) a n,
    reduces_ksteps_excc lib t (spexcc a) k1
    -> reduces_ksteps_excc lib t (mkc_nat n) k2
    -> False.
Proof.
  introv r1 r2; spcast.
  eapply reduces_in_atmost_k_steps_excc_impossible1 in r1; eauto.
Qed.

Lemma dec_reduces_ksteps_excc_nat {o} :
  forall lib k (t : @CTerm o),
    decidable {n : nat & reduces_ksteps_excc lib t (mkc_nat n) k}.
Proof.
  introv; destruct_cterms; allsimpl.
  pose proof (dec_reduces_in_atmost_k_steps_exc_nat lib k x) as h.
  destruct h as [h|h];[left|right].
  - exrepnd; exists n; spcast; tcsp.
  - intro r; exrepnd; destruct h; exists n; spcast; tcsp.
Qed.

Lemma equality_in_natE_implies {o} :
  forall lib (t u : @CTerm o) a,
    equality lib t u (natE a)
    -> equality_of_nat_tt lib t u
       [+] (cequivc lib t (spexcc a) # cequivc lib u (spexcc a)).
Proof.
  introv equ.

  assert {k : nat
          , {m : nat
          , (reduces_ksteps_excc lib t (mkc_nat m) k
             # reduces_ksteps_excc lib u (mkc_nat m) k)
            {+} (reduces_ksteps_excc lib t (spexcc a) k
                  # reduces_ksteps_excc lib u (spexcc a) k)}} as j.
  { apply equality_in_natE in equ.
    repndors.

    - unfold equality_of_nat in equ; exrepnd; spcast.
      allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
      exists (Peano.max k0 k1) k.
      left; dands; spcast.

      + apply (reduces_in_atmost_k_stepsc_le _ _ _ _ (Peano.max k0 k1)) in equ4; eauto 3 with slow;
        try (apply Nat.le_max_l; auto).
        apply reduces_in_atmost_k_steps_excc_can in equ4; tcsp.

      + apply (reduces_in_atmost_k_stepsc_le _ _ _ _ (Peano.max k0 k1)) in equ2; eauto 3 with slow;
        try (apply Nat.le_max_r; auto).
        apply reduces_in_atmost_k_steps_excc_can in equ2; tcsp.

    - repnd; spcast.
      apply cequivc_spexcc in equ0.
      apply cequivc_spexcc in equ.
      exrepnd.
      allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
      allrw @computes_to_excc_iff_reduces_in_atmost_k_stepsc; exrepnd.

      exists (Peano.max (k3 + k + k0) (k4 + k1 + k2)) 0.
      right; dands; spcast.

      + apply (reduces_in_atmost_k_steps_excc_le_exc _ (k3 + k + k0));
        eauto 3 with slow; tcsp;
        try (apply Nat.le_max_l; auto).
        pose proof (reduces_in_atmost_k_steps_excc_exception
                      lib k k0 n0 e0 (mkc_utoken a) mkc_axiom) as h.
        repeat (autodimp h hyp); tcsp; exrepnd.
        pose proof (reduces_in_atmost_k_steps_excc_trans2
                      lib k3 i
                      t
                      (mkc_exception n0 e0)
                      (mkc_exception (mkc_utoken a) mkc_axiom)) as q.
        repeat (autodimp q hyp); exrepnd.
        apply (reduces_in_atmost_k_steps_excc_le_exc _ i0); tcsp; try lia.

      + apply (reduces_in_atmost_k_steps_excc_le_exc _ (k4 + k1 + k2));
        eauto 3 with slow; tcsp;
        try (apply Nat.le_max_r; auto).
        pose proof (reduces_in_atmost_k_steps_excc_exception
                      lib k1 k2 n e (mkc_utoken a) mkc_axiom) as h.
        repeat (autodimp h hyp); tcsp; exrepnd.
        pose proof (reduces_in_atmost_k_steps_excc_trans2
                      lib k4 i
                      u
                      (mkc_exception n e)
                      (mkc_exception (mkc_utoken a) mkc_axiom)) as q.
        repeat (autodimp q hyp); exrepnd.
        apply (reduces_in_atmost_k_steps_excc_le_exc _ i0); tcsp; try lia.
  }

  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in j; auto.

  { exrepnd.
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in j0; auto.

    - exrepnd.
      pose proof (dec_reduces_ksteps_excc lib x t (mkc_nat x0)) as h.
      autodimp h hyp; simpl; eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x t (spexcc a)) as q.
      autodimp q hyp; simpl; try (fold (spexc a)); eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x u (mkc_nat x0)) as j.
      autodimp j hyp; simpl; eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x u (spexcc a)) as l.
      autodimp l hyp; simpl; try (fold (spexc a)); eauto 3 with slow.

      destruct h as [h|h];
      destruct q as [q|q];
      destruct j as [j|j];
      destruct l as [l|l];
      try (complete (eapply reduces_ksteps_excc_impossible1 in h;[|exact q]; tcsp));
      try (complete (eapply reduces_ksteps_excc_impossible1 in j;[|exact l]; eauto; tcsp));
      try (complete (provefalse; repndors; repnd; tcsp)).

      { left; exists x0; dands; split; simpl; eauto 3 with slow; exists x; spcast;
        apply reduces_in_atmost_k_steps_excc_can_implies in h;
        apply reduces_in_atmost_k_steps_excc_can_implies in j;
        allunfold @reduces_in_atmost_k_stepsc; allsimpl;
        allrw @get_cterm_apply; tcsp. }

      { right.
        apply reduces_ksteps_excc_spexcc_decompose in q.
        apply reduces_ksteps_excc_spexcc_decompose in l.
        exrepnd.
        allunfold @reduces_in_atmost_k_stepsc; allsimpl.
        allrw @get_cterm_apply; allsimpl.
        allrw @get_cterm_mkc_exception; allsimpl.
        dands;
          apply cequiv_spexc_if;
          try (apply isprog_apply);
          try (apply isprog_mk_nat);
          eauto 3 with slow.
        - exists (get_cterm a'0) (get_cterm e'0); dands; eauto 3 with slow.
          unfold computes_to_exception; exists k0; auto.
        - exists (get_cterm a') (get_cterm e'); dands; eauto 3 with slow.
          unfold computes_to_exception; exists k1; auto. }

    - clear j0.
      introv.

      pose proof (dec_reduces_ksteps_excc lib x t (mkc_nat x0)) as h.
      autodimp h hyp; simpl; eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x t (spexcc a)) as q.
      autodimp q hyp; simpl; try (fold (spexc a)); eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x u (mkc_nat x0)) as j.
      autodimp j hyp; simpl; eauto 3 with slow.
      pose proof (dec_reduces_ksteps_excc lib x u (spexcc a)) as l.
      autodimp l hyp; simpl; try (fold (spexc a)); eauto 3 with slow.

      destruct h as [h|h];
        destruct q as [q|q];
        destruct j as [j|j];
        destruct l as [l|l];
        tcsp;
        try (complete (right; intro xx; repndors; repnd; tcsp)).
  }

  { clear j; introv.

    pose proof (dec_reduces_ksteps_excc_nat lib x t) as h.
    pose proof (dec_reduces_ksteps_excc lib x t (spexcc a)) as q.
    autodimp q hyp; simpl; try (fold (spexc a)); eauto 3 with slow.
    pose proof (dec_reduces_ksteps_excc_nat lib x u) as j.
    pose proof (dec_reduces_ksteps_excc lib x u (spexcc a)) as l.
    autodimp l hyp; simpl; try (fold (spexc a)); eauto 3 with slow.

    destruct h as [h|h];
      destruct q as [q|q];
      destruct j as [j|j];
      destruct l as [l|l];
      exrepnd;
      try (destruct (deq_nat n0 n) as [d|d]); subst;
      tcsp;
      try (complete (eapply reduces_ksteps_excc_impossible1 in h0; eauto; tcsp));
      try (complete (eapply reduces_ksteps_excc_impossible1 in j0; eauto; tcsp));
      try (complete (provefalse; repndors; repnd; tcsp));
      try (complete (right; intro xx; exrepnd; repndors; repnd; tcsp;
                     try (complete (destruct h; eexists; eauto));
                     try (complete (destruct j; eexists; eauto))));
      try (complete (left; exists n; left; tcsp));
      try (complete (left; exists 0; right; tcsp)).

    right; intro xx; exrepnd; repndors; repnd; tcsp; spcast.
    allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
    allunfold @reduces_in_atmost_k_steps_exc.
    rw xx1 in h0.
    rw xx0 in j0.
    inversion h0.
    inversion j0.
    allapply Znat.Nat2Z.inj; subst; tcsp.
  }
Qed.

Lemma tequality_with_nexc_c {o} :
  forall lib a1 a2 (T1 T2 E1 E2 : @CTerm o),
    tequality lib (with_nexc_c a1 T1 E1) (with_nexc_c a2 T2 E2)
    <=> (a1 = a2 # tequality lib T1 T2 # tequality lib E1 E2).
Proof.
  introv.
  unfold with_nexc_c.
  rw @tequality_bunion.
  rw @tequality_mkc_texc.
  rw @tequality_mkc_singleton_uatom.
  split; sp.
Qed.

Lemma tequality_natE {o} :
  forall lib (a1 a2 : @get_patom_set o),
    tequality lib (natE a1) (natE a2) <=> a1 = a2.
Proof.
  introv.
  unfold natE.
  rw @tequality_with_nexc_c.
  allrw @fold_type.
  split; intro k; repnd; dands; eauto with slow.
Qed.

Lemma type_natE {o} :
  forall lib (a : @get_patom_set o),
    type lib (natE a).
Proof.
  introv.
  rw @tequality_natE; auto.
Qed.
Hint Resolve type_natE : slow.

Lemma disjoint_nat_unit {o}:
  forall (lib : @library o),
    disjoint_types lib mkc_tnat mkc_unit.
Proof.
  introv mem; repnd.
  allrw @equality_in_tnat.
  allrw @equality_in_unit.
  allunfold @equality_of_nat; exrepnd; spcast; GC.
  computes_to_eqval.
Qed.
Hint Resolve disjoint_nat_unit : slow.

Lemma member_bunion_nat_unit_implies_cis_spcan_not_atom {o} :
  forall lib (t : @CTerm o) a,
    member lib t (mkc_bunion mkc_tnat mkc_unit)
    -> cis_spcan_not_atom lib t a.
Proof.
  introv mem.
  apply @equality_in_disjoint_bunion in mem; eauto 3 with slow.
  repnd.
  clear mem0 mem1.
  repndors.
  - apply equality_in_tnat in mem.
    unfold equality_of_nat in mem; exrepnd; spcast.
    exists (@mkc_nat o k); dands; spcast; simpl; tcsp.
  - apply equality_in_unit in mem; repnd; spcast.
    exists (@mkc_axiom o); dands; spcast; simpl; tcsp.
Qed.
