(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
Require Export natk.
Require Export natk2.
Require Export cequiv_seq_util.
(*Require Export per_respects.*)
Require Export per_props_nat.

(*Require Export per_props_union.*)


Lemma equality_mkc_inl_implies {o} :
  forall lib (t1 t2 A B : @CTerm o),
    equality lib (mkc_inl t1) (mkc_inl t2) (mkc_union A B)
    -> equality lib t1 t2 A.
Proof.
  introv e.
  apply equality_mkc_union in e; repnd.
  repndors; exrepnd; spcast;
  apply computes_to_valc_isvalue_eq in e2; eauto 3 with slow;
  apply computes_to_valc_isvalue_eq in e4; eauto 3 with slow;
  eqconstr e2; eqconstr e4; auto.
Qed.

Lemma equality_tt_in_bool_implies_cequiv {o} :
  forall lib (t : @CTerm o),
    equality lib t tt mkc_bool
    -> ccequivc lib t tt.
Proof.
  introv e.
  apply equality_in_bool in e; repndors; repnd; spcast; eauto with slow.
  apply tt_not_cequivc_ff in e; sp.
Qed.

Lemma implies_isl_in_bool {o} :
  forall lib (A B a b : @CTerm o),
    equality lib a b (mkc_union A B)
    -> equality lib (mkc_isl a) (mkc_isl b) mkc_bool.
Proof.
  introv e.
  apply equality_mkc_union in e; exrepnd.
  apply equality_in_bool.
  repndors; exrepnd; spcast;[left|right]; dands; spcast.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
Qed.

Lemma tequality_natk2nat {o} :
  forall lib (a b : @CTerm o),
    tequality lib (natk2nat a) (natk2nat b)
     <=> {k1 : Z
          , {k2 : Z
          , (a) ===>(lib) (mkc_integer k1)
          # (b) ===>(lib) (mkc_integer k2)
          # (forall k : Z,
               (0 <= k)%Z ->
               ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z)}}.
Proof.
  introv.
  unfold natk2nat.
  rw @tequality_mkc_fun.
  rw @tequality_mkc_natk.
  split; intro k; exrepnd; dands; eauto 3 with slow.

  - spcast; exists k1 k0; dands; spcast; auto.

  - spcast; exists k1 k2; dands; spcast; auto.

  - introv inh; apply type_tnat.
Qed.

Lemma lsubstc_mk_unit {o} :
  forall w (s : @CSub o) c,
    lsubstc mk_unit w s c = mkc_unit.
Proof.
  introv.
  unfold mk_unit, mkc_unit.
  rw @lsubstc_mk_true; apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_natU {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_natU w s c) natU.
Proof.
  introv.
  unfold mk_natU, natU.
  pose proof (lsubstc_mk_bunion_ex mk_tnat mk_unit s w c) as h.
  exrepnd.
  eapply alphaeqc_trans;[exact h1|]; clear h1.
  rw @lsubstc_mkc_tnat.
  rw @lsubstc_mk_unit.
  apply alphaeqc_refl.
Qed.

Lemma type_natU {o} :
  forall (lib : @library o),
    type lib natU.
Proof.
  introv.
  apply tequality_bunion; dands; eauto 3 with slow.
  - apply type_tnat.
  - apply tequality_unit.
Qed.

Lemma lsubstc_mk_nat2nat {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_nat2nat w s c) nat2nat.
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 2 with slow.

  simpl.

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  fold_terms.
  auto.
Qed.

Lemma type_nat2nat {o} :
  forall (lib : @library o), type lib nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply type_mkc_fun; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2nat : slow.

Lemma equality_natk_to_tnat {o} :
  forall lib (n1 n2 k : @CTerm o),
    equality lib n1 n2 (mkc_natk k)
    -> equality lib n1 n2 mkc_tnat.
Proof.
  introv e.

  apply equality_in_natk in e; exrepnd; spcast.
  apply equality_in_tnat.
  exists m; dands; spcast; auto.
Qed.

Lemma equality_nat2nat_to_natk2nat {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_tnat
    -> equality lib f g nat2nat
    -> equality lib f g (natk2nat n).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { apply type_mkc_natk.
    exists (Z.of_nat k); spcast; auto. }

  introv en.
  apply equality_natk_to_tnat in en; apply e in en; auto.
Qed.

Lemma nat_in_nat {o} :
  forall (lib : @library o) n,
    member lib (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat.
  exists n; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Definition equality_of_nat_tt {o} lib (n m : @CTerm o) :=
  {k : nat & computes_to_valc lib n (mkc_nat k)
           # computes_to_valc lib m (mkc_nat k)}.

Definition equality_of_nat2 {p} lib (t1 t2 : @CTerm p) :=
  {j : nat
   , {n : nat
   , reduces_kstepsc lib t1 (mkc_nat n) j
   # reduces_kstepsc lib t2 (mkc_nat n) j}}.

Lemma equality_of_nat_implies_nat2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2 -> equality_of_nat2 lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
  exists (Peano.max k1 k0); exists k; dands; spcast.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e4]; auto;
    apply Nat.le_max_r; auto.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e2]; auto;
    apply Nat.le_max_l; auto.
Qed.

Lemma equality_of_nat2_implies_nat {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat2 lib t1 t2 -> equality_of_nat lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat2 in e; exrepnd; spcast.
  exists n; dands; spcast;
  apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
  dands; eauto 3 with slow.
Qed.

Lemma dec_reduces_kstepsc {o} :
  forall lib k (t v : @CTerm o),
    (forall x, decidable (x = get_cterm v))
    -> decidable (reduces_kstepsc lib t v k).
Proof.
  introv d.
  destruct_cterms; allsimpl.
  pose proof (dec_reduces_in_atmost_k_steps lib k x0 x d) as h.
  destruct h as [h|h];[left|right].
  - spcast; tcsp.
  - intro r; spcast; tcsp.
Qed.

Lemma equality_of_nat_imp_tt {o} :
  forall lib (n m : @CTerm o),
    equality_of_nat lib n m
    -> equality_of_nat_tt lib n m.
Proof.
  introv e.
  unfold equality_of_nat_tt.
  apply equality_of_nat_implies_nat2 in e.
  unfold equality_of_nat2 in e.
  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in e; auto.

  - exrepnd.
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in e0; auto.

    + exrepnd.
      exists x0; dands; auto;
      apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
      dands; eauto 3 with slow; exists x; spcast; auto.

    + clear e0.
      introv.
      pose proof (dec_reduces_kstepsc lib x n (mkc_nat x0)) as h; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      pose proof (dec_reduces_kstepsc lib x m (mkc_nat x0)) as q; allsimpl.
      autodimp q hyp; eauto 3 with slow.
      destruct h as [h|h]; destruct q as [q|q]; tcsp;
      try (complete (right; intro r; repnd; tcsp)).

  - clear e.
    introv.
    remember (compute_at_most_k_steps lib x (get_cterm n)) as c1; symmetry in Heqc1.
    remember (compute_at_most_k_steps lib x (get_cterm m)) as c2; symmetry in Heqc2.
    destruct c1, c2.

    + destruct (decidable_ex_mk_nat n0) as [h|h]; exrepnd.

      * rw h0 in Heqc1; clear h0.
        destruct (decidable_ex_mk_nat n1) as [q|q]; exrepnd.

        { rw q0 in Heqc2; clear q0.
          destruct (deq_nat n2 n3) as [d|d].

          - subst.
            left; exists n3; dands; spcast; auto.

          - right; intro r; exrepnd; spcast.
            allunfold @reduces_in_atmost_k_stepsc; allsimpl.
            allunfold @reduces_in_atmost_k_steps.
            rw Heqc1 in r1.
            rw Heqc2 in r0.
            inversion r1 as [c1].
            inversion r0 as [c2].
            allapply Znat.Nat2Z.inj; subst; tcsp.
        }

        { right; intro r; exrepnd; spcast.
          allunfold @reduces_in_atmost_k_stepsc; allsimpl.
          allunfold @reduces_in_atmost_k_steps.
          rw Heqc1 in r1.
          rw Heqc2 in r0.
          inversion r1 as [c1].
          inversion r0 as [c2].
          allapply Znat.Nat2Z.inj; subst; tcsp.
          destruct q; exists n3; auto.
        }

      * right; intro r; exrepnd; spcast.
        allunfold @reduces_in_atmost_k_stepsc; allsimpl.
        allunfold @reduces_in_atmost_k_steps.
        rw Heqc1 in r1.
        rw Heqc2 in r0.
        inversion r1 as [c1].
        inversion r0 as [c2].
        allapply Znat.Nat2Z.inj; subst; tcsp.
        destruct h; exists n2; auto.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.
Qed.

Lemma equality_in_tnat_nat {o} :
  forall (lib : @library o) n, equality lib (mkc_nat n) (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat; unfold equality_of_nat; exists n.
  dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.
Hint Resolve equality_in_tnat_nat : slow.

Lemma member_tnat_implies_computes {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    -> {k : nat & computes_to_valc lib t (mkc_nat k)}.
Proof.
  introv mem.
  apply equality_in_tnat in mem.
  apply equality_of_nat_imp_tt in mem.
  unfold equality_of_nat_tt in mem; exrepnd.
  exists k; auto.
Qed.

Lemma member_tnat_iff {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    <=> {k : nat & computes_to_valc lib t (mkc_nat k)}.
Proof.
  introv; split; introv mem.
  - apply member_tnat_implies_computes; auto.
  - apply equality_in_tnat.
    exrepnd.
    exists k; dands; spcast; auto.
Qed.


Lemma equality_nat2nat_apply {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2nat
    -> equality lib a b mkc_tnat
    -> equality lib (mkc_apply f a) (mkc_apply g b) mkc_tnat.
Proof.
  introv eqf eqn.
  unfold nat2nat in eqf.
  apply equality_in_fun in eqf; repnd.
  apply eqf in eqn; auto.
Qed.

Lemma equality_int_nat_implies_cequivc {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    -> cequivc lib a b.
Proof.
  introv eqn.
  apply equality_in_tnat in eqn.
  apply equality_of_nat_imp_tt in eqn.
  unfold equality_of_nat_tt in eqn; exrepnd.
  eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact eqn1|].
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma member_nseq_nat2nat {o} :
  forall (lib : @library o) s,
    member lib (mkc_nseq s) nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply equality_in_fun; dands; tcsp; eauto 3 with slow.
  introv eqn.
  applydup @equality_int_nat_implies_cequivc in eqn.
  apply equality_respects_cequivc.
  { apply implies_cequivc_apply; auto. }
  clear eqn0.
  apply equality_refl in eqn.
  apply member_tnat_iff in eqn; exrepnd.

  eapply member_respects_cequivc.
  { apply cequivc_sym.
    apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact eqn0].
  }

  apply (member_respects_cequivc _ (mkc_nat (s k))).
  { apply cequivc_sym.
    apply reduces_toc_implies_cequivc.
    unfold reduces_toc; simpl.
    eapply reduces_to_if_split2.
    { csunf; simpl; auto. }
    apply reduces_to_if_step.
    csunf; simpl; dcwf h; simpl.
    boolvar; try omega.
    allrw @Znat.Nat2Z.id; auto.
  }
  apply nat_in_nat.
Qed.
