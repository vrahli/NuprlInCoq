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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export computation_preserve4.


Lemma reduces_atmost_split {p} :
  forall lib n m (t1 t2 t3 : @NTerm p),
    reduces_in_atmost_k_steps lib t1 t2 n
    -> reduces_in_atmost_k_steps lib t1 t3 m
    -> n<=m
    -> reduces_in_atmost_k_steps lib t2 t3 (m-n).
Proof.
  unfold reduces_in_atmost_k_steps.
  exact compute_split.
Qed.

Lemma reduces_atmost_preserves_program {p} :
  forall lib k (t1 t2 : @NTerm p),
    reduces_in_atmost_k_steps lib t1 t2 k
    -> isprogram t1
    -> isprogram t2.
Proof.
  unfold reduces_in_atmost_k_steps.
  exact computek_preserves_program.
Qed.

Lemma computes_to_exception_preserves_program {p} :
  forall lib a (t e : @NTerm p),
    computes_to_exception lib a t e
    -> isprogram t
    -> isprogram e.
Proof.
  unfold computes_to_exception, reduces_to; introv comp isp; exrepnd.
  apply reduces_atmost_preserves_program in comp0; auto.
  apply isprogram_exception_iff in comp0; sp.
Qed.

Lemma computes_to_value_preserves_program {p} :
  forall lib (t v : @NTerm p),
    computes_to_value lib t v
    -> isprogram t
    -> isprogram v.
Proof.
  unfold computes_to_value, reduces_to; introv comp isp; exrepnd.
  apply reduces_atmost_preserves_program in comp1; auto.
Qed.

(* ra stands for reduces_atmost *)
Lemma no_change_after_value_ra {p} :
  forall lib (t : @NTerm p) k1 v1,
    reduces_in_atmost_k_steps lib t v1 k1
    -> isvalue v1
    -> forall k2,
         k1 <= k2
         -> reduces_in_atmost_k_steps lib t v1 k2.
Proof.
  unfold reduces_in_atmost_k_steps.
  exact no_change_after_value2.
Qed.

Lemma no_change_after_val_or_exc {p} :
  forall lib (t : @NTerm p) k1 v1,
    reduces_in_atmost_k_steps lib t v1 k1
    -> isprogram v1
    -> is_can_or_exc v1
    -> forall k2,
         k1 <= k2
         -> reduces_in_atmost_k_steps lib t v1 k2.
Proof.
  introv r i o l.
  destruct o as [o|o].

  - apply @no_change_after_value_ra with (k1 := k1); auto.

  - apply isexc_implies in o; auto; exrepnd; subst.
    generalize (no_change_after_exception2 lib a t k1 e r k2 l); sp.
Qed.

Lemma no_change_after_val_or_exc2 {p} :
  forall lib (t : @NTerm p) k1 v1,
    computes_to_val_or_exc_in_max_k_steps lib t v1 k1
    -> isprogram v1
    -> forall k2,
         k1 <= k2
         -> computes_to_val_or_exc_in_max_k_steps lib t v1 k2.
Proof.
  introv comp isp le.
  allunfold @computes_to_val_or_exc_in_max_k_steps; repnd; dands; auto.
  apply @no_change_after_val_or_exc with (k1 := k1); auto.
Qed.

(*
Lemma no_change_after_marker {p} :
  forall lib t k1 m,
    @computes_to_marker_in_max_k_steps p lib t m k1
    -> forall k, computes_to_marker_in_max_k_steps lib t m (k + k1).
Proof.
  intros.
  induction k; simpl; auto.
  allunfold @computes_to_marker_in_max_k_steps.
  allunfold @reduces_in_atmost_k_steps; repnd.
  simpl.
  rw IHk; csunf; simpl.
Qed.

Lemma no_change_after_marker2 {p} :
  forall lib t k1 v1,
    @computes_to_marker_in_max_k_steps p lib t v1 k1
    -> forall k2,
         k1 <= k2
         -> computes_to_marker_in_max_k_steps lib t v1 k2.
Proof.
  intros.
  assert(k2 = (k2 - k1) + k1) as rwa by lia.
  rewrite rwa.
  apply no_change_after_marker; auto.
Qed.
*)

Lemma isvalue_like_implies_or1 {o} :
  forall t : @NTerm o,
    isvalue_like t
    -> is_can_or_exc t.
Proof.
  introv ivl.
  unfold isvalue_like in ivl.
  unfold is_can_or_exc; sp.
Qed.

Lemma no_change_after_val_like {p} :
  forall lib (t : @NTerm p) k1 v1,
    reduces_in_atmost_k_steps lib t v1 k1
    -> isprogram v1
    -> isvalue_like v1
    -> forall k2,
         k1 <= k2
         -> reduces_in_atmost_k_steps lib t v1 k2.
Proof.
  introv r i o l.
  apply isvalue_like_implies_or1 in o.
  eapply no_change_after_val_or_exc; eauto.
Qed.

Lemma no_change_after_val_like2 {p} :
  forall lib (t : @NTerm p) k1 v1,
    computes_to_val_like_in_max_k_steps lib t v1 k1
    -> isprogram v1
    -> forall k2,
         k1 <= k2
         -> computes_to_val_like_in_max_k_steps lib t v1 k2.
Proof.
  introv comp isp le.
  allunfold @computes_to_val_like_in_max_k_steps; repnd; dands; auto.
  apply @no_change_after_val_like with (k1 := k1); auto.
Qed.

Lemma reduces_atmost_exists_step {p} :
  forall lib t m a,
    reduces_in_atmost_k_steps lib t a m
    -> m > 0
    -> {tc : @NTerm p $ compute_step lib t = csuccess tc}.
Proof.
  unfold reduces_in_atmost_k_steps.
  exact compute_at_most_k_steps_step.
Qed.

Lemma reduces_atmost_S {p} :
  forall lib t1 t2 n,
    reduces_in_atmost_k_steps lib t1 t2 (S n)
    -> {t : @NTerm p & compute_step lib t1 = csuccess t # reduces_in_atmost_k_steps lib t t2 n}.
Proof.
  unfold reduces_in_atmost_k_steps; introv comp.
  rw @compute_at_most_k_steps_eq_f in comp.
  simpl in comp.
  remember (compute_step lib t1); destruct c; try (complete (inversion comp)).
  exists n0; sp.
  rw <- @compute_at_most_k_steps_eq_f in comp; auto.
Qed.

Lemma reduces_atmost_exc {p} :
  forall lib bterms (v : @NTerm p) k,
    reduces_in_atmost_k_steps lib (oterm Exc bterms) v k
    -> v = oterm Exc bterms.
Proof.
  introv comp.
  unfold reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_exception in comp.
  inversion comp; subst; sp.
Qed.

Lemma reduces_atmost_can {p} :
  forall lib c bterms (a : @NTerm p) k,
    reduces_in_atmost_k_steps lib (oterm (Can c) bterms) a k
    -> a = oterm (Can c) bterms.
Proof.
  introv comp.
  unfold reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_can in comp.
  inversion comp; subst; sp.
Qed.

Lemma computes_to_exception_as_reduces_to {p} :
  forall lib n (a b : @NTerm p),
    computes_to_exception lib n a b <=> reduces_to lib a (mk_exception n b).
Proof.
  sp.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_preserves_program {p} :
  forall lib k (t1 t2 : @NTerm p),
    computes_to_val_or_exc_in_max_k_steps lib t1 t2 k
    -> isprogram t1
    -> isprogram t2.
Proof.
  unfold computes_to_val_or_exc_in_max_k_steps, reduces_in_atmost_k_steps;
  introv comp isp; repnd.
  apply computek_preserves_program in comp0; sp.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_S {p} :
  forall lib t v k,
    computes_to_val_or_exc_in_max_k_steps lib t v (S k)
    <=> {u : @NTerm p
        & compute_step lib t = csuccess u
        # computes_to_val_or_exc_in_max_k_steps lib u v k}.
Proof.
  introv; split; intro comp.

  - allunfold @computes_to_val_or_exc_in_max_k_steps; repnd.
    apply reduces_in_atmost_k_steps_S in comp0; exrepnd.
    exists u; sp.

  - exrepnd.
    allunfold @computes_to_val_or_exc_in_max_k_steps; repnd; dands; auto.
    rw @reduces_in_atmost_k_steps_S.
    exists u; sp.
Qed.

Lemma computes_to_exception_in_max_k_steps_S {p} :
  forall lib a (t : @NTerm p) v k,
    computes_to_exception_in_max_k_steps lib a t v (S k)
    <=> {u : NTerm
        & compute_step lib t = csuccess u
        # computes_to_exception_in_max_k_steps lib a u v k}.
Proof.
  introv; split; intro comp.

  - allunfold @computes_to_exception_in_max_k_steps; repnd.
    apply reduces_in_atmost_k_steps_S in comp; exrepnd.
    exists u; sp.

  - exrepnd.
    allunfold @computes_to_exception_in_max_k_steps; repnd; dands; auto.
    rw @reduces_in_atmost_k_steps_S.
    exists u; sp.
Qed.

Lemma computes_to_exception_in_max_k_steps_can {p} :
  forall lib a c bterms (e : @NTerm p) k,
    computes_to_exception_in_max_k_steps lib a (oterm (@Can p c) bterms) e k
    -> False.
Proof.
  unfold computes_to_exception_in_max_k_steps, reduces_in_atmost_k_steps.
  induction k; introv comp.

  - simpl in comp.
    inversion comp.

  - rw @compute_at_most_k_steps_eq_f in comp.
    rw @compute_at_most_k_stepsf_S in comp.
    simpl in comp.
    rw <- @compute_at_most_k_steps_eq_f in comp; sp.
Qed.

Lemma computes_to_exception_in_max_k_steps_exc {p} :
  forall lib a (e : @NTerm p) v k,
    computes_to_exception_in_max_k_steps lib a (mk_exception a e) v k
    <=> v = e.
Proof.
  unfold computes_to_exception_in_max_k_steps, reduces_in_atmost_k_steps.
  introv.
  rw @compute_at_most_k_steps_eq_f.
  revert k e a.
  induction k; simpl; introv.
  - split; intro h; subst; sp.
    inversion h; subst; sp.
  - apply IHk.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_can_iff {p} :
  forall lib c bterms a k,
    computes_to_val_or_exc_in_max_k_steps lib (oterm (@Can p c) bterms) a k
    <=> a = oterm (Can c) bterms.
Proof.
  introv; split; intro comp; subst.
  apply computes_to_val_or_exc_in_max_k_steps_can in comp; auto.
  unfold computes_to_val_or_exc_in_max_k_steps, reduces_in_atmost_k_steps.
  dands; try (complete (left; sp)).
  induction k; simpl; sp.
  rw IHk; simpl; sp.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_exc_iff {p} :
  forall lib bterms (t : @NTerm p) k,
    computes_to_val_or_exc_in_max_k_steps lib (oterm Exc bterms) t k
    <=> t = oterm Exc bterms.
Proof.
  introv; split; intro comp; subst.
  apply computes_to_val_or_exc_in_max_k_steps_exc in comp; auto.
  unfold computes_to_val_or_exc_in_max_k_steps, reduces_in_atmost_k_steps.
  dands; try (complete (right; sp)).
  induction k; simpl; sp.
  rw IHk; simpl; sp.
Qed.

(*
Lemma reduces_in_atmost_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs v,
    reduces_in_atmost_k_steps
      lib
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
      v k
    -> v = oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs).
Proof.
  introv h.
  unfold reduces_in_atmost_k_steps in h.
  rw @compute_at_most_k_steps_primarg_marker in h; ginv; auto.
Qed.
*)

(*
Lemma computes_to_val_or_exc_in_max_k_steps_arith_implies {p} :
  forall lib k a n1 n2 v,
    isprogram n1
    -> isprogram n2
    -> computes_to_val_or_exc_in_max_k_steps lib
         (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
         v
         k
    -> {nv1 , nv2 : Z
       $ { k1 , k2 : nat
         $ v = mk_integer (get_arith_op a nv1 nv2)
         # k1+k2+1 <= k
         # computes_to_value_in_max_k_steps lib k1 n1 (mk_integer nv1)
         # computes_to_value_in_max_k_steps lib k2 n2 (mk_integer nv2)
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
              (oterm (NCan (NArithOp a))
                     [bterm [] (mk_integer nv1),
                      bterm [] (mk_integer nv2)])
              (k1+k2)
       }}
       [+]
       {e : NTerm
       $ { k1 : nat
         $ k1 + 1 <= k
         # v = mk_exception e
         # computes_to_exception_in_max_k_steps lib n1 e k1
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
              (oterm (NCan (NArithOp a))
                     [bterm [] v,
                      bterm [] n2])
              k1
       }}
       [+]
       {x , e : @NTerm p
       $ { k1 , k2 : nat
         $ k1+k2+1 <= k
         # v = mk_exception e
         # computes_to_value_in_max_k_steps lib k1 n1 x
         # computes_to_exception_in_max_k_steps lib n2 e k2
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
              (oterm (NCan (NArithOp a))
                     [bterm [] x,
                      bterm [] v])
              (k1+k2)
       }}.
Proof.
  induction k; introv isp1 isp2 comp.

  - destruct comp as [r is].
    inversion r; subst.
    dorn is;[|dorn is]; inversion is.

  - apply computes_to_val_or_exc_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1)).
    dopid o as [can1|ncan1|exc1|nexc1|mrk1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (inversion comp1)).
      dopid o as [can2|ncan2|exc2|nexc2|mrk2|abs2] SCase.

      * SCase "Can".
        simpl in comp1.
        unfold compute_step_arith in comp1.
        destruct l; try (complete (inversion comp1)).
        destruct l0; try (complete (inversion comp1)).
        destruct can1; try (complete (inversion comp1)).
        destruct can2; try (complete (inversion comp1)).
        remember (get_int_from_cop (Nint z)).
        remember (get_int_from_cop (Nint z0)).
        allsimpl.
        destruct o; destruct o0; try (complete (inversion comp1)).
        inversion comp1; subst; GC; cpx.
        apply computes_to_val_or_exc_in_max_k_steps_can in comp0; subst.
        left.
        exists z z0 0 0; simpl; dands; auto; try lia.
        unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps; sp.
        constructor; apply isprogram_integer.
        unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps; sp.
        constructor; apply isprogram_integer.
        unfold reduces_in_atmost_k_steps; sp.

      * SCase "NCan".
        rw @compute_step_narithop_ncan2 in comp1.
        remember (compute_step lib (oterm (NCan ncan2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        {
          left.
          exists nv1 nv2 k1 (S k2); dands; auto; try lia.
          rw @computes_to_value_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_ncan2.
          rw Heqc; auto.
        }

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        {
          apply computes_to_exception_in_max_k_steps_can in comp3; sp.
        }

        {
          right; right.
          exists x e k1 (S k2); dands; auto; try lia.
          rw @computes_to_exception_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_ncan2.
          rw Heqc; auto.
        }

      * SCase "Exc".
        simpl in comp1; inversion comp1; subst; GC.
        right; right.
        apply isprogram_exception_implies in isp2; exrepnd; sp; subst.
        apply computes_to_val_or_exc_in_max_k_steps_exc_iff in comp0; subst.
        exists (oterm (Can can1) l) t 0 0; simpl; dands; auto; try lia.
        unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps;
          simpl; dands; auto.
        apply computes_to_exception_in_max_k_steps_exc; sp.
        unfold reduces_in_atmost_k_steps; simpl; auto.

      * SCase "NExc".
        simpl in comp1; inversion comp1; subst; GC.
        apply computes_to_val_or_exc_in_max_k_steps_nexc in comp0; subst.
        right; right.
        apply isprogram_exception_implies in isp2; exrepnd; sp; subst.
        apply computes_to_val_or_exc_in_max_k_steps_exc_iff in comp0; subst.
        exists (oterm (Can can1) l) t 0 0; simpl; dands; auto; try lia.
        unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps;
          simpl; dands; auto.
        apply computes_to_exception_in_max_k_steps_exc; sp.
        unfold reduces_in_atmost_k_steps; simpl; auto.

      * SCase "Mrk".
        allsimpl; fold_terms; ginv.

      * SCase "Abs".
        rw @compute_step_narithop_abs2 in comp1.
        remember (compute_step lib (oterm (Abs abs2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        left.
        exists nv1 nv2 k1 (S k2); dands; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a))
                      [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
        rw @compute_step_narithop_abs2.
        rw Heqc; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        apply computes_to_exception_in_max_k_steps_can in comp3; sp.

        right; right.
        exists x e k1 (S k2); dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a))
                      [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
        rw @compute_step_narithop_abs2.
        rw Heqc; auto.

    + Case "NCan".
      rw @compute_step_narithop_ncan1 in comp1.
      remember (compute_step lib (oterm (NCan ncan1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.

      destruct comp0 as [comp0|comp0]; [|destruct comp0 as [comp0|comp0]];
      exrepnd; subst.

      * left.
        exists nv1 nv2 (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); sp.
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

      * right; left.
        exists e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]).
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

      * right; right.
        exists x e (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); dands; auto.
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

    + Case "Exc".
      simpl in comp1.
      unfold compute_step_catch in comp1; inversion comp1; subst; GC.
      apply computes_to_val_or_exc_in_max_k_steps_exc in comp0; subst.
      right; left.
      apply isprogram_exception_implies in isp1; exrepnd; subst.
      exists t 0; dands; auto; try lia.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "NExc".
      provefalse.
      allsimpl; ginv.
      apply computes_to_val_or_exc_in_max_k_steps_nexc in comp0; sp.

    + Case "Mrk".
      allsimpl; ginv; fold_terms.
      unfold computes_to_val_or_exc_in_max_k_steps in comp0; repnd.
      apply reduces_in_atmost_k_steps_primarg_marker in comp1; subst.
      dorn comp0; inversion comp0.

    + Case "Abs".
      rw @compute_step_narithop_abs1 in comp1.
      remember (compute_step lib (oterm (Abs abs1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.

      destruct comp0 as [comp0|comp0]; [|destruct comp0 as [comp0|comp0]];
      exrepnd; subst.

      * left.
        exists nv1 nv2 (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); sp.
        rw @compute_step_narithop_abs1; rw Heqc; auto.

      * right; left.
        exists e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]).
        rw @compute_step_narithop_abs1; rw Heqc; auto.

      * right; right.
        exists x e (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); dands; auto.
        rw @compute_step_narithop_abs1; rw Heqc; auto.
Qed.
*)

Definition spcan {p} (c : @CanonicalOp p) := oterm (Can c) [].

(*
Lemma computes_to_val_or_exc_in_max_k_steps_comp_implies {p} :
  forall lib k a n1 n2 n3 n4 v,
    isprogram n1
    -> isprogram n2
    -> isprogram n3
    -> isprogram n4
    -> computes_to_val_or_exc_in_max_k_steps lib
         (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
         v
         k
    -> {c1 , c2 : CanonicalOp
       $ { k1 , k2 : nat
       $ { d : bool
         $ k1+k2+1 <= k
         # computes_to_value_in_max_k_steps lib k1 n1 (spcan c1)
         # computes_to_value_in_max_k_steps lib k2 n2 (spcan c2)
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd (spcan c1),
                      nobnd (spcan c2),
                      nobnd n3,
                      nobnd n4])
              (k1+k2)
         # computes_to_val_or_exc_in_max_k_steps lib
                   (if d then n3 else n4)
                   v
                   (k - (k1 + k2 + 1))
         # ({i1, i2 : Z
             $ a = CompOpLess
             # c1 = Nint i1
             # c2 = Nint i2
             # d = Z.ltb i1 i2}
           [+]
           {i1, i2 : Z
             $ a = CompOpInteq
             # c1 = Nint i1
             # c2 = Nint i2
             # d = Z.eqb i1 i2}
           [+]
           {s1, s2 : String.string
             $ a = CompOpAtomeq
             # c1 = NTok s1
             # c2 = NTok s2
             # d = if String.string_dec s1 s2 then true else false})
       }}}
       [+]
       {e : NTerm
       $ { k1 : nat
         $ k1 + 1 <= k
         # v = mk_exception e
         # computes_to_exception_in_max_k_steps lib n1 e k1
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd v,
                      nobnd n2,
                      nobnd n3,
                      nobnd n4])
              k1
       }}
       [+]
       {x , e : @NTerm p
       $ { k1 , k2 : nat
         $ k1+k2+1 <= k
         # v = mk_exception e
         # computes_to_value_in_max_k_steps lib k1 n1 x
         # computes_to_exception_in_max_k_steps lib n2 e k2
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd x,
                      nobnd v,
                      nobnd n3,
                      nobnd n4])
              (k1+k2)
       }}.
Proof.
  induction k; introv isp1 isp2 isp3 isp4 comp.

  - destruct comp as [r is].
    inversion r; subst.
    destruct is as [is|is]; inversion is.

  - apply computes_to_val_or_exc_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1)).
    dopid o as [can1|ncan1|exc1|nexc1|mrk1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (inversion comp1)).
      dopid o as [can2|ncan2|exc2|nexc2|mrk2|abs2] SCase.

      * SCase "Can".
        simpl in comp1.
        unfold compute_step_comp in comp1.
        destruct l; try (complete (inversion comp1)).
        destruct l0; try (complete (inversion comp1)).
        simpl in comp1.

        destruct a; try (complete (inversion comp1)).

        {
          remember (get_int_from_cop can1).
          remember (get_int_from_cop can2).
          destruct o; destruct o0; try (complete (inversion comp1)).
          inversion comp1; subst; GC; cpx.
          left.
          exists can1 can2 0 0 ((z <? z0)%Z); simpl; dands; auto; try lia;
          try (complete (unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps; sp;
                         constructor; sp)).
          rw minus0; auto.
          left.
          destruct can1; inversion Heqo; subst; GC.
          destruct can2; inversion Heqo0; subst; GC.
          exists z1 z; dands; auto.
        }

        {
          remember (get_int_from_cop can1).
          remember (get_int_from_cop can2).
          destruct o; destruct o0; try (complete (inversion comp1)).
          inversion comp1; subst; GC; cpx.
          left.
          exists can1 can2 0 0 ((z =? z0)%Z); simpl; dands; auto; try lia;
          try (complete (unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps; sp;
                         constructor; sp)).
          rw minus0; auto.
          right; left.
          destruct can1; inversion Heqo; subst; GC.
          destruct can2; inversion Heqo0; subst; GC.
          exists z1 z; dands; auto.
        }

        {
          remember (get_str_from_cop can1).
          remember (get_str_from_cop can2).
          destruct o; destruct o0; try (complete (inversion comp1)).
          inversion comp1; subst; GC; cpx.
          left.
          exists can1 can2 0 0 (if String.string_dec s s0 then true else false); simpl; dands; auto; try lia;
          try (complete (unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps; sp;
                         constructor; sp)).
          rw minus0; auto.
          destruct (String.string_dec s s0); allsimpl; auto.
          right; right.
          destruct can1; inversion Heqo; subst; GC.
          destruct can2; inversion Heqo0; subst; GC.
          exists s1 s; dands; auto.
        }

      * SCase "NCan".
        unfold nobnd in comp1.
        rw @compute_step_ncompop_ncan2 in comp1.
        remember (compute_step lib (oterm (NCan ncan2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        left.
        exists c1 c2  k1 (S k2) d; dands; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a))
                      [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan2.
        rw Heqc; auto.
        assert ((S k - (k1 + S k2 + 1)) = (k - (k1 + k2 + 1))) as e by lia.
        rw e; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        apply computes_to_exception_in_max_k_steps_can in comp3; sp.

        right; right.
        exists x e k1 (S k2); dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a))
                      [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan2.
        rw Heqc; auto.

      * SCase "Exc".
        simpl in comp1; inversion comp1; subst; GC.
        right; right.
        apply isprogram_exception_implies in isp2; exrepnd; sp; subst.
        apply computes_to_val_or_exc_in_max_k_steps_exc_iff in comp0; subst.
        exists (oterm (Can can1) l) t 0 0; simpl; dands; auto; try lia.
        unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps;
          simpl; dands; auto.
        apply computes_to_exception_in_max_k_steps_exc; sp.
        unfold reduces_in_atmost_k_steps; simpl; auto.

      * SCase "NExc".
        provefalse.
        allsimpl; ginv.
        apply computes_to_val_or_exc_in_max_k_steps_nexc in comp0; sp.

      * SCase "Mrk".
        allsimpl; ginv.

      * SCase "Abs".
        unfold nobnd in comp1.
        rw @compute_step_ncompop_abs2 in comp1.
        remember (compute_step lib (oterm (Abs abs2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        left.
        exists c1 c2  k1 (S k2) d; dands; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a))
                      [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs2.
        rw Heqc; auto.
        assert ((S k - (k1 + S k2 + 1)) = (k - (k1 + k2 + 1))) as e by lia.
        rw e; auto.

        destruct comp0 as [comp0|comp0]; exrepnd; subst.

        apply computes_to_exception_in_max_k_steps_can in comp3; sp.

        right; right.
        exists x e k1 (S k2); dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw <- plus_n_Sm.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a))
                      [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs2.
        rw Heqc; auto.

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_ncan1 in comp1.
      remember (compute_step lib (oterm (NCan ncan1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.

      destruct comp0 as [comp0|comp0]; [|destruct comp0 as [comp0|comp0]];
      exrepnd; subst.

      * left.
        exists c1 c2 (S k1) k2 d; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

      * right; left.
        exists e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

      * right; right.
        exists x e (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

    + Case "Exc".
      simpl in comp1.
      unfold compute_step_catch in comp1; inversion comp1; subst; GC.
      apply computes_to_val_or_exc_in_max_k_steps_exc in comp0; subst.
      right; left.
      apply isprogram_exception_implies in isp1; exrepnd; subst.
      exists t 0; dands; auto; try lia.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "NExc".
      provefalse.
      allsimpl; ginv.
      apply computes_to_val_or_exc_in_max_k_steps_nexc in comp0; sp.

    + Case "Mrk".
      allsimpl; ginv; fold_terms.
      unfold computes_to_val_or_exc_in_max_k_steps in comp0; repnd.
      apply reduces_in_atmost_k_steps_primarg_marker in comp1; subst.
      dorn comp0; inversion comp0.

    + Case "Abs".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_abs1 in comp1.
      remember (compute_step lib (oterm (Abs abs1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.

      destruct comp0 as [comp0|comp0]; [|destruct comp0 as [comp0|comp0]];
      exrepnd; subst.

      * left.
        exists c1 c2 (S k1) k2 d; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.

      * right; left.
        exists e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.

      * right; right.
        exists x e (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.
Qed.
*)

Lemma computes_to_value_implies_val_or_exc {p} :
  forall lib (a b : @NTerm p),
    computes_to_value lib a b
    -> computes_to_val_or_exc lib a b.
Proof.
  introv comp.
  unfold computes_to_val_or_exc, computes_to_val_or_exc_in_max_k_steps.
  unfold computes_to_value, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  left; eauto 3 with slow.
Qed.

Lemma computes_to_exception_implies_val_or_exc {p} :
  forall lib n (a b : @NTerm p),
    computes_to_exception lib n a b
    -> computes_to_val_or_exc lib a (mk_exception n b).
Proof.
  introv comp.
  unfold computes_to_val_or_exc, computes_to_val_or_exc_in_max_k_steps.
  unfold computes_to_exception, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  right; eauto with slow.
Qed.

Lemma isvalue_subst {p} :
  forall t x a,
    isprogram a
    -> (isvalue (subst t x a)
        <=> (isprogram (subst t x a)
             # (iscan t [+] (t = @mk_var p x # isvalue a)))).
Proof.
  introv ispa.
  unfold subst.
  change_to_lsubst_aux4; simpl; allrw app_nil_r;
  try (complete (destruct ispa; rw c; sp)).
  split.

  - intro isv.
    inversion isv as [c bts isp h]; dands; auto.
    destruct t.

    + allunfold @subst; allsimpl; right.
      revert isv h.
      boolvar; intros isv h; auto; subst.
      allrw @isprogram_vterm; sp.

    + allsimpl; GC; subst; sp.

    + destruct o; inversion h; subst; simpl; tcsp.

  - intro h; repnd.
    destruct h as [h|h]; repnd; subst.

    + destruct t; try (complete (inversion h)); allsimpl; eauto 3 with slow.

    + allsimpl.
      revert h0; boolvar; sp.
Qed.

Lemma computes_to_value_can_same {p} :
  forall lib t, (@iscan p t # isprogram t) <=> computes_to_value lib t t.
Proof.
  introv; split; intro k.

  - repnd.
    apply iscan_implies in k0; repndors; exrepnd; subst;
    unfold computes_to_value, reduces_to; dands; eauto 3 with slow;
    exists 0;
    unfold reduces_in_atmost_k_steps; simpl; auto.

  - unfold computes_to_value in k; repnd.
    apply isvalue_implies in k; auto.
Qed.

Lemma if_computes_to_exception_apply {p} :
  forall lib en f a e,
    isprogram f
    -> isprogram a
    -> computes_to_exception lib en (mk_apply f a) e
    -> {v : NVar & {b : @NTerm p & reduces_to lib f (mk_lam v b)}}
       [+] {s : nseq & reduces_to lib f (mk_nseq s) }
       [+] {s : ntseq & reduces_to lib f (mk_ntseq s) }
       [+] computes_to_exception lib en f e.
Proof.
  introv.
  unfold computes_to_exception, reduces_to.
  introv ispf ispa comp; exrepnd.
  revert f a e ispf ispa comp0.
  induction k; simpl; introv ispf ispa comp.

  - inversion comp; subst; GC.

  - apply reduces_in_atmost_k_steps_S in comp; exrepnd.
    simpl in comp1.
    destruct f; try (complete (inversion comp1)).

    { csunf comp1; allsimpl; ginv; allsimpl.
      right; right; left.
      exists n 0; eauto 3 with slow.
      apply reduces_in_atmost_k_steps_0; auto. }

    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      csunf comp1; allsimpl.
      apply compute_step_apply_success in comp1;
        repndors; exrepnd; subst; fold_terms; cpx; GC.
      { left.
        exists v b 0; sp. }
      { right; left.
        exists f 0; sp. }

    + Case "NCan".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd.

      * left.
        exists v b (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; left.
        exists s (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; right; left.
        exists s (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; right; right.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      apply reduces_atmost_exc in comp0.
      inversion comp0; subst.
      right; right; right; exists 0; sp.

    + Case "Abs".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_abs in comp1.
      remember (compute_step_lib lib abs l); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @isprogram_compute_step_lib in Heqc; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd.

      * left.
        exists v b (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; left.
        exists s (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; right; left.
        exists s (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

      * right; right; right.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.
Qed.

Lemma computes_to_value_and_exception_false {p} :
  forall lib en (a v e : @NTerm p),
    computes_to_value lib a v
    -> computes_to_exception lib en a e
    -> False.
Proof.
  introv cv ce.
  unfold computes_to_value in cv; repnd.
  unfold computes_to_exception in ce; repnd.
  apply reduces_to_or with (u := mk_exception en e) in cv0; auto.
  destruct cv0 as [r|r].

  + apply reduces_to_exception in r; subst; sp.
    apply isvalue_exc in cv; sp.

  + apply reduces_to_if_value in r; subst; sp.
    apply isvalue_exc in cv; sp.
Qed.

Lemma lsubst_mk_axiom {p} :
  forall sub, lsubst mk_axiom sub = @mk_axiom p.
Proof. sp. Qed.

Lemma subst_mk_axiom {p} :
  forall v t, subst mk_axiom v t = @mk_axiom p.
Proof. sp. Qed.

Lemma computes_to_exception_raises_exception {p} :
  forall lib a (t e : @NTerm p),
    computes_to_exception lib a t e
    -> raises_exception lib t.
Proof.
  introv comp.
  unfold raises_exception; exists a e; auto.
Qed.

Lemma if_computes_to_exception_cbv0 {p} :
  forall lib a t v u e,
    isprogram t
    -> computes_to_exception lib a (mk_cbv t v u) e
    -> computes_to_exception lib a t e
       [+] {x : @NTerm p
            & computes_to_value lib t x
            # computes_to_exception lib a (subst u v x) e}.
Proof.
  unfold computes_to_exception, reduces_to.
  introv ispt re; exrepnd.
  revert dependent t.
  revert v u e.
  induction k; introv ispt r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    simpl in r1.
    destruct t; try (complete (inversion r1)).

    { csunf r1; allsimpl; ginv; allsimpl.
      right.
      exists (sterm n); dands; eauto 3 with slow. }

    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".
      inversion r1; subst; GC.
      unfold apply_bterm in r0; simpl in r0.
      rw @fold_subst in r0.
      right.
      exists (oterm (Can can) l); dands; sp.
      apply computes_to_value_can_same; sp.
      exists k; auto.

    + Case "NCan".
      unfold mk_cbv, nobnd in r1.
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c.

      * inversion r1; subst; GC; allrw @fold_cbv.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in r0; auto.
        destruct r0 as [r|r]; exrepnd.

        left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; auto.

        right.
        exists x; sp.
        apply computes_to_value_step with (t2 := n); auto.
        exists k0; auto.

      * inversion r1.

    + Case "Exc".
      unfold compute_step_catch in r1; inversion r1; subst; GC.
      left.
      exists k; auto.

    + Case "Abs".
      unfold mk_cbv, nobnd in r1.
      rw @compute_step_ncan_abs in r1.
      remember (compute_step_lib lib abs l); destruct c.

      * inversion r1; subst; GC; allrw @fold_cbv.
        symmetry in Heqc.
        applydup @isprogram_compute_step_lib in Heqc; auto.
        apply IHk in r0; auto.
        destruct r0 as [r|r]; exrepnd.

        left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; auto.

        right.
        exists x; sp.
        apply computes_to_value_step with (t2 := n); auto.
        exists k0; auto.

      * inversion r1.
Qed.

Lemma if_raises_exception_cbv0 {p} :
  forall lib t v u,
    isprogram t
    -> raises_exception lib (mk_cbv t v u)
    -> raises_exception lib t
       [+] {x : @NTerm p & computes_to_value lib t x # raises_exception lib (subst u v x)}.
Proof.
  introv isp re.
  unfold raises_exception in re; exrepnd.
  generalize (if_computes_to_exception_cbv0 lib a t v u e isp re1).
  intro k.
  destruct k as [k|k].
  - left; exists a e; auto.
  - right; exrepnd.
    exists x; dands; auto.
    exists a e; auto.
Qed.

Lemma iscan_compute_step {o} :
  forall lib (t : @NTerm o),
    iscan t
    -> compute_step lib t = csuccess t.
Proof.
  introv isc.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  dopid op as [can|ncan|exc|abs] Case; allsimpl; tcsp.
Qed.

Lemma iscancan_doesnt_raise_an_exception {o} :
  forall lib (t a e : @NTerm o),
    iscan t
    -> computes_to_exception lib a t e
    -> False.
Proof.
  introv isc comp.
  unfold computes_to_exception, reduces_to in comp; exrepnd.
  revert dependent t.
  induction k; introv isc comp.
  - allrw @reduces_in_atmost_k_steps_0; subst; allsimpl; sp.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    rw @iscan_compute_step in comp1; auto; ginv.
    apply IHk in comp0; sp.
Qed.

Lemma raises_exception_can {p} :
  forall lib t, @iscan p t -> raises_exception lib t -> False.
Proof.
  introv isc re.
  unfold raises_exception in re; exrepnd.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  apply iscancan_doesnt_raise_an_exception in re1; tcsp.
Qed.

Lemma compute_step_cbv_ncan {p} :
  forall lib nc bterms v u,
    compute_step lib (mk_cbv (oterm (@NCan p nc) bterms) v u)
    = match compute_step lib (oterm (NCan nc) bterms) with
        | csuccess t => csuccess (mk_cbv t v u)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma compute_step_cbv_abs {p} :
  forall lib x bterms v u,
    compute_step lib (mk_cbv (oterm (@Abs p x) bterms) v u)
    = match compute_step lib (oterm (Abs x) bterms) with
        | csuccess t => csuccess (mk_cbv t v u)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma cbv_raises_exception {p} :
  forall lib a (t : @NTerm p) v u e,
    isprogram t
    -> computes_to_exception lib a t e
    -> computes_to_exception lib a (mk_cbv t v u) e.
Proof.
  unfold computes_to_exception, reduces_to; introv ispt comp; exrepnd.
  revert dependent t.
  revert v u e.
  induction k; introv ispt comp.

  - apply reduces_in_atmost_k_steps_0 in comp; subst.
    exists 1.
    rw @reduces_in_atmost_k_steps_S.
    exists (mk_exception a e); dands; auto.
    apply reduces_in_atmost_k_steps_0; auto.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.

    applydup @preserve_compute_step in comp1;
      try (complete (allrw @isprogram_eq; sp)).
    generalize (IHk v u e u0 comp2 comp0); intro h; exrepnd.

    destruct t; try (complete (inversion comp1)).

    { csunf comp1; allsimpl; ginv; allsimpl.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; ginv. }

    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      simpl in comp1; inversion comp1; subst; GC.
      exists k0; auto.

    + Case "NCan".
      exists (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists (mk_cbv u0 v u); dands; auto.
      rw @compute_step_cbv_ncan.
      rw comp1; auto.

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      exists k0; auto.

    + Case "Abs".
      exists (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists (mk_cbv u0 v u); dands; auto.
      rw @compute_step_cbv_abs.
      rw comp1; auto.
Qed.

Lemma fold_computes_to_exc_max {p} :
  forall lib a k (t e : @NTerm p),
    (compute_at_most_k_steps lib k t = csuccess (mk_exception a e))
    = computes_to_exception_in_max_k_steps lib a t e k.
Proof. sp. Qed.

Lemma no_change_after_value_like {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isvalue_like v1
    -> forall k, compute_at_most_k_steps lib (k+k1) t = csuccess v1.
Proof.
  intros. induction k. simpl. auto.
  rewrite plus_Sn_m. simpl.
  rewrite IHk. apply compute_step_value_like.
  auto.
Qed.

Lemma no_change_after_value_like2 {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isvalue_like v1
    -> forall k, k >= k1 -> compute_at_most_k_steps lib k t = csuccess v1.
Proof.
  introv comp isv x.
  pose proof (no_change_after_value_like lib t k1 v1 comp isv (k - k1)) as h.
  assert(k=(k-k1) + k1) as e by lia.
  rw <- e in h; auto.
Qed.

Lemma reduces_to_eq_val_like {o} :
  forall lib (t v1 v2 : @NTerm o),
    reduces_to lib t v1
    -> reduces_to lib t v2
    -> isvalue_like v1
    -> isvalue_like v2
    -> v1 = v2.
Proof.
  introv r1 r2 isv1 isv2.
  allunfold @reduces_to; exrepnd.
  allunfold @reduces_in_atmost_k_steps.
  pose proof (no_change_after_value_like2 lib t k0 v1 r2 isv1 (k0 + k)) as h1.
  autodimp h1 hyp; try lia.
  pose proof (no_change_after_value_like2 lib t k v2 r0 isv2 (k0 + k)) as h2.
  autodimp h2 hyp; try lia.
  eapply compute_at_most_k_steps_eqp in h2; eauto.
Qed.

Lemma computes_to_exception_eq {p} :
  forall lib a b (t e1 e2 : @NTerm p),
    computes_to_exception lib a t e1
    -> computes_to_exception lib b t e2
    -> e1 = e2 # a = b.
Proof.
  introv comp1 comp2.
  allunfold @computes_to_exception.
  pose proof (reduces_to_eq_val_like
                lib t (mk_exception a e1)
                (mk_exception b e2)) as h.
  repeat (autodimp h hyp); eauto with slow.
  inversion h; subst; auto.
Qed.

Lemma reduces_in_atmost_k_steps_implies_hasvalue {p} :
  forall lib (a b : @NTerm p) k,
    reduces_in_atmost_k_steps lib a b k
    -> iscan b
    -> isprogram b
    -> hasvalue lib a.
Proof.
  introv r isc isp.
  exists b.
  unfold computes_to_value, reduces_to; dands.
  exists k; auto.
  apply isvalue_iff; auto.
Qed.

Lemma reduces_in_atmost_k_steps_implies_raises_exception {p} :
  forall lib (a b : @NTerm p) k,
    reduces_in_atmost_k_steps lib a b k
    -> isexc b
    -> isprogram b
    -> raises_exception lib a.
Proof.
  introv r ise isp.
  apply isexc_implies in ise; auto; exrepnd; subst.
  exists a0 e.
  unfold computes_to_exception, reduces_to.
  exists k; auto.
Qed.

Lemma reduces_in_atmost_k_steps_S2 {p} :
  forall lib (t v : @NTerm p) k,
    reduces_in_atmost_k_steps lib t v (S k)
    <=> {u : @NTerm p
        & reduces_in_atmost_k_steps lib t u k
        # compute_step lib u = csuccess v}.
Proof.
  introv.
  unfold reduces_in_atmost_k_steps.
  rw @compute_at_most_k_steps_S.
  remember (compute_at_most_k_steps lib k t); destruct c;
  split; intro comp; exrepnd.

  - exists n; sp.

  - inversion comp1; subst; GC; auto.

  - inversion comp.

  - inversion comp1.
Qed.

Lemma compute_step_apply_ncan {p} :
  forall lib n l c,
    compute_step lib (mk_apply (oterm (@NCan p n) l) c)
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess f => csuccess (mk_apply f c)
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; csunf; allsimpl; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_apply {p} :
  forall lib k (a b c : @NTerm p),
    reduces_in_atmost_k_steps lib a b k
    -> {k1 : nat & reduces_in_atmost_k_steps lib (mk_apply a c) (mk_apply b c) k1}.
Proof.
  introv comp.
  allunfold @reduces_in_atmost_k_steps; exrepnd.
  generalize (computes_atmost_ksteps_prinarg lib NApply a [nobnd c] k b comp).
  intro h; exrepnd.
  allrw @fold_apply.
  exists j; auto.
Qed.

Lemma computes_to_exception_fix {p} :
  forall lib a (t e : @NTerm p),
    computes_to_exception lib a t e
    -> computes_to_exception lib a (mk_fix t) e.
Proof.
  introv comp.
  allunfold @computes_to_exception.
  allunfold @reduces_to.
  allunfold @reduces_in_atmost_k_steps; exrepnd.
  generalize (computes_atmost_ksteps_prinarg lib NFix t [] k (mk_exception a e) comp0).
  intro h; exrepnd.
  allrw (@fold_nobnd p).
  allrw (@fold_fix p).
  exists (S j); auto.
  rw @compute_at_most_k_steps_S.
  rw h1; sp.
Qed.

Lemma reduces_in_atmost_k_steps_implies_computes_in_kstep {p} :
  forall lib k (a b : @NTerm p),
    reduces_in_atmost_k_steps lib a b k
    -> {k1 : nat $ k1 <= k # computes_in_kstep lib k1 a b}.
Proof.
  induction k; introv r.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    exists 0; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    apply IHk in r0; exrepnd.
    symmetry in r1; apply compute_step_dicot in r1.
    destruct r1 as [r1|r1]; repnd; subst.

    + exists k1; sp.

    + exists (S k1); dands; try lia.
      apply ckcons with (t2 := u); sp.
Qed.

Lemma computes_in_kstep_0 {p} :
  forall lib (t u : @NTerm p), computes_in_kstep lib 0 t u <=> t = u.
Proof.
  introv; split; intro k; subst; auto.
  inversion k; sp.
  constructor.
Qed.

Lemma computes_in_kstep_S {p} :
  forall lib t v k,
    computes_in_kstep lib (S k) t v
    <=> {u : @NTerm p
        & computes_in_1step lib t u
        # computes_in_kstep lib k u v}.
Proof.
  introv.
  split; intro comp; exrepnd.

  - inversion comp; subst.
    exists t2; sp.

  - apply ckcons with (t2 := u); sp.
Qed.

Definition computes_to_alpha_exception {p} lib a (t1 t2 : @NTerm p) :=
  {aa : NTerm
   & {t2a : NTerm
   & computes_to_exception lib aa t1 t2a
   # alpha_eq aa a
   # alpha_eq t2a t2}}.

Lemma reduces_in_atmost_k_steps_implies_reduces_to {p} :
  forall lib (a b : @NTerm p) k,
    reduces_in_atmost_k_steps lib a b k
    -> reduces_to lib a b.
Proof.
  introv r; exists k; auto.
Qed.
Hint Resolve reduces_in_atmost_k_steps_implies_reduces_to : slow.

Lemma computes_to_exception_step {p} :
  forall lib a (t1 t2 t3 : @NTerm p),
    computes_to_exception lib a t2 t3
    -> compute_step lib t1 = csuccess t2
    -> computes_to_exception lib a t1 t3.
Proof.
  introv Hcv Hcs.
  invertsn Hcv.
  apply reduces_to_if_step in Hcs.
  apply reduces_in_atmost_k_steps_implies_reduces_to in Hcv.
  eapply reduces_to_trans in Hcv; eauto.
Qed.

Lemma computes_in_kstep_alpha_implies_exc {p} :
  forall lib a k (t e : @NTerm p),
    nt_wf t
    -> computes_in_kstep_alpha lib k t (mk_exception a e)
    -> computes_to_alpha_exception lib a t e.
Proof.
  induction k as [ | k Hind]; introv wf Hcka; unfolds_base.
  - invertsn Hcka.
    apply alpha_eq_sym in Hcka; apply alpha_eq_exception in Hcka; exrepnd; subst.
    exists a' e'; dands; eauto with slow.
    apply computes_to_exception_refl.
  - inverts Hcka as HH HHH.
    applydup @computes_in_1step_alpha_preserves_nt_wf in HH as wf2; auto.
    apply Hind in HHH; auto.
    invertsn HHH.
    invertsn HHH.
    repnd.
    invertsn HH.
    repnd.
    eapply compute_to_exception_alpha in HHH0; eauto.
    exrepnd.
    rename HHH2 into Hcv.
    invertsn HH0;
    eapply computes_to_exception_step in Hcv; eauto;
    eexists; eexists; dands; eauto with slow.
Qed.

Lemma computes_in_kstep_alpha_preserves_isprogram {p} :
  forall lib k (a b : @NTerm p),
    computes_in_kstep_alpha lib k a b
    -> isprogram a
    -> isprogram b.
Proof.
  induction k; introv comp isp.

  - inversion comp as [? ? ? aeq|]; subst.
    apply alphaeq_preserves_program in aeq.
    apply aeq; sp.

  - inversion comp as [|? ? ? ? ? cstep csteps]; subst.
    apply IHk in csteps; auto.
    apply computes_in_1step_alpha_program in cstep; sp.
Qed.

Lemma computes_step_sleep_ncan {p} :
  forall lib n l,
    compute_step lib (mk_sleep (oterm (@NCan p n) l))
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess t => csuccess (mk_sleep t)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; sp.
Qed.

Lemma computes_step_sleep_abs {p} :
  forall lib o l,
    compute_step lib (mk_sleep (oterm (@Abs p o) l))
    = match compute_step lib (oterm (Abs o) l) with
        | csuccess t => csuccess (mk_sleep t)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; sp.
Qed.

(*
Lemma computes_to_val_or_exc_in_max_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs v,
    computes_to_val_or_exc_in_max_k_steps
      lib
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
      v k
    -> False.
Proof.
  introv h.
  unfold computes_to_val_or_exc_in_max_k_steps in h; repnd.
  apply reduces_in_atmost_k_steps_primarg_marker in h0; subst.
  dorn h; sp.
Qed.
*)

Lemma computes_to_val_or_exc_in_max_k_steps_sleep_implies {p} :
  forall lib k t v,
    computes_to_val_or_exc_in_max_k_steps lib (mk_sleep t) v k
    -> {x : NTerm
        & {m : nat
           & k = S m
           # computes_to_val_or_exc_in_max_k_steps lib t x m
           # ({z : Z & v = mk_axiom # x = @mk_integer p z}
              [+]
              (isexc x # x = v))}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_or_exc_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    dorn comp; inversion comp.

  - rw @computes_to_val_or_exc_in_max_k_steps_S in comp; exrepnd.
    destruct t; try (complete (inversion comp1)).
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      destruct l; try (complete (inversion comp1)).
      destruct can; inversion comp1; subst.
      apply computes_to_val_or_exc_in_max_k_steps_can_iff in comp0; subst.
      exists (@mk_integer p z) k; dands; auto.
      apply computes_to_val_or_exc_in_max_k_steps_can_iff; sp.
      left; exists z; sp.

    + Case "NCan".
      rw @computes_step_sleep_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_or_exc_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      inversion comp1; subst; GC.
      apply computes_to_val_or_exc_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc l) k; dands; auto.
      apply computes_to_val_or_exc_in_max_k_steps_exc_iff; sp.

    + Case "Abs".
      rw @computes_step_sleep_abs in comp1.
      remember (compute_step lib (oterm (Abs abs) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_or_exc_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma computes_step_tuni_ncan {p} :
  forall lib n l,
    compute_step lib (mk_tuni (oterm (@NCan p n) l))
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess t => csuccess (mk_tuni t)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; sp.
Qed.

Lemma computes_step_tuni_abs {p} :
  forall lib o l,
    compute_step lib (mk_tuni (oterm (@Abs p o) l))
    = match compute_step lib (oterm (Abs o) l) with
        | csuccess t => csuccess (mk_tuni t)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; sp.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_tuni_implies {p} :
  forall lib k t v,
    computes_to_val_or_exc_in_max_k_steps lib (mk_tuni t) v k
    -> {x : NTerm
        & {m : nat
           & k = S m
           # computes_to_val_or_exc_in_max_k_steps lib t x m
           # ({n : nat & v = mk_uni n # x = @mk_integer p (Z.of_nat n)}
              [+]
              (isexc x # x = v))}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_or_exc_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    dorn comp; inversion comp.

  - rw @computes_to_val_or_exc_in_max_k_steps_S in comp; exrepnd.
    destruct t; try (complete (inversion comp1)).
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      destruct l; try (complete (inversion comp1)).
      csunf comp1; allsimpl.
      unfold compute_step_tuni in comp1; simpl in comp1.
      destruct can; allsimpl; try (complete (inversion comp1)).
      destruct (Z_le_gt_dec 0 z); inversion comp1; subst; GC.
      apply computes_to_val_or_exc_in_max_k_steps_can_iff in comp0; subst.
      exists (@mk_integer p z) k; dands; auto.
      apply computes_to_val_or_exc_in_max_k_steps_can_iff; sp.
      left; exists (Z.to_nat z); sp.
      rw Znat.Z2Nat.id; sp.

    + Case "NCan".
      rw @computes_step_tuni_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_or_exc_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      inversion comp1; subst; GC.
      apply computes_to_val_or_exc_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc l) k; dands; auto.
      apply computes_to_val_or_exc_in_max_k_steps_exc_iff; sp.

    + rw @computes_step_tuni_abs in comp1.
      remember (compute_step lib (oterm (Abs abs) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_or_exc_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma wf_exception_implies {p} :
  forall (bterms : list (@BTerm p)),
    wf_term (oterm Exc bterms)
    -> {a : NTerm
        $ {t : NTerm
        $ bterms = [bterm [] a, bterm [] t]
        # wf_term a
        # wf_term t}}.
Proof.
  introv isp.
  allrw @wf_oterm_iff; repnd; allsimpl.
  repeat (destruct bterms; allsimpl; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in isp0; allsimpl.
  destruct l1; destruct l2; ginv.
  pose proof (isp (bterm [] t1)) as w1; autodimp w1 hyp.
  pose proof (isp (bterm [] t2)) as w2; autodimp w2 hyp.
  allrw @wf_bterm_iff.
  eexists; eexists; dands; eauto.
Qed.

Definition computes_to_can_in_max_k_steps {p} lib (k: nat) (a av : @NTerm p) :=
  reduces_in_atmost_k_steps lib a av k
  # iscan av.

Lemma computes_to_can_in_max_k_steps_0 {p} :
  forall lib (a b : @NTerm p),
    computes_to_can_in_max_k_steps lib 0 a b <=> (a = b # iscan b).
Proof.
  unfold computes_to_can_in_max_k_steps, reduces_in_atmost_k_steps.
  simpl; introv; split; intro k; repnd.
  inversion k0; auto.
  subst; dands; auto.
Qed.

Lemma computes_to_can_in_max_k_steps_S {p} :
  forall lib t v k,
    computes_to_can_in_max_k_steps lib (S k) t v
    <=> {u : @NTerm p
        & compute_step lib t = csuccess u
        # computes_to_can_in_max_k_steps lib k u v}.
Proof.
  introv; split; intro comp.

  - allunfold @computes_to_can_in_max_k_steps; repnd.
    apply reduces_in_atmost_k_steps_S in comp0; exrepnd.
    exists u; sp.

  - exrepnd.
    allunfold @computes_to_can_in_max_k_steps; repnd; dands; auto.
    rw @reduces_in_atmost_k_steps_S.
    exists u; sp.
Qed.

Lemma wf_compute_step_lib {o} :
  forall lib (x : opabs) (bs : list BTerm) (t : @NTerm o),
    wf_term (oterm (Abs x) bs)
    -> compute_step_lib lib x bs = csuccess t
    -> wf_term t.
Proof.
  introv wa comp.
  pose proof (compute_step_preserves_wf lib (oterm (Abs x) bs) t) as h.
  csunf h; allsimpl; repeat (autodimp h hyp).
Qed.

Lemma computes_to_val_like_in_max_k_steps_S {p} :
  forall lib t v k,
    computes_to_val_like_in_max_k_steps lib t v (S k)
    <=> {u : @NTerm p
        & compute_step lib t = csuccess u
        # computes_to_val_like_in_max_k_steps lib u v k}.
Proof.
  introv; split; intro comp.

  - allunfold @computes_to_val_like_in_max_k_steps; repnd.
    apply reduces_in_atmost_k_steps_S in comp0; exrepnd.
    exists u; sp.

  - exrepnd.
    allunfold @computes_to_val_like_in_max_k_steps; repnd; dands; auto.
    rw @reduces_in_atmost_k_steps_S.
    exists u; sp.
Qed.

Lemma computes_to_val_like_in_max_k_steps_exc_iff {p} :
  forall lib bterms (t : @NTerm p) k,
    computes_to_val_like_in_max_k_steps lib (oterm Exc bterms) t k
    <=> t = oterm Exc bterms.
Proof.
  introv; split; intro comp; subst.
  apply computes_to_val_like_in_max_k_steps_exc in comp; auto.
  unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps.
  dands; try (complete (right; sp)).
  induction k; simpl; sp.
  rw IHk; simpl; sp.
Qed.

Lemma computes_to_val_like_in_max_k_steps_arith_implies {p} :
  forall lib k a n1 n2 v,
    wf_term n1
    -> wf_term n2
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
         v
         k
    -> {nv1 , nv2 : Z
       $ { k1 , k2 : nat
         $ v = mk_integer (get_arith_op a nv1 nv2)
         # k1+k2+1 <= k
         # computes_to_value_in_max_k_steps lib k1 n1 (mk_integer nv1)
         # computes_to_value_in_max_k_steps lib k2 n2 (mk_integer nv2)
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
              (oterm (NCan (NArithOp a))
                     [bterm [] (mk_integer nv1),
                      bterm [] (mk_integer nv2)])
              (k1+k2)
       }}
       [+]
       {en, e : NTerm
        $ { k1 : nat
        $ k1 + 1 <= k
        # v = mk_exception en e
        # computes_to_exception_in_max_k_steps lib en n1 e k1
        # reduces_in_atmost_k_steps lib
             (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
             (oterm (NCan (NArithOp a))
                    [bterm [] v,
                     bterm [] n2])
             k1
       }}
       [+]
       {en, e : @NTerm p
        $ {z : Z
        $ { k1 , k2 : nat
        $ k1+k2+1 <= k
         # v = mk_exception en e
         # computes_to_value_in_max_k_steps lib k1 n1 (mk_integer z)
         # computes_to_exception_in_max_k_steps lib en n2 e k2
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NArithOp a)) [bterm [] n1, bterm [] n2])
              (oterm (NCan (NArithOp a))
                     [bterm [] (mk_integer z),
                      bterm [] v])
              (k1+k2)
       }}}.
Proof.
  induction k; introv isp1 isp2 comp.

  - destruct comp as [r is].
    inversion r; subst.
    unfold isvalue_like in is; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1)).
    dopid o as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (csunf comp1; allsimpl; dcwf h));[].
      dopid o as [can2|ncan2|exc2|abs2] SCase.

      * SCase "Can".
        csunf comp1; simpl in comp1.
        dcwf h; allsimpl;[].
        apply compute_step_arithop_success_can_can in comp1; exrepnd; subst; GC.
        allapply @get_param_from_cop_pki; subst.
        apply computes_to_val_like_in_max_k_steps_can in comp0; subst.
        left.
        exists n1 n2 0 0; simpl; dands; auto; try lia;
        try (rw @computes_to_value_in_max_k_steps_0; dands; eauto with slow).
        rw @reduces_in_atmost_k_steps_0; auto.

      * SCase "NCan".
        rw @compute_step_narithop_ncan2 in comp1.
        dcwf h;[].
        remember (compute_step lib (oterm (NCan ncan2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @compute_step_preserves_wf in Heqc; auto.
        apply IHk in comp0; auto.

        repndors; exrepnd; subst.

        { left.
          exists nv1 nv2 k1 (S k2); dands; auto; try lia.
          rw @computes_to_value_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_ncan2.
          dcwf h;[].
          rw Heqc; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp3; sp. }

        { right; right.
          exists en e z k1 (S k2); dands; auto; try lia.
          rw @computes_to_exception_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_ncan2.
          dcwf h;[].
          rw Heqc; auto. }

      * SCase "Exc".
        csunf comp1; simpl in comp1; inversion comp1; subst; GC.
        dcwf h;[]; ginv.
        right; right.
        apply wf_exception_implies in isp2; exrepnd; sp; subst.
        apply computes_to_val_like_in_max_k_steps_exc_iff in comp0; subst;[].
        unfold ca_wf_def in Heqh; exrepnd; subst.
        exists a0 t i 0 0; simpl; dands; auto; try lia.
        { unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps;
          simpl; dands; eauto 3 with slow. }
        { apply computes_to_exception_in_max_k_steps_exc; sp. }
        { unfold reduces_in_atmost_k_steps; simpl; auto. }

      * SCase "Abs".
        rw @compute_step_narithop_abs2 in comp1.
        dcwf h;[].
        remember (compute_step_lib lib abs2 l0);
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @wf_compute_step_lib in Heqc; auto.
        apply IHk in comp0; auto.

        repndors; exrepnd; subst.

        { left.
          exists nv1 nv2 k1 (S k2); dands; auto; try lia.
          rw @computes_to_value_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_abs2.
          dcwf h;[].
          rw Heqc; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp3; sp. }

        { right; right.
          exists en e z k1 (S k2); dands; auto; try lia.
          rw @computes_to_exception_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NArithOp a))
                        [bterm [] (oterm (Can can1) l), bterm [] n]); dands; auto.
          rw @compute_step_narithop_abs2.
          dcwf h;[].
          rw Heqc; auto. }

    + Case "NCan".
      rw @compute_step_narithop_ncan1 in comp1.
      remember (compute_step lib (oterm (NCan ncan1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @compute_step_preserves_wf in Heqc; auto.
      apply IHk in comp0; auto.

      repndors; exrepnd; subst.

      * left.
        exists nv1 nv2 (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); sp.
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]).
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

      * right; right.
        exists en e z (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); dands; auto.
        rw @compute_step_narithop_ncan1; rw Heqc; auto.

    + Case "Exc".
      csunf comp1; simpl in comp1.
      unfold compute_step_catch in comp1; inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right; left.
      apply wf_exception_implies in isp1; exrepnd; subst.
      exists a0 t 0; dands; auto; try lia.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      rw @compute_step_narithop_abs1 in comp1.
      remember (compute_step_lib lib abs1 l);
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @wf_compute_step_lib in Heqc; auto.
      apply IHk in comp0; auto.

      repndors; exrepnd; subst.

      * left.
        exists nv1 nv2 (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); sp.
        rw @compute_step_narithop_abs1; rw Heqc; auto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]).
        rw @compute_step_narithop_abs1; rw Heqc; auto.

      * right; right.
        exists en e z (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_value_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NArithOp a)) [bterm [] n, bterm [] n2]); dands; auto.
        rw @compute_step_narithop_abs1; rw Heqc; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_comp_implies {p} :
  forall lib k a n1 n2 n3 n4 v,
    wf_term n1
    -> wf_term n2
    -> wf_term n3
    -> wf_term n4
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
         v
         k
    -> {pk1, pk2 : param_kind
       $ { k1 , k2 : nat
       $ { d : bool
         $ k1+k2+1 <= k
         # computes_to_can_in_max_k_steps lib k1 n1 (pk2term pk1)
         # computes_to_can_in_max_k_steps lib k2 n2 (pk2term pk2)
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd (pk2term pk1),
                      nobnd (pk2term pk2),
                      nobnd n3,
                      nobnd n4])
              (k1+k2)
         # computes_to_val_like_in_max_k_steps lib
                   (if d then n3 else n4)
                   v
                   (k - (k1 + k2 + 1))
         # ({i1, i2 : Z
             $ a = CompOpLess
             # pk1 = PKi i1
             # pk2 = PKi i2
             # d = if Z_lt_le_dec i1 i2 then true else false}
            [+]
            (a = CompOpEq # d = if param_kind_deq pk1 pk2 then true else false))
       }}}
       [+]
       {en, e : NTerm
       $ { k1 : nat
         $ k1 + 1 <= k
         # v = mk_exception en e
         # computes_to_exception_in_max_k_steps lib en n1 e k1
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd v,
                      nobnd n2,
                      nobnd n3,
                      nobnd n4])
              k1
       }}
       [+]
       {en, e : @NTerm p
       $ {pk : param_kind
       $ { k1 , k2 : nat
         $ k1+k2+1 <= k
         # v = mk_exception en e
         # computes_to_can_in_max_k_steps lib k1 n1 (pk2term pk)
         # ({i : Z & a = CompOpLess # pk = PKi i}
            [+] a = CompOpEq)
         # computes_to_exception_in_max_k_steps lib en n2 e k2
         # reduces_in_atmost_k_steps lib
              (oterm (NCan (NCompOp a)) [nobnd n1,nobnd n2,nobnd n3,nobnd n4])
              (oterm (NCan (NCompOp a))
                     [nobnd (pk2term pk),
                      nobnd v,
                      nobnd n3,
                      nobnd n4])
              (k1+k2)
       }}}.
Proof.
  induction k; introv wf1 wf2 wf3 wf4 comp.

  - destruct comp as [r is].
    inversion r; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1));[].
    dopid o as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (csunf comp1; allsimpl; dcwf h));[].
      dopid o as [can2|ncan2|exc2|abs2] SCase.

      * SCase "Can".
        csunf comp1; simpl in comp1.
        dcwf h; allsimpl;[].
        apply compute_step_compop_success_can_can in comp1; exrepnd; subst; ginv.
        repndors; exrepnd; subst;
        allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.

        {
          left.
          exists (@PKi p n1) (@PKi p n2) 0 0 (if Z_lt_le_dec n1 n2 then true else false);
            simpl; dands; auto; try lia;
            allrw @computes_to_can_in_max_k_steps_0;
            allrw @reduces_in_atmost_k_steps_0;
            dands; eauto 3 with slow.
          { boolvar; allrw minus0; auto. }
          left; exists n1 n2; dands; auto.
        }

        {
          left.
          allrw <- @pk2term_eq.
          exists pk1 pk2 0 0 (if param_kind_deq pk1 pk2 then true else false);
            simpl; dands; auto; try lia;
            allrw @computes_to_can_in_max_k_steps_0;
            allrw @reduces_in_atmost_k_steps_0;
            dands; eauto 3 with slow.
          allrw minus0; boolvar; tcsp.
        }

      * SCase "NCan".
        unfold nobnd in comp1.
        rw @compute_step_ncompop_ncan2 in comp1.
        dcwf h;allsimpl;[].
        remember (compute_step lib (oterm (NCan ncan2) l0));
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @compute_step_preserves_wf in Heqc; auto;[].
        apply IHk in comp0; auto.

        repndors; exrepnd; subst.

        { left.
          exists pk1 pk2 k1 (S k2) d; dands; auto; try lia.
          - rw @computes_to_can_in_max_k_steps_S.
            exists n; sp.
          - rw <- plus_n_Sm.
            rw @reduces_in_atmost_k_steps_S.
            exists (oterm (NCan (NCompOp a))
                          [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
            unfold nobnd.
            rw @compute_step_ncompop_ncan2.
            dcwf h;[].
            rw Heqc; auto.
          - assert (k1 + S k2 + 1 = S (k1 + k2 + 1)) as e by lia.
            rw e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp3; sp. }

        { right; right.
          exists en e pk k1 (S k2); dands; auto; try lia.
          rw @computes_to_exception_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NCompOp a))
                        [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
          unfold nobnd.
          rw @compute_step_ncompop_ncan2.
          dcwf h;[].
          rw Heqc; auto. }

      * SCase "Exc".
        csunf comp1; simpl in comp1; inversion comp1; subst; GC.
        dcwf h;ginv; allsimpl;[].
        right; right.
        apply wf_exception_implies in wf2; exrepnd; tcsp; subst; fold_terms.
        apply computes_to_val_like_in_max_k_steps_exc_iff in comp0; subst.
        unfold co_wf_def in Heqh; exrepnd; subst.
        allrw @get_param_from_cop_some; subst.
        exists a0 t pk 0 0; simpl; dands; auto; try lia.
        { unfold computes_to_can_in_max_k_steps, reduces_in_atmost_k_steps;
          simpl; dands; auto; allrw @pk2term_eq; auto. }
        { repndors; exrepnd; subst; tcsp; left; eexists; dands; eauto. }
        { apply computes_to_exception_in_max_k_steps_exc; sp. }
        { unfold reduces_in_atmost_k_steps; simpl; auto; allrw @pk2term_eq; auto. }

      * SCase "Abs".
        unfold nobnd in comp1.
        rw @compute_step_ncompop_abs2 in comp1.
        dcwf h;allsimpl;[].
        remember (compute_step_lib lib abs2 l0);
          destruct c; inversion comp1; subst; GC.
        symmetry in Heqc.
        applydup @wf_compute_step_lib in Heqc; auto;[].
        apply IHk in comp0; auto.

        repndors; exrepnd; subst.

        { left.
          exists pk1 pk2  k1 (S k2) d; dands; auto; try lia.
          rw @computes_to_can_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NCompOp a))
                        [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
          unfold nobnd.
          rw @compute_step_ncompop_abs2.
          dcwf h;[].
          rw Heqc; auto.
          assert (k1 + S k2 + 1 = S (k1 + k2 + 1)) as e by lia.
          rw e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp3; sp. }

        { right; right.
          exists en e pk k1 (S k2); dands; auto; try lia.
          rw @computes_to_exception_in_max_k_steps_S.
          exists n; sp.
          rw <- plus_n_Sm.
          rw @reduces_in_atmost_k_steps_S.
          exists (oterm (NCan (NCompOp a))
                        [bterm [] (oterm (Can can1) l),nobnd n,nobnd n3,nobnd n4]); dands; auto.
          unfold nobnd.
          rw @compute_step_ncompop_abs2.
          dcwf h;[].
          rw Heqc; auto. }

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_ncan1 in comp1.
      remember (compute_step lib (oterm (NCan ncan1) l));
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @compute_step_preserves_wf in Heqc; auto.
      apply IHk in comp0; auto.

      repndors; exrepnd; subst.

      * left.
        exists pk1 pk2 (S k1) k2 d; dands; simpl; auto; try lia.
        rw @computes_to_can_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

      * right; right.
        exists en e pk (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_can_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_ncan1; rw Heqc; auto.

    + Case "Exc".
      csunf comp1; simpl in comp1.
      unfold compute_step_catch in comp1; inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right; left.
      apply wf_exception_implies in wf1; exrepnd; subst.
      exists a0 t 0; dands; auto; try lia.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_abs1 in comp1.
      remember (compute_step_lib lib abs1 l);
        destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @wf_compute_step_lib in Heqc; auto.
      apply IHk in comp0; auto.

      repndors; exrepnd; subst.

      * left.
        exists pk1 pk2 (S k1) k2 d; dands; simpl; auto; try lia.
        rw @computes_to_can_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try lia.
        rw @computes_to_exception_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]).
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.

      * right; right.
        exists en e pk (S k1) k2; dands; simpl; auto; try lia.
        rw @computes_to_can_in_max_k_steps_S.
        exists n; sp.
        rw @reduces_in_atmost_k_steps_S.
        exists (oterm (NCan (NCompOp a)) [nobnd n,nobnd n2,nobnd n3,nobnd n4]); dands; auto.
        unfold nobnd.
        rw @compute_step_ncompop_abs1; rw Heqc; auto.
Qed.

Lemma computes_to_value_mk_less {o} :
  forall lib (a b c d v : @NTerm o),
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_value lib (mk_less a b c d) v
    -> {k1 : Z
        & {k2 : Z
        & reduces_to lib a (mk_integer k1)
        # reduces_to lib b (mk_integer k2)
        # (((k1 < k2)%Z # computes_to_value lib c v)
           [+]
           ((k2 <= k1)%Z # computes_to_value lib d v)
          )}}.
Proof.
  introv wfa wfb wfc wfd hv.
  unfold computes_to_value in hv; repnd.
  unfold reduces_to in hv0; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpLess a b c d v) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv;
  try (complete (provefalse; subst; allapply @isvalue_exc; sp));[].

  allunfold @spcan; fold_terms.
  allunfold @computes_to_can_in_max_k_steps; repnd.
  exists i1 i2; dands; eauto with slow.
  boolvar.
  - left; dands; auto.
    allunfold @computes_to_val_like_in_max_k_steps; repnd.
    unfold computes_to_value; dands; auto.
    exists (k - (k1 + k2 + 1)); auto.
  - right; dands; auto.
    allunfold @computes_to_val_like_in_max_k_steps; repnd.
    unfold computes_to_value; dands; auto.
    exists (k - (k1 + k2 + 1)); auto.
Qed.

Lemma hasvalue_mk_less {o} :
  forall lib (a b c d : @NTerm o),
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> hasvalue lib (mk_less a b c d)
    -> {k1 : Z
        & {k2 : Z
        & reduces_to lib a (mk_integer k1)
        # reduces_to lib b (mk_integer k2)
        # (((k1 < k2)%Z # hasvalue lib c)
           [+]
           ((k2 <= k1)%Z # hasvalue lib d)
          )}}.
Proof.
  introv wfa wfb wfc wfd hv.
  unfold hasvalue in hv; exrepnd.
  apply computes_to_value_mk_less in hv0; auto.
  exrepnd.
  exists k1 k2; dands; auto.
  repndors; repnd;[left|right]; dands; auto; exists t'; auto.
Qed.

Lemma isprog_implies_wf {o} :
  forall (t : @NTerm o), isprog t -> wf_term t.
Proof.
  introv isp.
  apply isprogram_implies_wf; apply isprogram_eq; auto.
Qed.
Hint Resolve isprog_implies_wf : slow.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
