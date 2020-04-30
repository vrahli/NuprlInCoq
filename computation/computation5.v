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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export computation_mark.


Lemma computes_to_val_like_iff_hasvalue_like {o} :
  forall lib (t : @NTerm o),
    hasvalue_like lib t <=> {v : NTerm & computes_to_val_like lib t v}.
Proof.
  introv; unfold hasvalue_like, computes_to_val_like, reduces_to, computes_to_val_like_in_max_k_steps;
  split; intro k; exrepnd.
  - exists v k; sp.
  - exists v; sp.
    exists k; sp.
Qed.

Lemma isvalue_like_isvalue {o} :
  forall t : @NTerm o,
    isvalue t -> isvalue_like t.
Proof.
  introv isv.
  inversion isv; subst; eauto with slow.
Qed.
Hint Resolve isvalue_like_isvalue : slow.

Lemma hasvalue_like_if_hasvalue {o} :
  forall lib (t : @NTerm o),
    hasvalue lib t
    -> hasvalue_like lib t.
Proof.
  introv hv.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  exists t'; dands; eauto with slow.
Qed.
Hint Resolve hasvalue_like_if_hasvalue : slow.

Lemma hasvalue_like_if_raises_exception {o} :
  forall lib (t : @NTerm o),
    raises_exception lib t
    -> hasvalue_like lib t.
Proof.
  introv hv.
  unfold raises_exception in hv; exrepnd.
  unfold computes_to_exception in hv1; repnd.
  eexists; dands; eauto with slow.
Qed.
Hint Resolve hasvalue_like_if_raises_exception : slow.

(*
Lemma reduces_in_atmost_k_steps_implies_marks {p} :
  forall lib (a b : @NTerm p) k,
    reduces_in_atmost_k_steps lib a b k
    -> ismrk lib b
    -> isprogram b
    -> marks lib a.
Proof.
  introv r ism isp.
  apply ismrk_implies in ism; auto; exrepnd; subst.
  exists s.
  unfold computes_to_marker, reduces_to.
  exists k; auto.
Qed.
*)

(*
Lemma marker_in_atmost_k_steps_alpha {p} :
  forall lib (t1 t2 : @NTerm p),
    alpha_eq t1 t2
    -> forall k m,
         computes_to_marker_in_max_k_steps lib t1 m k
         -> computes_to_marker_in_max_k_steps lib t2 m k.
Proof.
  introv Hal.
  introv.
  revert m t1 t2 Hal.
  induction k as [| k Hind]; introv aeq comp;
  allunfold @computes_to_marker_in_max_k_steps; repnd; dands; auto.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    apply alpha_eq_marker in aeq; exrepnd; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eapply compute_step_alpha in comp0; eauto; exrepnd.
    pose proof (Hind m u t2') as h.
    repeat (autodimp h hyp); repnd; GC.
    eexists; dands; eauto.
Qed.

Theorem compute_to_marker_alpha {p} :
  forall lib (t1 t2 : @NTerm p) m,
    alpha_eq t1 t2
    -> computes_to_marker lib t1 m
    -> computes_to_marker lib t2 m.
Proof.
  introv aeq comp.
  allunfold @computes_to_marker; allunfold @reduces_to; exrepnd.
  pose proof (marker_in_atmost_k_steps_alpha lib t1 t2 aeq k m) as h.
  unfold computes_to_marker_in_max_k_steps in h.
  autodimp h hyp; repnd.
  eexists; dands; eauto.
Qed.
 *)

Lemma reduces_to_if_split2 {p} :
  forall lib (t : @NTerm p) u v,
  compute_step lib t = csuccess u
  -> reduces_to lib u v
  -> reduces_to lib t v.
Proof.
  unfold reduces_to; sp; exists (S k).
  rw @reduces_in_atmost_k_steps_S.
  exists u; sp.
Qed.

Lemma reduces_to_if_split3 {p} :
  forall lib (t : @NTerm p) u v,
  computes_in_1step lib t u
  -> reduces_to lib u v
  -> reduces_to lib t v.
Proof.
  introv c r.
  inversion c; subst; clear c;
    eapply reduces_to_if_split2; eauto.
Qed.

(*
Lemma computes_in_kstep_alpha_implies_mrk {p} :
  forall lib k (t : @NTerm p) m,
    is_mrk lib m
    -> computes_in_kstep_alpha lib k t (mk_marker m)
    -> computes_to_marker lib t m.
Proof.
  induction k as [ | k Hind]; introv ism Hcka; unfolds_base; dands; auto.
  - invertsn Hcka.
    apply alpha_eq_sym in Hcka; apply alpha_eq_marker in Hcka; exrepnd; subst.
    apply reduces_to_symm.
  - inverts Hcka as HH HHH.
    apply Hind in HHH; auto.
    invertsn HH; repnd.
    apply (compute_to_marker_alpha _ _ x) in HHH; auto.
    allunfold @computes_to_marker; repnd.
    eapply reduces_to_if_split3; eauto.
Qed.

Lemma compute_to_marker_mrk {o} :
  forall (lib : @library o) m,
    is_mrk lib m -> computes_to_marker lib (mk_marker m) m.
Proof.
  introv ism; unfold computes_to_marker; dands; auto.
  exists 0.
  rw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma computes_to_marker_alpha {p} :
  forall lib (t1 t2 : @NTerm p) m,
    alpha_eq t1 t2
    -> computes_to_marker lib t1 m
    -> computes_to_marker lib t2 m.
Proof.
  introv aeq comp.
  unfold computes_to_marker, reduces_to in comp; exrepnd.
  unfold computes_to_marker; dands; auto.
  exists k.
  revert dependent t2.
  revert dependent t1.
  induction k; introv r aeq.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allrw @alpha_eq_marker; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eapply compute_step_alpha in r1; eauto; exrepnd.
    exists t2'; dands; auto.
    eapply IHk; eauto.
Qed.

Lemma reduces_to_computes_to_marker {p} :
  forall lib a b m,
    @reduces_to p lib a b
    -> computes_to_marker lib b m
    -> computes_to_marker lib a m.
Proof.
  introv redto compex.
  allunfold @computes_to_marker; repnd; dands; auto.
  eapply reduces_to_trans; eauto.
Qed.

Lemma reduces_to_marker_eq {p} :
  forall lib (t u : @NTerm p) m,
    computes_to_marker lib t m
    -> reduces_to lib t u
    -> computes_to_marker lib u m.
Proof.
  unfold computes_to_marker; introv Hcv Hcr; repnd; dands; auto.
  apply @reduces_to_or with (u := u) in Hcv0; auto.
  repndors; tcsp.
  apply reduces_to_marker in Hcv0; auto; subst.
  apply reduces_to_symm.
Qed.

Lemma exception_doesnt_mark {o} :
  forall lib a (e : @NTerm o) m,
    computes_to_marker lib (mk_exception a e) m -> False.
Proof.
  introv comp.
  unfold computes_to_marker, reduces_to in comp; exrepnd.
  induction k.
  - allrw @reduces_in_atmost_k_steps_0; ginv.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl; ginv; sp.
Qed.
*)

Definition mk_vid {p} (v : NVar) : @NTerm p := mk_lam v (mk_var v).

Lemma reduces_in_atmost_k_steps_apply_vid {o} :
  forall lib (t : @NTerm o) v u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps lib (mk_apply (mk_vid v) t) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps lib t u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; allsimpl; ginv.
    unfold apply_bterm, lsubst in r0; allsimpl; boolvar; auto.
Qed.

Lemma reduces_in_atmost_k_steps_vbot {o} :
  forall lib v (u : @NTerm o) k,
    isvalue_like u
    -> reduces_in_atmost_k_steps lib (mk_vbot v) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv; auto; fold_terms.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply isvalue_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_apply_vid in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma reduces_to_vbot_if_isvalue_like {o} :
  forall lib v (u : @NTerm o),
    isvalue_like u
    -> reduces_to lib (mk_vbot v) u
    -> False.
Proof.
  introv isv r.
  unfold reduces_to in r; exrepnd.
  apply reduces_in_atmost_k_steps_vbot in r0; sp.
Qed.
