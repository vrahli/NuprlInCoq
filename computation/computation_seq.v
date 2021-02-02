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


Require Export computation6.


Definition computes_to_seq {o} lib (t : @NTerm o) f :=
  reduces_to lib t (mk_ntseq f).

Notation "t1 =v>( lib ) t2" := (computes_to_value lib t1 t2) (at level 99).
Notation "t1 =e>( a , lib ) t2" := (computes_to_exception lib a t1 t2) (at level 99).
Notation "t1 =e>( lib ) t2" := (computes_to_exception lib None t1 t2) (at level 99).
Notation "t =s>( lib ) f" := (computes_to_seq lib t f) (at level 99).
Notation "t =m>( lib ) m" := (computes_to_marker lib t m) (at level 99).


Lemma reduces_in_atmost_k_steps_eapply_sterm_to_isvalue_like {o} :
  forall lib (f : @ntseq o) v k a,
    reduces_in_atmost_k_steps lib (mk_eapply (mk_ntseq f) a) v k
    -> isvalue_like v
    -> {n : nat
        & {i : nat
        & {j : nat
        & i + j < k
        # reduces_in_atmost_k_steps lib a (mk_nat n) i
        # reduces_in_atmost_k_steps lib (f n) v j }}}
       [+] {j : nat & j < k # reduces_in_atmost_k_steps lib a v j # isexc v}.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; ginv.
      left.
      exists n 0 k; simpl; dands; auto.
      apply reduces_in_atmost_k_steps_0; auto.

    + apply isexc_implies2 in comp2; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      right; exists 0; dands; eauto 3 with slow; try omega.
      apply reduces_in_atmost_k_steps_refl; eauto 3 with slow.

    + apply IHk in comp0; auto.
      repndors; exrepnd.

      * left; exists n (S i) j; dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

      * right; exists (S j); dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_eapply_lam_to_isvalue_like {o} :
  forall lib x (b : @NTerm o) v k a,
    reduces_in_atmost_k_steps lib (mk_eapply (mk_lam x b) a) v k
    -> isvalue_like v
    -> {c : NTerm
        & {i : nat
        & {j : nat
        & i + j < k
        # iscan c
        # reduces_in_atmost_k_steps lib a c i
        # reduces_in_atmost_k_steps lib (subst b x c) v j }}}
       [+] {j : nat & j < k # reduces_in_atmost_k_steps lib a v j # isexc v}.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; ginv.
      left.
      exists arg2 0 k; simpl; dands; auto.
      apply reduces_in_atmost_k_steps_0; auto.

    + apply isexc_implies2 in comp2; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      right; exists 0; dands; eauto 3 with slow; try omega.
      apply reduces_in_atmost_k_steps_refl; eauto 3 with slow.

    + apply IHk in comp0; auto.
      repndors; exrepnd.

      * left; exists c (S i) j; dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

      * right; exists (S j); dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_eapply_nseq_to_isvalue_like {o} :
  forall lib s v k (a : @NTerm o),
    reduces_in_atmost_k_steps lib (mk_eapply (mk_nseq s) a) v k
    -> isvalue_like v
    -> {n : nat
        & {i : nat
        & i < k
        # reduces_in_atmost_k_steps lib a (mk_nat n) i
        # v = mk_nat (s n) }}
       [+] {j : nat & j < k # reduces_in_atmost_k_steps lib a v j # isexc v}.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      left.
      exists n 0; dands; auto; try omega.
      apply reduces_in_atmost_k_steps_0; auto.

    + apply isexc_implies2 in comp2; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      right; exists 0; dands; eauto 3 with slow; try omega.
      apply reduces_in_atmost_k_steps_refl; eauto 3 with slow.

    + apply IHk in comp0; auto.
      repndors; exrepnd.

      * left; exists n (S i); dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

      * right; exists (S j); dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma isprogram_sterm_implies_isprogram_apply {o} :
  forall (f : @ntseq o) n, isprogram (sterm f) -> isprogram (f n).
Proof.
  introv isp.
  inversion isp as [cl wf].
  inversion wf as [|? imp|]; subst; clear wf.
  pose proof (imp n) as h; clear imp; repnd.
  constructor; auto.
Qed.
Hint Resolve isprogram_sterm_implies_isprogram_apply : slow.

Lemma eapply_wf_def_lam {o} :
  forall v (b : @NTerm o), eapply_wf_def (mk_lam v b).
Proof.
  introv; right; right; eexists; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_lam : slow.

Lemma eapply_wf_def_nseq {o} :
  forall (s : nseq), @eapply_wf_def o (mk_nseq s).
Proof.
  introv; right; left; eexists; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_nseq : slow.

Lemma implies_eapply_red_aux {o} :
  forall lib (t a v : @NTerm o),
    eapply_wf_def t
    -> reduces_to lib a v
    -> reduces_to lib (mk_eapply t a) (mk_eapply t v).
Proof.
  introv wf comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.
  revert dependent a.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup IHk in comp0.
    destruct a as [w|g|op bs].

    + csunf comp1; allsimpl; ginv.

    + csunf comp1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

    + dopid op as [can|ncan|exc|abs] Case.

      * Case "Can".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

      * eapply reduces_to_if_split2;[|exact comp2].
        unfold mk_eapply; rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow.
        rw comp1; auto.

      * Case "Exc".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

      * eapply reduces_to_if_split2;[|exact comp2].
        unfold mk_eapply; rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow.
        rw comp1; auto.
Qed.

Lemma implies_eapply_red {o} :
  forall lib (f t a v : @NTerm o),
    eapply_wf_def t
    -> reduces_to lib f t
    -> reduces_to lib a v
    -> reduces_to lib (mk_eapply f a) (mk_eapply t v).
Proof.
  introv wf comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.
  revert dependent f.
  induction k; introv comp1 comp2.

  - allrw @reduces_in_atmost_k_steps_0; subst; eauto 3 with slow.
    apply implies_eapply_red_aux; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup IHk in comp0; auto.
    destruct f as [w|g|op bs].

    + csunf comp1; allsimpl; ginv.

    + csunf comp1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

    + dopid op as [can|ncan|exc|abs] Case.

      * Case "Can".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

      * eapply reduces_to_if_split2;[|exact comp3].
        csunf; simpl; rw comp1; simpl; auto.

      * Case "Exc".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

      * eapply reduces_to_if_split2;[|exact comp3].
        csunf; simpl; rw comp1; simpl; auto.
Qed.

Lemma eapply_lam_can_implies {o} :
  forall lib (a : @NTerm o) v b z,
    computes_to_can lib a z
    -> reduces_to lib (mk_eapply (mk_lam v b) a) (subst b v z).
Proof.
  introv comp.
  allunfold @computes_to_can; repnd.
  eapply reduces_to_trans;
    [apply implies_eapply_red_aux;eauto 3 with slow|].
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; allsimpl.
  apply iscan_implies in comp; repndors; exrepnd; subst; allsimpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma eapply_lam_val_implies {o} :
  forall lib (a : @NTerm o) v b z,
    (a =v>(lib) z)
    -> reduces_to lib (mk_eapply (mk_lam v b) a) (subst b v z).
Proof.
  introv comp.
  apply eapply_lam_can_implies.
  allunfold @computes_to_value; repnd.
  allunfold @computes_to_can; dands; auto.
Qed.

Lemma eapply_red_lam_val_implies {o} :
  forall lib (f a : @NTerm o) v b z,
    (f =v>(lib) (mk_lam v b))
    -> (a =v>(lib) z)
    -> reduces_to lib (mk_eapply f a) (subst b v z).
Proof.
  introv comp1 comp2.
  allunfold @computes_to_value; repnd.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |];
    eauto 3 with slow.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; allsimpl.
  rw @isvalue_iff in comp2; repnd.
  apply iscan_implies in comp4; repndors; exrepnd; subst; allsimpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma eapply_sterm_nat_implies {o} :
  forall lib (a : @NTerm o) f n,
    (a =v>(lib) (mk_nat n))
    -> reduces_to lib (mk_eapply (sterm f) a) (f n).
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  eapply reduces_to_trans;
    [apply implies_eapply_red_aux;eauto 3 with slow|].
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; allsimpl.
  boolvar; try omega.
  rw @Znat.Nat2Z.id; auto.
Qed.

Lemma eapply_red_sterm_nat_implies {o} :
  forall lib (t a : @NTerm o) f n,
    (t =s>(lib) f)
    -> (a =v>(lib) (mk_nat n))
    -> reduces_to lib (mk_eapply t a) (f n).
Proof.
  introv comp1 comp2.
  unfold computes_to_seq in comp1.
  unfold computes_to_value in comp2; repnd.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |]; eauto 3 with slow.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; allsimpl.
  boolvar; try omega.
  rw @Znat.Nat2Z.id; auto.
Qed.

Lemma eapply_sterm_exception_implies {o} :
  forall lib (a n e : @NTerm o) f,
    (a =e>(n,lib) e)
    -> ((mk_eapply (sterm f) a) =e>(n,lib) e).
Proof.
  introv comp.
  allunfold @computes_to_exception.
  eapply reduces_to_trans;
    [apply implies_eapply_red_aux;eauto 3 with slow|].
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; allsimpl; auto.
Qed.

Lemma eapply_red_sterm_exception_implies {o} :
  forall lib (t a n e : @NTerm o) f,
    (t =s>(lib) f)
    -> (a =e>(n,lib) e)
    -> ((mk_eapply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  allunfold @computes_to_exception.
  allunfold @computes_to_seq.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |]; eauto 3 with slow.
Qed.

Lemma apply_sterm_nat_implies {o} :
  forall lib (t a : @NTerm o) f n,
    (t =s>(lib) f)
    -> (a =v>(lib) (mk_nat n))
    -> reduces_to lib (mk_apply t a) (f n).
Proof.
  introv comp1 comp2.
  unfold computes_to_seq in comp1.
  eapply reduces_to_trans;
    [eapply reduces_to_prinarg;eauto|].
  eapply reduces_to_if_split2;[csunf;simpl;eauto|].
  apply eapply_sterm_nat_implies; auto.
Qed.

Lemma apply_sterm_exception_implies {o} :
  forall lib (t a n e : @NTerm o) f,
    (t =s>(lib) f)
    -> (a =e>(n,lib) e)
    -> ((mk_apply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  unfold computes_to_seq in comp1.
  eapply reduces_to_trans;
    [eapply reduces_to_prinarg;eauto|].
  eapply reduces_to_if_split2;[csunf;simpl;eauto|].
  apply eapply_sterm_exception_implies; auto.
Qed.

Lemma eapply_lam_exception_implies {o} :
  forall lib (t : @NTerm o) v b a n e,
    (t =v>(lib) (mk_lam v b))
    -> (a =e>(n,lib) e)
    -> ((mk_eapply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  unfold computes_to_value in comp1; repnd.
  allunfold @computes_to_exception.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |];
    eauto 3 with slow.
Qed.

Lemma eapply_nseq_exception_implies {o} :
  forall lib (t : @NTerm o) s a n e,
    (t =v>(lib) (mk_nseq s))
    -> (a =e>(n,lib) e)
    -> ((mk_eapply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  unfold computes_to_value in comp1; repnd.
  allunfold @computes_to_exception.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |];
    eauto 3 with slow.
Qed.

Lemma eapply_wf_def_oterm_implies {o} :
  forall (op : @Opid o) bs,
    eapply_wf_def (oterm op bs)
    -> ({v : NVar & {t : NTerm & op = Can NLambda # bs = [bterm [v] t] }}
        [+] {s : nseq & op = Can (Nseq s) # bs = [] }).
Proof.
  introv w.
  unfold eapply_wf_def in w; repndors; exrepnd; ginv.
  - allunfold @mk_nseq; ginv.
    right; eexists; dands; auto.
  - allunfold @mk_lam; ginv.
    left; eexists; eexists; dands; eauto.
Qed.

Lemma raises_exception_step {o} :
  forall lib (t u : @NTerm o),
    compute_step lib t = csuccess u
    -> raises_exception lib u
    -> raises_exception lib t.
Proof.
  unfold raises_exception; introv comp1 comp2; exrepnd.
  allunfold @computes_to_exception.
  exists a e.
  eapply reduces_to_if_split2; eauto.
Qed.

Lemma hasvalue_like_eapply_sterm_implies1 {o} :
  forall lib f (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (mk_eapply (sterm f) t)
    -> ({n : nat & computes_to_value lib t (mk_nat n)} [+] raises_exception lib t).
Proof.
  introv wf hv.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t; induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv0; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      left; exists n; eauto 3 with slow.

    + right; eauto 3 with slow.
      apply wf_isexc_implies in wf; auto; exrepnd; subst.
      exists a e.
      apply reduces_to_symm.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd; [left|right].

      * exists n.
        eapply computes_to_value_step; eauto.

      * eapply raises_exception_step; eauto.
Qed.

Lemma hasvalue_like_eapply_sterm_implies {o} :
  forall lib f (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (mk_eapply (sterm f) t)
    -> hasvalue_like lib t.
Proof.
  introv wf hv.
  apply hasvalue_like_eapply_sterm_implies1 in hv; auto.
  repndors; exrepnd; eauto 3 with slow.
  exists (@mk_nat o n); dands; eauto 3 with slow.
Qed.

Lemma hasvalue_like_eapply_lam_implies {o} :
  forall lib v b (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (mk_eapply (mk_lam v b) t)
    -> hasvalue_like lib t.
Proof.
  introv wf hv.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t; induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv0; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      exists arg2; dands; eauto 3 with slow.

    + exists arg2; eauto 3 with slow.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      exrepnd.
      exists v1; dands; auto.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma hasvalue_like_eapply_nseq_implies {o} :
  forall lib s (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (mk_eapply (mk_nseq s) t)
    -> hasvalue_like lib t.
Proof.
  introv wf hv.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t; induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv0; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      exists (@mk_nat o n); dands; eauto 3 with slow.

    + exists arg2; eauto 3 with slow.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      exrepnd.
      exists v0; dands; auto.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma has_value_like_k_eapply_sterm_implies1 {o} :
  forall lib f k (t : @NTerm o),
    nt_wf t
    -> has_value_like_k lib k (mk_eapply (sterm f) t)
    -> {v : NTerm
        & {j : nat
        & j < k
        # reduces_in_atmost_k_steps lib t v j
        # ({n : nat & v = mk_nat n}
           [+] {a : NTerm & {e : NTerm & v = mk_exception a e}}) }}.
Proof.
  induction k; introv wf comp.

  - allrw @has_value_like_0; repnd; subst.
    unfold isvalue_like in comp; allsimpl; tcsp.

  - allrw @has_value_like_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      exists (@mk_nat o n) 0; dands; try omega.

      * apply reduces_in_atmost_k_steps_0; auto.

      * left; eexists; eauto.

    + apply wf_isexc_implies in wf; auto; exrepnd; subst.
      exists (mk_exception a e) 0; dands; try omega.

      * apply reduces_in_atmost_k_steps_0; auto.

      * right; eexists; eexists; eauto.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd.
      exists v (S j); dands; try omega; auto.
      apply reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma has_value_k_like_eapply_sterm_implies {o} :
  forall lib f k (t : @NTerm o),
    nt_wf t
    -> has_value_like_k lib k (mk_eapply (sterm f) t)
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  introv wf hv.
  apply has_value_like_k_eapply_sterm_implies1 in hv; auto.
  exrepnd.
  exists j; dands; auto.
  unfold has_value_like_k.
  exists v; auto.
  unfold computes_to_val_like_in_max_k_steps; dands; auto.
  repndors; exrepnd; subst; eauto 3 with slow.
Qed.

Lemma has_value_like_k_eapply_lam_implies {o} :
  forall lib v b k (t : @NTerm o),
    nt_wf t
    -> has_value_like_k lib k (mk_eapply (mk_lam v b) t)
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv wf comp.

  - allrw @has_value_like_0; subst.
    allunfold @isvalue_like; allsimpl; tcsp.

  - allrw @has_value_like_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      exists 0; dands; try omega.
      apply has_value_like_0; eauto 3 with slow.

    + exists 0; dands; try omega.
      apply has_value_like_0; eauto 3 with slow.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      exrepnd.
      exists (S j); dands; auto; try omega.
      apply has_value_like_S; eexists; dands; eauto.
Qed.

Lemma has_value_like_k_eapply_nseq_implies {o} :
  forall lib s k (t : @NTerm o),
    nt_wf t
    -> has_value_like_k lib k (mk_eapply (mk_nseq s) t)
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv wf comp.

  - allrw @has_value_like_0; subst.
    allunfold @isvalue_like; allsimpl; tcsp.

  - allrw @has_value_like_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; subst; ginv.
      exists 0; dands; try omega.
      apply has_value_like_0; eauto 3 with slow.

    + exists 0; dands; try omega.
      apply has_value_like_0; eauto 3 with slow.

    + applydup @preserve_nt_wf_compute_step in comp1; auto.
      apply IHk in comp0; auto.
      exrepnd.
      exists (S j); dands; auto; try omega.
      apply has_value_like_S; eexists; dands; eauto.
Qed.

Lemma hasvalue_sterm {o} :
  forall lib (f : @ntseq o),
    isprogram (sterm f)
    -> hasvalue lib (sterm f).
Proof.
  introv isp.
  eapply computes_to_value_hasvalue.
  apply computes_to_value_isvalue_refl; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_sterm : slow.

Definition ntseqc {o} : Type := nat -> @CNTerm o.

Definition ntseqc2seq {o} (f : @ntseqc o) :=
  fun n => get_cnterm (f n).

Definition computes_to_seqc {o} lib (a : @CTerm o) (f : ntseqc) :=
  computes_to_seq lib (get_cterm a) (ntseqc2seq f).

Definition computes_to_seqnc {o} lib (a : @CTerm o) (f : ntseq) :=
  computes_to_seq lib (get_cterm a) f.

Lemma isprog_nout_iff {o} :
  forall (t : @NTerm o),
    isprog_nout t <=> (closed t # noutokens t # nt_wf t).
Proof.
  introv.
  unfold isprog_nout, no_vars_like_b.
  rw assert_of_andb.
  allrw assert_nullb.
  allrw null_iff_nil.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma isprog_ntseqc {o} :
  forall (f : @ntseqc o),
    isprog (sterm (ntseqc2seq f)).
Proof.
  introv.
  apply isprog_eq.
  constructor; tcsp.
  constructor; introv.
  unfold ntseqc2seq.
  remember (f n) as t; clear Heqt.
  destruct t; simpl.
  rw @isprog_nout_iff in i; sp.
Qed.

Definition mkc_ntseq {o} (f : @ntseqc o) : CTerm :=
  exist isprog (sterm (ntseqc2seq f)) (isprog_ntseqc f).


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
