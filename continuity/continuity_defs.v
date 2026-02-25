(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export computation8.
Require Export list_tacs.
Require Export alphaeq2.
Require Export substitution2.
Require Export terms5.
Require Export computation10.
Require Export computation11.
Require Export nat_defs.


Definition uexc {o} (a : get_patom_set o) :=
  mk_exception (mk_utoken a) mk_axiom.

Lemma isnexc_uexc {o} :
  forall lib (a : get_patom_set o),
    isnexc lib a (uexc a).
Proof.
  introv; simpl; eauto with slow.
Qed.
Hint Resolve isnexc_uexc : slow.

Definition get_ints_can {o} (c : @CanonicalOp o) : list Z :=
  match c with
    | Nint z => [z]
    | _ => []
  end.

Definition get_ints_op {o} (op : @Opid o) : list Z :=
  match op with
    | Can c => get_ints_can c
    | _ => []
  end.

Fixpoint get_ints {o} (t : @NTerm o) : list Z :=
  match t with
    | vterm _ => []
    | sterm _ => []
    | oterm op bs => get_ints_op op ++ flat_map get_ints_b bs
  end
with get_ints_b {o} (b : @BTerm o) : list Z :=
       match  b with
         | bterm vs t => get_ints t
       end.

(*
   t + 0
 *)
Definition force_int {o} (t : @NTerm o) : NTerm := mk_add t mk_zero.

(*
   if |t| < b then t else e
 *)
Definition less_bound {o} (b : nat) (t e : @NTerm o) :=
  mk_less (absolute_value t) (mk_nat b) t e.

(*
   let v := t
   in if |v| < b then v else e
 *)
Definition force_int_bound {o} (v : NVar) (b : nat) (t e : @NTerm o) : NTerm :=
  mk_cbv t v (less_bound b (mk_var v) e).



Definition force_int_f {o} v (f : @NTerm o) :=
  mk_lam v (mk_cbv
              (force_int (mk_var v))
              v
              (mk_apply f (mk_var v))).

Definition force_int_F {o} v (F f : @NTerm o) :=
  mk_apply F (force_int_f v f).

Definition force_int_bound_f {o} v b (f : @NTerm o) e :=
  mk_lam v (mk_cbv
              (force_int_bound v b (mk_var v) e)
              v
              (mk_apply f (mk_var v))).

Definition force_int_bound_F {o} v b (F f : @NTerm o) e :=
  mk_apply F (force_int_bound_f v b f e).

Definition agree_upto_red_b {o} lib b (f g : @NTerm o) :=
  forall t1 t2 (i : Z),
    reduces_to lib t1 (mk_integer i)
    -> reduces_to lib t2 (mk_integer i)
    -> Z.abs_nat i < b
    -> {z : Z
        & reduces_to lib (mk_apply f t1) (mk_integer z)
        # reduces_to lib (mk_apply g t2) (mk_integer z)}.

Definition agree_upto_b {o} lib b (f g : @NTerm o) :=
  forall (i : Z),
    Z.abs_nat i < b
    -> {z : Z
        & reduces_to lib (mk_apply f (mk_integer i)) (mk_integer z)
        # reduces_to lib (mk_apply g (mk_integer i)) (mk_integer z)}.

Lemma agree_upto_red_implies {o} :
  forall lib b (f g : @NTerm o),
    agree_upto_red_b lib b f g
    -> agree_upto_b lib b f g.
Proof.
  introv agree.

  unfold agree_upto_b; introv l.
  unfold agree_upto_red_b in agree.

  pose proof (agree (mk_integer i) (mk_integer i) i) as h.
  repeat (autodimp h hyp); eauto with slow.
Qed.

Lemma agree_upto_red_if {o} :
  forall lib b (f g : @NTerm o),
    agree_upto_b lib b f g
    -> agree_upto_red_b lib b f g.
Proof.
  introv agree.

  unfold agree_upto_red_b; introv r1 r2 l.
  unfold agree_upto_b in agree.

  pose proof (agree i) as h; autodimp h hyp.
  exrepnd.
  exists z; dands.
Abort.

Definition reduces_to_int {o} lib (t : @NTerm o) :=
  {z : Z & reduces_to lib t (mk_integer z)}.

(*

  let v := (let v := arg in if |v| < b then v else e) in f(v)

 *)
Definition force_int_bound_app {o} (v : NVar) (b : nat) (arg f e : @NTerm o) : NTerm :=
  mk_cbv (force_int_bound v b arg e) v (mk_apply f (mk_var v)).

Lemma alpha_eq_force_int {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (force_int t1) (force_int t2).
Proof.
  introv aeq.
  unfold force_int, mk_add.
  prove_alpha_eq4.
  introv i.
  destruct n;[|destruct n]; try lia.
  - apply alphaeqbt_nilv2; auto.
  - apply alphaeqbt_nilv2; auto.
Qed.

Lemma alpha_eq_force_int_bound {o} :
  forall b v1 v2 (t1 t2 e1 e2 : @NTerm o),
    !LIn v1 (free_vars e1)
    -> !LIn v2 (free_vars e2)
    -> alpha_eq t1 t2
    -> alpha_eq e1 e2
    -> alpha_eq
         (force_int_bound v1 b t1 e1)
         (force_int_bound v2 b t2 e2).
Proof.
  introv ni1 ni2 aeq1 aeq2.
  unfold force_int_bound, mk_cbv, mk_less.
  prove_alpha_eq4.
  introv i.
  destruct n;[|destruct n]; try lia.

  - apply alphaeqbt_nilv2; auto.

  - pose proof (ex_fresh_var
                  ([v1,v2]
                     ++ all_vars (less_bound b (vterm v1) e1)
                     ++ all_vars (less_bound b (vterm v2) e2)
               )) as h; exrepnd.
    allunfold @all_vars; allsimpl.
    allsimpl; allrw app_nil_r; allrw remove_nvars_nil_l.
    allrw in_app_iff; allsimpl; allrw in_app_iff.
    allrw not_over_or; repnd; GC.

    apply (al_bterm _ _ [v]); simpl; auto.

    + unfold all_vars; simpl.
      allrw remove_nvars_nil_l; allrw app_nil_r.
      rw disjoint_singleton_l; simpl.
      allrw in_app_iff; simpl; allrw in_app_iff; sp.

    + unfold lsubst; simpl; boolvar; allrw app_nil_r;
      allrw disjoint_singleton_r; tcsp.
      prove_alpha_eq4.
      introv j.
      destruct n;[|destruct n;[|destruct n;[|destruct n]]];
      try lia; eauto 3 with slow.

      apply alphaeqbt_nilv2; auto.
      repeat (rw @lsubst_aux_trivial_cl_term); auto; simpl;
      allrw disjoint_singleton_r; auto.
Qed.

Lemma wf_term_absolute_value {o} :
  forall (t : @NTerm o), wf_term (absolute_value t) <=> wf_term t.
Proof.
  introv; unfold absolute_value.
  rw <- @wf_less_iff.
  rw <- @wf_minus_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma wf_term_force_int {o} :
  forall (t : @NTerm o), wf_term (force_int t) <=> wf_term t.
Proof.
  introv; unfold force_int.
  rw @wf_arithop_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma hasvalue_like_absolute_value {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> hasvalue_like lib (absolute_value t)
    -> ({z : Z & computes_to_value lib t (mk_integer z)} [+] raises_exception lib t).
Proof.
  introv wf r.
  unfold hasvalue_like in r; exrepnd.
  unfold absolute_value, reduces_to in r1; exrepnd.
  pose proof (has_value_like_k_mk_less lib k t mk_zero (mk_minus t) t) as h.
  repeat (autodimp h hyp); eauto 3 with slow;
  try (apply wf_minus; auto).
  { exists v; unfold computes_to_val_like_in_max_k_steps; dands; auto. }

  repndors; exrepnd.

  - right.
    exists u e k1; auto.

  - left.
    exists z.
    split; eauto 3 with slow.

  - left.
    exists i1.
    split; eauto 3 with slow.
Qed.

Lemma computes_to_exception_absolute_value {o} :
  forall lib (t : @NTerm o) a e,
    wf_term t
    -> computes_to_exception lib a (absolute_value t) e
    -> computes_to_exception lib a t e.
Proof.
  introv wf r.
  apply computes_to_exception_mk_less in r; eauto 3 with slow;
  try (apply wf_minus; auto).

  repndors; exrepnd; repndors; exrepnd; auto;
  try (complete (exists a e; auto)).

  - apply computes_to_exception_minus in r1; auto.

  - apply can_doesnt_raise_an_exception in r0; sp.
Qed.

(*
Lemma absolute_value_reduces_to_int {o} :
  forall lib (t : @NTerm o) z,
    reduces_to lib (absolute_value t) (mk_integer z)
    -> {i : Z & reduces_to lib t (mk_integer i) # z = Z.abs i}.
Proof.
  introv comp.
  unfold reduces_to in comp; exrepnd.
  revert dependent t.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; ginv.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [v|f|op bs]; ginv.
    dopid op as [can|ncan|exc|abs] Case.

    + Case "Can".
      dcwf h; allsimpl.
      apply compute_step_compop_success_can_can in comp1; exrepnd; subst; GC; allsimpl.
      repndors; exrepnd; subst; ginv.
      allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.
      boolvar.

      * pose proof (computes_to_val_like_in_max_k_steps_minus_implies
                      lib k (mk_integer n1) (mk_integer z)) as h.
        autodimp h hyp.
        { split; eauto 3 with slow. }
        exrepnd; repndors; exrepnd; subst; allsimpl; ginv; tcsp.

        exists n1; dands; eauto 3 with slow.
        apply computes_to_val_like_in_max_k_steps_if_isvalue_like in h2; eauto 3 with slow; ginv.
        symmetry; apply Z.abs_neq; try lia.

      * apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; ginv.
        exists n1; dands; eauto 3 with slow.
        symmetry; apply Z.abs_eq; try lia.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bs)) as cs; symmetry in Heqcs; destruct cs; ginv.
      pose proof (IHk n) as h; autodimp h hyp.
      {
      }
Qed.
 *)

(*
Lemma hasvalue_like_subst_less_bound2 {o} :
  forall lib b v (t : @NTerm o),
    wf_term t
    -> hasvalue_like
         lib
         (subst (less_bound b (mk_var v) (mk_vbot v)) v t)
    -> ({z : Z & computes_to_value lib t (mk_integer z) # Z.abs_nat z < b}
        [+] raises_exception lib t).
Proof.
  introv wf r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.

    remember (compute_step lib (absolute_value t)) as cs;
      symmetry in Heqcs; destruct cs; ginv.
    fold_terms.
    unfold reduces_to in r2; exrepnd.
    applydup @compute_step_preserves_wf in Heqcs; auto;
    try (apply wf_term_absolute_value; auto).

    pose proof (has_value_like_k_mk_less lib k n (mk_nat b) t (mk_fix (mk_lam v (mk_var v)))) as h.
    repeat (autodimp h hyp); eauto 3 with slow;
    try (apply wf_fix; apply wf_lam; eauto 3 with slow).
    { exists v0.
      unfold computes_to_val_like_in_max_k_steps; dands; auto. }
    repndors; exrepnd.

    { pose proof (computes_to_exception_absolute_value lib t u e) as q.
      repeat (autodimp q hyp).
      { eapply computes_to_exception_step;[|eauto].
        exists k1; auto. }
      right.
      exists u e; auto. }

    { apply computes_to_exception_in_max_k_steps_can in h3; sp. }

    { apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in h3; eauto 3 with slow.
      allunfold @mk_nat; ginv; fold_terms.
      boolvar;[|apply has_value_like_k_vbot in h4; sp];[].
      left.


    }

      pose proof (hasvalue_like_absolute_value lib t) as q.
      repeat (autodimp q hyp).
      { exists (mk_exception u e); dands; eauto 3 with slow.
        eapply reduces_to_if_split2;[eauto|].
        exists k1; auto. }
      repndors; exrepnd.
      { left.
        exists z; dands; auto.

XXXXXXXXXXXX

    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; repndors; csunf r2; allsimpl; exrepnd; subst; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst; csunf r2; allsimpl; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }
Qed.
 *)

Lemma hasvalue_like_subst_less_bound {o} :
  forall lib b v can (bs : list (@BTerm o)),
    hasvalue_like
      lib
      (subst (less_bound b (mk_var v) (mk_vbot v)) v (oterm (Can can) bs))
    -> {z : Z & can = Nint z # bs = [] # Z.abs_nat z < b}.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; repndors; csunf r2; allsimpl; exrepnd; subst; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst; csunf r2; allsimpl; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }
Qed.

Lemma if_hasvalue_like_ncan_primarg {o} :
  forall lib ncan (t : @NTerm o) bs,
    hasvalue_like lib (oterm (NCan ncan) (bterm [] t :: bs))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t.
  induction k; introv r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv0; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [x|f|op l].

    { simpl in r1; ginv. }

    { exists (sterm f); dands; eauto 3 with slow. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists (oterm (Can can1) l); dands; simpl; eauto with slow; tcsp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists v0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; allsimpl.
      apply compute_step_catch_success in r1.
      dorn r1; exrepnd; subst; allsimpl.

      * exists (oterm Exc [bterm [] a', bterm [] e]); dands; eauto with slow.

      * apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; subst.

    + Case "Abs".
      csunf r1; allsimpl.
      csunf r1; allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists v0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma hasvalue_like_subst_less_bound_seq {o} :
  forall lib b v e (f : @ntseq o),
    hasvalue_like
      lib
      (subst (less_bound b (mk_var v) e) v (sterm f))
    -> False.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  unfold hasvalue_like in r; exrepnd.
  apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.
  { unfold isvalue_like in r0; allsimpl; sp. }
  csunf r1; allsimpl; ginv.
Qed.

Lemma reduces_to_force_int_bound {o} :
  forall lib v b (t e u : @NTerm o),
    nt_wf t
    -> !LIn v (free_vars e)
    -> disjoint (bound_vars e) (free_vars t) (* should be enough, make things easier *)
    -> reduces_to lib (force_int_bound v b t e) u
    -> isvalue_like u
    -> {z : Z & reduces_to lib t (mk_integer z)
        # (
           (Z.abs_nat z < b # u = mk_integer z)
           [+]
           (b <= Z.abs_nat z # reduces_to lib e u)
          )
       }
       [+]
       (reduces_to lib t u # isexc u).
Proof.
  introv wf ni disj r.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf disj r isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v1|f1|op1 bs1].

    { simpl in r1; ginv. }

    { csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl.
      allrw @fold_subst.
      pose proof (hasvalue_like_subst_less_bound_seq lib b v e f1) as h.
      autodimp h hyp; tcsp.
      exists u; dands; auto.
      exists k; auto. }

    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl.
      unfold lsubst in r0.
      boolvar;[|provefalse; simpl in n; allrw app_nil_r; complete sp].
      simpl in r0; boolvar.
      fold_terms.
      rw @lsubst_aux_trivial_cl_term in r0;
        [|simpl; rw disjoint_singleton_r; auto].
      destruct k.

      { allrw @reduces_in_atmost_k_steps_0; subst.
        allunfold @isvalue_like; allsimpl; sp. }

      allrw @reduces_in_atmost_k_steps_S; exrepnd.
      allsimpl; allrw app_nil_r.
      csunf r0; allsimpl.
      unfold on_success in r0.
      csunf r0; allsimpl.
      dcwf h; allsimpl.
      match goal with
        | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
      end.
      symmetry in Heqcomp; destruct comp; ginv.
      apply compute_step_compop_success_can_can in Heqcomp.
      exrepnd; subst; allsimpl; cpx; GC.
      repndors; exrepnd; ginv.
      allapply @get_param_from_cop_pki; subst.

      destruct k.

      { allrw @reduces_in_atmost_k_steps_0; subst.
        unfold isvalue_like in isv; allsimpl; cpx. }

      allrw @reduces_in_atmost_k_steps_S; exrepnd.
      left.
      csunf r1; allsimpl.
      boolvar; allsimpl; ginv.

      * destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        allsimpl.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

        { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
          exists n1; dands; eauto with slow.
          left; dands; eauto with slow.
          apply abs_of_neg; auto. }

        { exists n1; dands; eauto with slow.
          right; dands; eauto with slow.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-n1)) as p.
          autodimp p hyp; try lia. }

      * dcwf h; allsimpl.
        unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

        { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
          exists n1; dands; eauto with slow.
          left; dands; eauto with slow.
          apply abs_of_pos; auto. }

        { exists n1; dands; eauto with slow.
          right; dands; eauto with slow.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) n1) as p.
          autodimp p hyp; try lia. }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      applydup @compute_step_preserves in Heqcomp; repnd; auto.
      eapply subvars_disjoint_r in Heqcomp1;[|exact disj].

      apply IHk in r0; auto; exrepnd.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; simpl in r1; ginv.
      right.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.

    + Case "Abs".
      csunf r1; allsimpl.
      unfold on_success in r1.
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      pose proof (compute_step_preserves lib (oterm (Abs abs1) bs1) n) as h.
      repeat (autodimp h hyp); repnd.
      eapply subvars_disjoint_r in h0;[|exact disj].

      apply IHk in r0; auto.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.
Qed.

Lemma reduces_to_force_int_bound_vbot {o} :
  forall lib v b (t u : @NTerm o),
    nt_wf t
    -> reduces_to lib (force_int_bound v b t (mk_vbot v)) u
    -> isvalue_like u
    -> {z : Z & reduces_to lib t (mk_integer z)
        # Z.abs_nat z < b
        # u = mk_integer z}
       [+]
       (reduces_to lib t u # isexc u).
Proof.
  introv wf r isv.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v1|f1|op1 bs1].

    { simpl in r1; ginv. }

    { csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl; allrw @fold_subst.
      pose proof (hasvalue_like_subst_less_bound_seq lib b v (mk_vbot v) f1) as h.
      autodimp h hyp; tcsp.
      exists u; dands; auto.
      exists k; auto. }

    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf r1; simpl in r1; ginv.
      unfold apply_bterm in r0; allsimpl.
      unfold lsubst in r0.
      boolvar; allsimpl; fold_terms; boolvar; allsimpl;
      allrw app_nil_r; allrw @var_ren_nil_l; allrw @lsubst_aux_nil;
      repndors; tcsp; GC; boolvar; allrw not_over_or; repnd; tcsp; GC;
      try (complete (match goal with
                       | [ H : context[fresh_var ?l] |- _ ] =>
                         let h := fresh "h" in
                         pose proof (fresh_var_not_in l) as h;
                       unfold all_vars in h;
                       simpl in h;
                       repeat (rw in_app_iff in h);
                       repeat (rw not_over_or in h);
                       repnd; allsimpl; tcsp
                     end)); fold_terms.

      { destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          allunfold @isvalue_like; allsimpl; sp. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        csunf r0; allsimpl.
        unfold on_success in r0.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        match goal with
          | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
            remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
        end.
        symmetry in Heqcomp; destruct comp; ginv.
        apply compute_step_compop_success_can_can in Heqcomp.
        exrepnd; subst; allsimpl; cpx; GC.
        repndors; exrepnd; ginv.
        allapply @get_param_from_cop_pki; subst.

        destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        left.
        csunf r1; allsimpl.
        boolvar; allsimpl; ginv.

        * destruct k.

          { allrw @reduces_in_atmost_k_steps_0; subst.
            unfold isvalue_like in isv; allsimpl; cpx. }

          allrw @reduces_in_atmost_k_steps_S; exrepnd.
          csunf r0; allsimpl.
          dcwf h; allsimpl.
          unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_neg; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r1; sp. }

        * dcwf h; allsimpl.
          unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_pos; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r0; sp. }
      }

      { destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          allunfold @isvalue_like; allsimpl; sp. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        csunf r0; allsimpl.
        unfold on_success in r0.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        fold_terms.
        match goal with
          | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
            remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
        end.
        symmetry in Heqcomp; destruct comp; ginv.
        apply compute_step_compop_success_can_can in Heqcomp.
        exrepnd; subst; allsimpl; cpx; GC.
        repndors; exrepnd; ginv.
        allapply @get_param_from_cop_pki; subst.

        destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        left.
        csunf r1; allsimpl.
        boolvar; allsimpl; ginv.

        * destruct k.

          { allrw @reduces_in_atmost_k_steps_0; subst.
            unfold isvalue_like in isv; allsimpl; cpx. }

          allrw @reduces_in_atmost_k_steps_S; exrepnd.
          csunf r0; allsimpl.
          dcwf h; allsimpl.
          unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_neg; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r1; sp. }

        * dcwf h; allsimpl.
          unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_pos; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r0; sp. }
      }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      applydup @compute_step_preserves in Heqcomp; repnd; auto.

      apply IHk in r0; auto; exrepnd.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; simpl in r1; ginv.
      right.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.

    + Case "Abs".
      csunf r1; allsimpl.
      unfold on_success in r1.
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      pose proof (compute_step_preserves lib (oterm (Abs abs1) bs1) n) as h.
      repeat (autodimp h hyp); repnd.

      apply IHk in r0; auto.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.
Qed.

Definition has_value_like_except {p} lib a (t : @NTerm p) :=
  {u : NTerm
   & reduces_to lib t u
   # isvalue_like u
   # !isnexc lib a u}.

Lemma if_has_value_like_except_force_int_bound {o} :
  forall lib a v b (t : @NTerm o),
    nt_wf t
    -> has_value_like_except
         lib a
         (force_int_bound v b t (uexc a))
    -> {u : NTerm
        & reduces_to lib t u
        # isvalue_like u
        # (
           {z : Z & u = mk_integer z # Z.abs_nat z < b}
           [+]
           (isexc u # !isnexc lib a u)
          )
       }.
Proof.
  introv wf hv.
  unfold has_value_like_except in hv; exrepnd.
  apply reduces_to_force_int_bound in hv1; simpl; tcsp.
  dorn hv1; exrepnd.

  - exists (@mk_integer o z); dands; eauto with slow;
    try (complete (unfold mk_integer; eauto with slow)).
    left; exists z; dands; auto.
    dorn hv3; repnd; auto.
    apply reduces_to_if_isvalue_like in hv3;[|unfold uexc; eauto with slow].
    subst.
    destruct hv0.
    simpl; boolvar; eauto with slow.

  - exists u; dands; eauto with slow.
Qed.

Lemma if_hasvalue_like_force_int_bound {o} :
  forall lib v b (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (force_int_bound v b t (mk_vbot v))
    -> {u : NTerm
        & reduces_to lib t u
        # isvalue_like u
        # (
           {z : Z & u = mk_integer z # Z.abs_nat z < b}
           [+]
           isexc u
          )
       }.
Proof.
  introv wf hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_to_force_int_bound_vbot in hv1; simpl; tcsp;
  allrw remove_nvars_eq; tcsp.
  dorn hv1; exrepnd.

  - exists (@mk_integer o z); dands; eauto with slow;
    try (complete (unfold mk_integer; eauto with slow)).

  - exists v0; dands; eauto with slow.
Qed.

(*
Lemma if_has_value_like_except_ncan_primarg {o} :
  forall lib a ncan (t : @NTerm o) bs,
    has_value_like_except lib a (oterm (NCan ncan) (bterm [] t :: bs))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  allunfold @has_value_like_except; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t.
  induction k; introv r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv2; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists (oterm (Can can1) l); dands; simpl; eauto with slow; tcsp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists u0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; allsimpl.
      apply compute_step_catch_success in r1.
      repndors; exrepnd; subst; allsimpl.

      *

Lemma reduces_in_atmost_k_steps_mk_atom_eq {o}:
  forall lib (a b c d : @NTerm o) u,
    reduces_in_atmost_k_steps lib (mk_atom_eq a b c d) u k
    -> isvalue_like u
    -> {k1 : nat
        & {k2 : nat
        & {v1 : NTerm
        & {v2 : NTerm
        & reduces_in_atmost_k_steps lib a v1 k1
        # reduces_in_atmost_k_steps lib b v2 k2
        # }}}}.
Proof.
Qed.

        exists (oterm Exc [bterm [] a', bterm [] e]); dands; eauto with slow.
        allsimpl.
        destruct exc1; allsimpl; tcsp.
        boolvar; ginv; allrw not_over_or; tcsp.

      * apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; subst.
        exists (oterm (Exc exc1) l); dands; eauto with slow.

    + Case "Mrk".
      allsimpl; ginv.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      unfold isvalue_like in hv2; allsimpl; sp.

    + Case "Abs".
      allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists u0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.
Qed.
*)

(*
Lemma if_has_value_like_except_exc {o} :
  forall lib a exc (bs : list (@BTerm o)),
    has_value_like_except lib a (oterm (Exc exc) bs)
    -> exc <> Some a.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.
  apply reduces_to_if_isvalue_like in hv1; eauto with slow.
  subst.
  introv k.
  destruct exc; allsimpl; ginv; boolvar; cpx.
Qed.
*)

(*
Lemma compute_step_apply_failure {o} :
  forall can (bs1 bs2 : list (@BTerm o)) s t,
    compute_step_apply
      can
      (oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
      bs1 bs2 = cfailure s t
    -> (
         (can = NLambda
          # (forall v b, bs1 <> [bterm [v] b])
          # s = compute_step_apply_not_well_formed
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
         [+]
         (can = NLambda
          # (forall arg, bs2 <> [bterm [] arg])
          # s = compute_step_apply_not_well_formed
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
         [+]
         (can <> NLambda
          # s = bad_first_arg
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
       ).
Proof.
  introv comp.
  destruct can;
    try (complete (simpl in comp; ginv; right; right; dands; tcsp; intro k; inversion k)).
  destruct bs1.
  - simpl in comp; ginv.
    left; dands; sp.
  - destruct bs1.
    + destruct b.
      destruct l.
      * simpl in comp; ginv.
        left; dands; tcsp.
        introv k; tcsp; ginv.
      * destruct l.
        { destruct bs2.
          { simpl in comp; ginv.
            right; left; sp. }
          { destruct bs2.
            - destruct b.
              destruct l.
              + simpl in comp; ginv.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
                introv k; ginv.
            - destruct b.
              destruct l.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
          }
        }
        { simpl in comp; ginv.
          left; dands; tcsp.
          introv k; ginv. }
    + destruct b.
      destruct l.
      * simpl in comp; ginv.
        left; dands; tcsp.
      * destruct l.
        { simpl in comp; ginv.
          left; dands; tcsp. }
        { simpl in comp; ginv.
          left; dands; tcsp. }
Qed.
*)

Lemma wf_force_int_bound {o} :
  forall v b (t : @NTerm o) e,
    wf_term (force_int_bound v b t e) <=> (wf_term t # wf_term e).
Proof.
  introv.
  unfold force_int_bound.
  rw <- @wf_cbv_iff.
  unfold less_bound.
  rw <- @wf_less_iff.
  unfold absolute_value.
  rw <- @wf_less_iff.
  rw <- @wf_minus_iff.
  split; introv k; repndors; repnd; dands; tcsp.
Qed.

Lemma wf_term_force_int_bound_F_if {o} :
  forall x b (F f e : @NTerm o),
    wf_term F
    -> wf_term f
    -> wf_term e
    -> wf_term (force_int_bound_F x b F f e).
Proof.
  introv wF wf we.
  unfold force_int_bound_F.
  apply wf_apply; auto.
  unfold force_int_bound_f.
  apply wf_lam.
  apply wf_cbv.
  - apply wf_force_int_bound; sp.
  - apply wf_apply; sp.
Qed.
Hint Resolve wf_term_force_int_bound_F_if : slow.

Lemma wf_term_force_int_F_if {o} :
  forall x (F f : @NTerm o),
    wf_term F
    -> wf_term f
    -> wf_term (force_int_F x F f).
Proof.
  introv wF wf.
  unfold force_int_F.
  apply wf_apply; auto.
  unfold force_int_f.
  apply wf_lam.
  apply wf_cbv; tcsp.
  apply wf_apply; sp.
Qed.
Hint Resolve wf_term_force_int_F_if : slow.

Lemma reduces_to_int_subst_less_bound {o} :
  forall lib b v a can z (bs : list (@BTerm o)),
    reduces_to
      lib
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
      (mk_integer z)
    -> can = Nint z # bs = [] # Z.abs_nat z < b.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.

  apply reduces_to_split2 in r; dorn r; allsimpl; exrepnd; ginv.
  csunf r1; allsimpl.
  unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r0; dorn r0; allsimpl; exrepnd; ginv.
  csunf r0; allsimpl.
  boolvar; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; ginv.
    exrepnd; allsimpl.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      inversion r0; subst; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      inversion r0.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r0; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      inversion r1; subst; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      inversion r1.
Qed.

Lemma has_value_like_except_subst_less_bound {o} :
  forall lib b v a can (bs : list (@BTerm o)),
    has_value_like_except
      lib a
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
    -> {z : Z & can = Nint z # bs = [] # Z.abs_nat z < b}.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.
  unfold has_value_like_except in r; exrepnd.

  apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

  { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

  csunf r1; allsimpl.
  unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r3; dorn r3; allsimpl; exrepnd; subst.

  { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

  csunf r3; allsimpl; boolvar; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
      exists z; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
      destruct r0; simpl; exists (mk_utoken a); simpl; boolvar; dands; tcsp; eauto with slow.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r3; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
      exists z; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
      destruct r0; simpl; exists (mk_utoken a); simpl; boolvar; dands; tcsp; eauto with slow.
Qed.

Lemma if_has_value_like_except_ncompop_can1 {o} :
  forall lib a c can bs (t : @NTerm o) l,
    has_value_like_except
      lib a
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_ncompop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (pk2term pk); dands; eauto 3 with slow.
    rw @pk2term_eq; simpl; tcsp.

  - exists e; dands; auto.
    + unfold isvalue_like; simpl; sp.
    + apply isexc_implies2 in h0; exrepnd; subst.
      eapply compose_reduces_to_primarg_ncompop in h1; eauto.
      apply reduces_to_split2 in h1; dorn h1.
      * subst; allunfold @isvalue_like; allsimpl; sp.
      * exrepnd; csunf h1; simpl in h1; ginv.
        dcwf h; ginv.
        apply reduces_to_if_isvalue_like in h0; eauto with slow.
        subst; auto.
Qed.

Lemma if_has_value_like_except_arithop_can1 {o} :
  forall lib a c can bs (t : @NTerm o) l,
    has_value_like_except
      lib a
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_narithop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.
    + intro k; inversion k.

  - exists e; dands; auto.
    + unfold isvalue_like; simpl; sp.
    + apply isexc_implies2 in h0; exrepnd; subst.
      eapply compose_reduces_to_primarg_arithop in h1; eauto.
      apply reduces_to_split2 in h1; dorn h1.
      * subst; allunfold @isvalue_like; allsimpl; sp.
      * exrepnd; csunf h1; simpl in h1; ginv.
        dcwf h; ginv.
        apply reduces_to_if_isvalue_like in h0; eauto with slow.
        subst; auto.
Qed.

Lemma if_hasvalue_like_arithop_can1 {o} :
  forall lib c can bs (t : @NTerm o) l,
    hasvalue_like
      lib
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_narithop lib c can bs t l) as h.
  autodimp h hyp.

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.

  - exists e; dands; auto.
    unfold isvalue_like; simpl; sp.
Qed.

Lemma reduces_to_int_subst_less_bound3 {o} :
  forall lib b v a can (bs : list (@BTerm o)) u,
    reduces_to
      lib
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
      u
    -> isvalue_like u
    -> {z : Z
        & can = Nint z
        # bs = []
        # (
           (Z.abs_nat z < b # u = mk_integer z)
           [+]
           (b <= Z.abs_nat z # u = uexc a)
          )
       }.
Proof.
  introv r isv.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.

  apply reduces_to_split2 in r; dorn r; subst.

  { allunfold @isvalue_like; allsimpl; sp. }

  exrepnd; allsimpl.
  csunf r1; allsimpl; unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r0; dorn r0; subst.

  { allunfold @isvalue_like; allsimpl; sp. }

  exrepnd; allsimpl.
  boolvar; allsimpl; ginv; csunf r0; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; subst.

    { allunfold @isvalue_like; allsimpl; sp. }

    exrepnd; allsimpl.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      subst.
      exists z; dands; auto.
      left; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      subst.
      exists z; dands; auto.
      right; dands; auto.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as k.
      autodimp k hyp; try lia.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r0; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      subst.
      exists z; dands; auto.
      left; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      subst.
      exists z; dands; auto.
      right; dands; auto.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as k.
      autodimp k hyp; try lia.
Qed.
