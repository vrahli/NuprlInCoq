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

Require Export computation5.
Require Export atom_ren.


Lemma computes_to_val_like_in_max_k_steps_preserves_program {p} :
  forall lib k (t1 t2 : @NTerm p),
    computes_to_val_like_in_max_k_steps lib t1 t2 k
    -> isprogram t1
    -> isprogram t2.
Proof.
  unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps;
  introv comp isp; repnd.
  apply computek_preserves_program in comp0; sp.
Qed.

Lemma isprogram_subst_if_bt {p} :
  forall t v a,
    @isprogram p a
    -> isprogram_bt (bterm [v] t)
    -> isprogram (subst t v a).
Proof.
  introv ispa ispt.
  apply subst_preserves_program; auto.
  destruct ispt as [c w].
  inversion w; sp.
  introv i.
  destruct ispt as [c w].
  unfold closed_bt in c; allsimpl.
  rw <- null_iff_nil in c; rw null_remove_nvars in c.
  discover; allsimpl; sp.
Qed.

Lemma wf_atom_eq_iff {p} :
  forall a b c d : @NTerm p,
    (wf_term a # wf_term b # wf_term c # wf_term d) <=> wf_term (mk_atom_eq a b c d).
Proof.
  introv; split; intro i.
  apply wf_atom_eq; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)) (k (nobnd d)); intros k1 k2 k3 k4.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  repeat (dest_imp k3 hyp).
  repeat (dest_imp k4 hyp).
  inversion k1; subst.
  inversion k2; subst.
  inversion k3; subst.
  inversion k4; subst; sp.
Qed.

Lemma isprog_vars_mk_atom_eq {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_atom_eq a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_atom_eq_iff; split; sp.
Qed.

Lemma isprogram_mk_atom_eq {p} :
  forall (a b c d : @NTerm p),
    isprogram (mk_atom_eq a b c d)
    <=> (isprogram a
         # isprogram b
         # isprogram c
         # isprogram d).
Proof.
  introv.
  pose proof (isprog_vars_mk_atom_eq a b c d []) as h.
  allrw <- @isprog_vars_nil_iff_isprog.
  allrw @isprogram_eq; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_can_iff {p} :
  forall lib c bterms a k,
    computes_to_val_like_in_max_k_steps lib (oterm (@Can p c) bterms) a k
    <=> a = oterm (Can c) bterms.
Proof.
  introv; split; intro comp; subst.
  apply computes_to_val_like_in_max_k_steps_can in comp; auto.
  unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps.
  dands; try (complete (left; sp)).
  induction k; simpl; sp.
  rw IHk; simpl; sp.
Qed.

Lemma computes_to_val_like_in_max_k_steps_sleep_implies {p} :
  forall lib k t v,
    computes_to_val_like_in_max_k_steps lib (mk_sleep t) v k
    -> {x : NTerm
        & {m : nat
           & k = S m
           # computes_to_val_like_in_max_k_steps lib t x m
           # ({z : Z & v = mk_axiom # x = @mk_integer p z}
              [+]
              (isexc x # x = v))}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    destruct t; ginv.
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      destruct l; try (complete (inversion comp1)).
      destruct can; inversion comp1; subst.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (@mk_integer p z) k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_can_iff; sp.
      left; exists z; sp.

    + Case "NCan".
      rw @computes_step_sleep_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc l) k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_exc_iff; sp.

    + Case "Abs".
      rw @computes_step_sleep_abs in comp1.
      remember (compute_step lib (oterm (Abs abs) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_tuni_implies {p} :
  forall lib k t v,
    computes_to_val_like_in_max_k_steps lib (mk_tuni t) v k
    -> {x : NTerm
        & {m : nat
           & k = S m
           # computes_to_val_like_in_max_k_steps lib t x m
           # ({n : nat & v = mk_uni n # x = @mk_integer p (Z.of_nat n)}
              [+]
              (isexc x # x = v))}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    destruct t; ginv.
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      destruct l; try (complete (inversion comp1)).
      csunf comp1; simpl in comp1.
      unfold compute_step_tuni in comp1; simpl in comp1.
      destruct can; allsimpl; try (complete (inversion comp1)).
      destruct (Z_le_gt_dec 0 z); inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (@mk_integer p z) k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_can_iff; sp.
      left; exists (Z.to_nat z); sp.
      rw Znat.Z2Nat.id; sp.

    + Case "NCan".
      rw @computes_step_tuni_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc l) k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_exc_iff; sp.

    + rw @computes_step_tuni_abs in comp1.
      remember (compute_step lib (oterm (Abs abs) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma alphaeqbt_nilv_r {o}:
  forall (b : @BTerm o) t,
    alpha_eq_bterm b (bterm [] t)
    -> {t' : NTerm $ b = bterm [] t' # alpha_eq t' t}.
Proof.
  introv aeq.
  apply alpha_eq_bterm_sym in aeq.
  apply alphaeqbt_nilv in aeq; exrepnd; subst.
  exists nt2; dands; eauto with slow.
Qed.

Lemma computes_step_minus_ncan {p} :
  forall lib n l,
    compute_step lib (mk_minus (oterm (@NCan p n) l))
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess t => csuccess (mk_minus t)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma computes_step_minus_abs {p} :
  forall lib o l,
    compute_step lib (mk_minus (oterm (@Abs p o) l))
    = match compute_step lib (oterm (Abs o) l) with
        | csuccess t => csuccess (mk_minus t)
        | cfailure m t => cfailure m t
      end.
Proof. sp. Qed.

Lemma computes_to_val_like_in_max_k_steps_minus_implies {p} :
  forall lib k t v,
    computes_to_val_like_in_max_k_steps lib (mk_minus t) v k
    -> {x : NTerm
        & {m : nat
           & k = S m
           # computes_to_val_like_in_max_k_steps lib t x m
           # ({z : Z & v = mk_integer (- z) # x = @mk_integer p z}
              [+]
              (isexc x # x = v))}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    destruct t; ginv.
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      destruct l; try (complete (inversion comp1)).
      csunf comp1; simpl in comp1.
      unfold compute_step_minus in comp1; simpl in comp1.
      destruct can; allsimpl; ginv.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (@mk_integer p z) k; dands; auto.
      * apply computes_to_val_like_in_max_k_steps_can_iff; sp.
      * left; exists z; sp.

    + Case "NCan".
      rw @computes_step_minus_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      inversion comp1; subst; GC.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc l) k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_exc_iff; sp.

    + rw @computes_step_minus_abs in comp1.
      remember (compute_step lib (oterm (Abs abs) l)); destruct c; inversion comp1; subst; GC.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_parallel_implies {o} :
  forall lib k (bs : list (@BTerm o)) v,
    computes_to_val_like_in_max_k_steps lib (oterm (NCan NParallel) bs) v k
    -> {x : NTerm
        & {u : NTerm
        & {bs' : list BTerm
        & {m : nat
        & k = S m
        # bs = nobnd u :: bs'
        # computes_to_val_like_in_max_k_steps lib u x m
        # (iscan x # v = mk_axiom)
          [+]
          (isexc x # x = v)}}}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    csunf comp1; allsimpl.
    destruct bs as [|b bs]; ginv.
    destruct b as [l t].
    destruct l; ginv.
    destruct t as [z|op bts]; ginv;[].
    dopid op as [can|ncan|exc|abs] Case; ginv.

    + Case "Can".
      apply compute_step_parallel_success in comp1; subst.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (oterm (Can can) bts) (oterm (Can can) bts) bs k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_can_iff; sp.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst; allunfold @nobnd; ginv.
      exists x (oterm (NCan ncan) bts) bs' (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists u; auto.

    + Case "Exc".
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc bts) (oterm Exc bts) bs k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_exc_iff; sp.

    + Case "Abs".
      remember (compute_step lib (oterm (Abs abs) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      allunfold @nobnd; ginv.
      exists x (oterm (Abs abs) bts) bs' (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists u; auto.
Qed.

Lemma isvalue_vterm {o} : forall v, !@isvalue o (vterm v).
Proof.
  introv h.
  inversion h; subst; allsimpl; tcsp.
Qed.

Lemma computes_to_value_implies_val_like {p} :
  forall lib (a b : @NTerm p),
    computes_to_value lib a b
    -> computes_to_val_like lib a b.
Proof.
  introv comp.
  unfold computes_to_val_like, computes_to_val_like_in_max_k_steps.
  unfold computes_to_value, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  left.
  destruct b as [v|op bs]; allsimpl; tcsp;[allapply @isvalue_vterm;tcsp|].
  allapply @isvalue_implies; repnd; auto.
Qed.

Lemma computes_to_exception_implies_val_like {p} :
  forall lib en (a b : @NTerm p),
    computes_to_exception lib en a b
    -> computes_to_val_like lib a (mk_exception en b).
Proof.
  introv comp.
  unfold computes_to_val_like, computes_to_val_like_in_max_k_steps.
  unfold computes_to_exception, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  right.
  constructor.
Qed.

Lemma computes_to_val_like_in_max_k_steps_0 {p} :
  forall lib (t u : @NTerm p),
    computes_to_val_like_in_max_k_steps lib t u 0 <=> (t = u # isvalue_like u).
Proof.
  introv; unfold computes_to_val_like_in_max_k_steps.
  rw @reduces_in_atmost_k_steps_0; sp.
Qed.

Definition has_value_like_k {p} lib k (t : @NTerm p) :=
  {u : NTerm & computes_to_val_like_in_max_k_steps lib t u k}.

Lemma has_value_like_0 {o} :
  forall lib (t : @NTerm o),
    has_value_like_k lib 0 t <=> isvalue_like t.
Proof.
  introv; unfold has_value_like_k; split; intro k; exrepnd.
  - allrw @computes_to_val_like_in_max_k_steps_0; repnd; subst; auto.
  - exists t; allrw @computes_to_val_like_in_max_k_steps_0; auto.
Qed.

Lemma has_value_like_S {o} :
  forall lib k (t : @NTerm o),
    has_value_like_k lib (S k) t
    <=> {u : NTerm
         & compute_step lib t = csuccess u
         # has_value_like_k lib k u}.
Proof.
  introv; unfold has_value_like_k; split; intro h; exrepnd.
  - allrw @computes_to_val_like_in_max_k_steps_S; exrepnd.
    eexists; eauto.
  - exists u0; dands; auto.
    allrw @computes_to_val_like_in_max_k_steps_S.
    eexists; eauto.
Qed.

Lemma if_has_value_like_k_ncompop_can1 {o} :
  forall lib c can bs k (t : @NTerm o) l,
    has_value_like_k
      lib k
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv r.
  - allrw @has_value_like_0; repnd.
    unfold isvalue_like in r; allsimpl; sp.
  - allrw @has_value_like_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (csunf r1; allsimpl; dcwf h)).
    dopid op as [can2|ncan2|exc2|abs2] Case.
    + exists 0; dands; try omega.
      rw @has_value_like_0; dands; eauto 3 with slow.
    + rw @compute_step_ncompop_ncan2 in r1.
      dcwf h.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; tcsp.
    + csunf r1; simpl in r1; ginv.
      dcwf h; ginv.
      exists k; sp.
    + csunf r1; simpl in r1; csunf r1; allsimpl.
      dcwf h.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; tcsp.
Qed.

Lemma if_has_value_like_k_narithop_can1 {o} :
  forall lib c can bs k (t : @NTerm o) l,
    has_value_like_k
      lib k
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv r.
  - allrw @has_value_like_0; repnd.
    unfold isvalue_like in r; allsimpl; sp.
  - allrw @has_value_like_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (csunf r1; allsimpl; dcwf h)).
    dopid op as [can2|ncan2|exc2|abs2] Case.
    + exists 0; dands; try omega.
      rw @has_value_like_0; dands; eauto 3 with slow.
    + rw @compute_step_narithop_ncan2 in r1.
      dcwf h.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; tcsp.
    + csunf r1; simpl in r1; ginv.
      dcwf h; ginv.
      exists k; sp.
    + csunf r1; simpl in r1; csunf r1; allsimpl.
      dcwf h.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; tcsp.
Qed.

Lemma has_value_like_k_lt {o} :
  forall lib k1 k2 (t : @NTerm o),
    has_value_like_k lib k1 t
    -> k1 < k2
    -> has_value_like_k lib k2 t.
Proof.
  unfold has_value_like_k; introv r l; exrepnd.
  exists u; dands; auto.
  pose proof (no_change_after_value_like lib t k1 u) as h.
  allunfold @computes_to_val_like_in_max_k_steps; repnd; dands; auto.
  repeat (autodimp h hyp); tcsp.
  pose proof (h (k2 - k1)) as hh.
  assert (k2 - k1 + k1 = k2) as e by omega.
  rw e in hh; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_if_isvalue_like {o} :
  forall lib (t u : @NTerm o) k,
    computes_to_val_like_in_max_k_steps lib t u k
    -> isvalue_like t
    -> t = u.
Proof.
  introv comp isv.
  unfold computes_to_val_like_in_max_k_steps in comp; repnd.
  apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; auto.
Qed.

Lemma if_has_value_like_k_cbv_primarg {o} :
  forall lib k (t : @NTerm o) bs,
    has_value_like_k lib k (oterm (NCan NCbv) (bterm [] t :: bs))
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv r.

  - allrw @has_value_like_0; repnd.
    unfold isvalue_like in r; allsimpl; sp.

  - allrw @has_value_like_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists 0; dands; try omega.
      rw @has_value_like_0; dands; eauto 3 with slow; simpl; sp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S; exists n; sp.

    + Case "Exc".
      csunf r1; allsimpl; ginv.
      unfold has_value_like_k in r0; exrepnd.
      apply computes_to_val_like_in_max_k_steps_if_isvalue_like in r1; subst; tcsp.
      exists 0; dands; try omega.
      rw @has_value_like_0; dands; eauto 3 with slow.

    + Case "Abs".
      csunf r1; allsimpl; csunf r1; allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try omega.
      rw @has_value_like_S; exists n; sp.
Qed.

Lemma isvalue_like_integer {o} :
  forall z, @isvalue_like o (mk_integer z).
Proof.
  introv; unfold isvalue_like; simpl; sp.
Qed.
Hint Resolve isvalue_like_integer : slow.

Lemma isvalue_like_uni {o} :
  forall n, @isvalue_like o (mk_uni n).
Proof.
  introv; unfold isvalue_like; simpl; sp.
Qed.
Hint Resolve isvalue_like_uni : slow.

Lemma if_has_value_like_k_ncan_primarg {o} :
  forall lib ncan k (t : @NTerm o) bs,
    has_value_like_k lib k (oterm (NCan ncan) (bterm [] t :: bs))
    -> {j : nat & j < k # has_value_like_k lib j t}.
Proof.
  induction k; introv r.

  - allrw @has_value_like_0.
    unfold isvalue_like in r; allsimpl; sp.

  - allrw @has_value_like_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists 0; dands; try omega.
      rw @has_value_like_0; eauto 3 with slow.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd; auto.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; sp.

    + Case "Exc".
      csunf r1; allsimpl.
      apply compute_step_catch_success in r1.
      dorn r1; exrepnd; subst; allsimpl.

      * exists 0; dands; try omega.
        rw @has_value_like_0; eauto 3 with slow.

      * exists 0; dands; try omega.
        unfold has_value_like_k in r0; exrepnd.
        apply computes_to_val_like_in_max_k_steps_if_isvalue_like in r1; eauto 3 with slow; subst.
        rw @has_value_like_0; eauto 3 with slow.

    + Case "Abs".
      csunf r1; allsimpl; csunf r1; allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd; auto.
      exists (S j); dands; try omega.
      rw @has_value_like_S.
      exists n; sp.
Qed.

Lemma closed_mk_vbot {o} :
  forall v, @closed o (mk_vbot v).
Proof.
  introv.
  unfold closed, mk_vbot; simpl.
  rw remove_nvars_eq; simpl; auto.
Qed.
Hint Resolve closed_mk_vbot : slow.

Lemma alphaeq_preserves_computes_to_val_like_in_max_k_steps {o} :
  forall lib k (t1 t2 : @NTerm o) u,
    nt_wf t1
    -> alpha_eq t1 t2
    -> computes_to_val_like_in_max_k_steps lib t1 u k
    -> {v : NTerm & computes_to_val_like_in_max_k_steps lib t2 v k # alpha_eq u v}.
Proof.
  introv wf aeq hv.
  allunfold @computes_to_val_like_in_max_k_steps; repnd.
  pose proof (reduces_in_atmost_k_steps_alpha lib t1 t2) as h; repeat (autodimp h hyp).
  applydup h in hv0; exrepnd.
  exists t2'; dands; auto.
  eapply alpha_eq_preserves_isvalue_like; eauto.
Qed.

Lemma alphaeq_preserves_has_value_like_k {o} :
  forall lib k (t1 t2 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> has_value_like_k lib k t1
    -> has_value_like_k lib k t2.
Proof.
  introv wf aeq hv.
  allunfold @has_value_like_k; exrepnd.
  eapply alphaeq_preserves_computes_to_val_like_in_max_k_steps in hv0; eauto.
  exrepnd.
  exists v; auto.
Qed.

Lemma has_value_like_k_ren_utokens {o} :
  forall lib k (t : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (get_utokens_library lib) (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens_lib lib t))
    -> has_value_like_k lib k t
    -> has_value_like_k lib k (ren_utokens ren t).
Proof.
  introv wf norep disjlib disj hvl.
  allunfold @has_value_like_k; exrepnd.
  allunfold @computes_to_val_like_in_max_k_steps; repnd.
  apply (reduces_in_atmost_k_steps_ren_utokens _ _ _ _ ren) in hvl1; auto.
  exists (ren_utokens ren u); dands; eauto with slow.
Qed.

Lemma reduces_in_atmost_k_steps_refl {o} :
  forall (lib : pre_library) (k : nat) (t : @NTerm o),
    isvalue_like t
    -> reduces_in_atmost_k_steps lib t t k.
Proof.
  induction k; introv isvl.
  - rw @reduces_in_atmost_k_steps_0; auto.
  - rw @reduces_in_atmost_k_steps_S.
    exists t; dands; tcsp.
    apply compute_step_value_like; auto.
Qed.

Lemma eqset_free_vars_disjoint {o} :
  forall (t : @NTerm o) (sub : Substitution),
  eqset (free_vars (lsubst t sub))
        (remove_nvars (dom_sub sub) (free_vars t)
                      ++ sub_free_vars (sub_keep_first sub (free_vars t))).
Proof.
  introv; pose proof (eqvars_free_vars_disjoint t sub) as h; rw eqvars_prop in h; auto.
Qed.

Lemma has_value_like_k_fresh_implies {o} :
  forall lib k a v (t : @NTerm o),
    wf_term t
    -> !LIn a (get_utokens_lib lib t)
    -> has_value_like_k lib k (mk_fresh v t)
    -> has_value_like_k lib k (subst t v (mk_utoken a)).
Proof.
  introv wt nia hvl.
  allunfold @has_value_like_k; exrepnd.
  allunfold @computes_to_val_like_in_max_k_steps; exrepnd.
  revert dependent u.
  revert dependent t.
  revert dependent a.
  induction k; introv wt nia r isvl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isvl; repndors; inversion isvl.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_ncan_bterm_cons_success in r1; repnd; subst; GC.
    repndors; exrepnd; subst; allsimpl; GC.
    + apply reduces_in_atmost_k_steps_implies_reduces_to in r0.
      apply reduces_in_atmost_k_step_fresh_id in r0; tcsp.
    + apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      exists (subst t v (mk_utoken a)); dands; eauto 4 with slow.
      apply reduces_in_atmost_k_steps_refl; eauto with slow.
    + repnd; subst.
      pose proof (compute_step_subst_utoken lib t x [(v,mk_utoken (get_fresh_atom lib t))]) as h.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp h hyp); try (apply get_fresh_atom_prop_and_lib); eauto 3 with slow.

      { apply nr_ut_sub_cons; eauto 3 with slow.
        intro i; apply get_fresh_atom_prop_and_lib. }

      exrepnd.
      pose proof (h0 [(v,mk_utoken a)]) as q; clear h0; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp q hyp); exrepnd.

      allrw @fold_subst.

      assert (wf_term x) as wfx.
      { eapply compute_step_preserves_wf;[exact r3|].
        apply wf_term_subst; eauto with slow. }

      assert (!LIn v (free_vars x)) as nivx.
      { intro j; apply compute_step_preserves in r3; repnd; eauto 3 with slow.
        rw subvars_prop in r2; apply r2 in j; clear r2.
        apply eqset_free_vars_disjoint in j; allsimpl.
        allrw in_app_iff; allrw in_remove_nvars; allsimpl; boolvar; allsimpl; tcsp. }

      pose proof (IHk a (subst_utokens x [(get_fresh_atom lib t, mk_var v)])) as q; clear IHk.
      repeat (autodimp q hyp).

      { apply wf_subst_utokens; eauto 3 with slow. }

      { intro j; apply get_utokens_lib_subst_utokens_subset in j; allsimpl.
        unfold get_utokens_lib in *; simpl in *.
        unfold get_utokens_utok_ren in j; allsimpl; allrw app_nil_r.
        allrw in_app_iff; allrw not_over_or; repnd.
        repndors; tcsp.
        rw in_remove in j; repnd.
        apply alphaeq_preserves_utokens in h1; rw h1 in j.
        apply get_utokens_lib_subst in j; boolvar; allsimpl; allrw in_app_iff;
          tcsp; allsimpl; allrw not_over_or; repnd; repndors; tcsp.

        - apply (get_utokens_subset_get_utokens_lib lib) in j; unfold get_utokens_lib in j; apply h4 in j.
          allrw in_app_iff; tcsp.

        - apply (get_utokens_subset_get_utokens_lib lib) in j; unfold get_utokens_lib in j; apply h4 in j.
          allrw in_app_iff; tcsp. }

      pose proof (q u) as ih; clear q.
      repeat (autodimp ih hyp); exrepnd.

      pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom lib t) v) as aeq1.
      repeat (autodimp aeq1 hyp).

      pose proof (alpha_eq_ren_utokens
                    (subst (subst_utokens x [(get_fresh_atom lib t, mk_var v)]) v
                           (mk_utoken (get_fresh_atom lib t)))
                    x [(get_fresh_atom lib t, a)] aeq1) as aeq2.
      rw @subst_ren_utokens in aeq2; allsimpl; fold_terms.
      unfold ren_atom in aeq2; allsimpl; boolvar; tcsp.
      rw @ren_utokens_trivial in aeq2;
        [|simpl; apply disjoint_singleton_l; intro i;
          apply get_utokens_subst_utokens_subset in i; allsimpl;
          unfold get_utokens_utok_ren in i; allsimpl; rw app_nil_r in i;
          rw in_remove in i; repnd; GC;
          apply alphaeq_preserves_utokens in h1; rw h1 in i;
          apply get_utokens_subst in i; allsimpl; boolvar; allrw app_nil_r;
          allrw in_app_iff; repndors; tcsp].

      clear aeq1.

      pose proof (alpha_eq_ren_utokens
                    x (subst w v (mk_utoken (get_fresh_atom lib t)))
                    [(get_fresh_atom lib t, a)] h1) as aeq3.
      rw @subst_ren_utokens in aeq3; allsimpl; fold_terms.
      unfold ren_atom in aeq3; allsimpl; boolvar; tcsp.
      rw (ren_utokens_trivial [(get_fresh_atom lib t, a)] w) in aeq3;
        [|simpl; apply disjoint_singleton_l; intro i;
          apply (get_utokens_subset_get_utokens_lib lib) in i;
          apply h4 in i; apply get_fresh_atom_prop_and_lib in i; sp]; GC.

      eapply alpha_eq_trans in aeq3;[|exact aeq2]; clear aeq2.
      apply alpha_eq_sym in aeq3.
      eapply alpha_eq_trans in aeq3;[|exact q0]; clear q0.

      dup ih1 as ih2.
      eapply reduces_in_atmost_k_steps_alpha in ih2;
        [|apply nt_wf_subst; eauto 3 with slow;
          apply nt_wf_eq; apply wf_subst_utokens;
          eauto 3 with slow
         |apply alpha_eq_sym in aeq3; apply aeq3];[];exrepnd.
      rename t2' into s'.

      exists s'; dands; eauto 2 with slow.
      rw @reduces_in_atmost_k_steps_S.
      eexists; dands; eauto.
Qed.

Lemma has_value_like_k_vbot {o} :
  forall (lib : @pre_library o) k v,
    !has_value_like_k lib k (mk_vbot v).
Proof.
  introv hv.
  unfold has_value_like_k, computes_to_val_like_in_max_k_steps in hv; exrepnd.
  apply reduces_in_atmost_k_steps_vbot in hv1; tcsp.
Qed.

Lemma has_value_like_k_fresh_id {o} :
  forall (lib : @pre_library o) k v,
    !has_value_like_k lib k (mk_fresh v (mk_var v)).
Proof.
  introv hv.
  unfold has_value_like_k, computes_to_val_like_in_max_k_steps in hv; exrepnd.
  pose proof (reduces_in_atmost_k_step_fresh_id lib v u) as h.
  autodimp h hyp.
  eauto 3 with slow.
Qed.

Definition computes_to_can {p} lib (t1 t2 : @NTerm p) :=
  reduces_to lib t1 t2
  # iscan t2.

Lemma computes_to_exception_mk_less {o} :
  forall lib (a b c d : @NTerm o) n e,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_exception lib n (mk_less a b c d) e
    -> {k1 : Z
        & {k2 : Z
        & reduces_to lib a (mk_integer k1)
        # reduces_to lib b (mk_integer k2)
        # (((k1 < k2)%Z # computes_to_exception lib n c e)
           [+]
           ((k2 <= k1)%Z # computes_to_exception lib n d e)
          )}}
       [+] computes_to_exception lib n a e
       [+] {z : Z
            & reduces_to lib a (mk_integer z)
            # computes_to_exception lib n b e}.
Proof.
  introv wfa wfb wfc wfd comp.
  unfold computes_to_exception, reduces_to in comp; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpLess a b c d (mk_exception n e)) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv.

  - left.
    allunfold @computes_to_can_in_max_k_steps; repnd.
    allunfold @spcan; fold_terms.
    exists i1 i2; dands; eauto with slow.
    boolvar;[left|right]; dands; auto;
    allunfold @computes_to_val_like_in_max_k_steps; repnd;
    exists (k - (k1 + k2 + 1)); auto.

  - right; left.
    exists k1; auto.

  - right; right; allsimpl.
    exists i; dands; auto.
    + allunfold @computes_to_can_in_max_k_steps; repnd.
      unfold computes_to_can; dands; eauto with slow.
    + exists k2; auto.
Qed.

Lemma computes_to_can_in_max_k_steps_implies_reduces_in_atmost_k_steps {o} :
  forall lib k (t : @NTerm o) u,
    computes_to_can_in_max_k_steps lib k t u
    -> reduces_in_atmost_k_steps lib t u k.
Proof.
  introv comp.
  unfold computes_to_can_in_max_k_steps in comp; sp.
Qed.
Hint Resolve computes_to_can_in_max_k_steps_implies_reduces_in_atmost_k_steps : slow.

Lemma computes_to_val_like_in_max_k_steps_implies_has_value_like_k {o} :
  forall lib (t u : @NTerm o) k,
    computes_to_val_like_in_max_k_steps lib t u k
    -> has_value_like_k lib k t.
Proof.
  introv comp.
  unfold has_value_like_k.
  exists u; sp.
Qed.
Hint Resolve computes_to_val_like_in_max_k_steps_implies_has_value_like_k : slow.

Lemma has_value_like_k_mk_less {o} :
  forall lib k (a b c d : @NTerm o),
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> has_value_like_k lib k (mk_less a b c d)
    -> ({k1 : nat
         & {u : NTerm
         & {e : NTerm
         & k1 + 1 <= k
         # computes_to_exception_in_max_k_steps lib u a e k1
         # reduces_in_atmost_k_steps
             lib
             (mk_less a b c d)
             (mk_less (mk_exception u e) b c d) k1 }}}
        [+]
        {k1 : nat
         & {k2 : nat
         & {z : Z
         & {u : NTerm
         & {e : NTerm
         & k1 + k2 + 1 <= k
         # reduces_in_atmost_k_steps lib a (mk_integer z) k1
         # computes_to_exception_in_max_k_steps lib u b e k2
         # reduces_in_atmost_k_steps
             lib
             (mk_less a b c d)
             (mk_less (mk_integer z) (mk_exception u e) c d)
             (k1 + k2)}}}}}
        [+]
        {k1 : nat
         & {k2 : nat
         & {i1 : Z
         & {i2 : Z
         & k1 + k2 + 1 <= k
         # reduces_in_atmost_k_steps lib a (mk_integer i1) k1
         # reduces_in_atmost_k_steps lib b (mk_integer i2) k2
         # has_value_like_k
             lib
             (k - (k1 + k2 + 1))
             (if Z_lt_le_dec i1 i2 then c else d)
         # reduces_in_atmost_k_steps
             lib
             (mk_less a b c d)
             (mk_less (mk_integer i1) (mk_integer i2) c d)
             (k1 + k2) }}}}).
Proof.
  introv wa wb wc wd hv.
  unfold has_value_like_k in hv; exrepnd.
  apply computes_to_val_like_in_max_k_steps_comp_implies in hv0;
    repndors; exrepnd; auto;[|idtac|].

  - repndors; exrepnd; tcsp;ginv;[].
    allunfold @spcan; fold_terms.
    right; right.
    exists k1 k2 i1 i2.
    dands; eauto 3 with slow.
    boolvar; eauto 3 with slow.

  - subst; fold_terms.
    left.
    exists k1 en e; sp.

  - subst; fold_terms.
    right; left.
    repndors; exrepnd; ginv; allsimpl.
    exists k1 k2 i en e; dands; eauto 3 with slow.
Qed.
