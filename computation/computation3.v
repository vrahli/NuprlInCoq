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


Require Export subst_tacs2.
Require Export computation_preserve1.
(*Require Export list. (* WTF!! *)*)
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(* begin hide *)

(* Definition simulation_relation_step (n:nat )(P: (list NTerm )-> (list NTerm ) -> Type):=
  forall (l1 l2: list NTerm),
    length l1 = n
    -> length l2 = n
    -> (forall m, m<n -> compute_step (selectnt m l1) = csuccess (selectnt m l2))
    -> P l1 l2.

Definition simulation_relation (n:nat )(P: (list NTerm )-> (list NTerm ) -> Type):=
  forall (l1 l2: list NTerm),
    length l1 = n
    -> length l2 = n
    -> (forall m, m<n -> computes_to_value (selectnt m l1) (selectnt m l2))
    -> P l1 l2.
*)

(*
Lemma computek_preserves_nt_wf :
  forall k t1 t2,
    compute_at_most_k_steps k t1 = csuccess t2
    -> nt_wf t1
    -> nt_wf t2.
Proof.
  induction k; intros ? ?  Hck Hpt1; inverts Hck as Hck; auto.
  remember (compute_at_most_k_steps k t1) as rec. destruct rec; inverts Hck as Hck.
  symmetry in Heqrec. inverts Hck as Hck. apply IHk in Heqrec; auto.
  apply preserve_nt_wf_compute_step in Hck; auto.
Qed.

Theorem computes_to_ovalue_preserves_nt_wf :
  forall t1 t2,
    computes_to_ovalue t1 t2
    -> nt_wf t1
    -> nt_wf t2.
Proof.
  intros ? ? Hcv Hpt1. inverts Hcv as Hcv. inverts Hcv as Hcv.
  apply computek_preserves_nt_wf in Hcv; auto.
Qed.
*)

(*
Theorem preserve_program : forall (t1 t2 :NTerm),
  (computes_to_value t1 t2) -> (isprogram t1) ->(isprogram t2).
Proof.
 intros ? ? Hcv Hpt1. inverts Hcv as Hcv. inverts Hcv as Hcv.
  apply computek_preserves_program in Hcv; auto.
Qed.
*)


(*
Lemma lsubst_subst :
  forall t v arg sub,
    subst (lsubst t (sub_filter sub [v])) v (lsubst arg sub)
    = lsubst (subst t v arg) sub.
Proof.
  intro. nterm_ind t Case.

  - Case "vterm"; sp; allsimpl.
    unfold subst; simpl.
    remember (beq_var v n); destruct b.
    apply beq_var_eq in Heqb; subst.
    rewrite sub_find_sub_filter; simpl.
    rewrite <- beq_var_refl; auto.
    left; auto.
    symmetry in Heqb.
    apply beq_var_false_not_eq in Heqb.
Qed.
*)

(*
Lemma compute_step_preserves_lsubst :
  forall t1 t2 sub,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> compute_step t1 = csuccess t2
    -> compute_step (lsubst t1 sub) = csuccess (lsubst t2 sub).
Proof.
  intro. nterm_ind t1 Case.

  - Case "vterm"; sp; allsimpl.
    inversion H0.

  - Case "oterm".
    rename H into IHind.
    intros t2 sub Hsub Hcomp.
    dopid o as [c| nc] SCase.

    + SCase "Can".
      allsimpl; inverts Hcomp; auto.

    + SCase "NCan".
      (*simpl in Hcomp.*)
      dlist lbt SSCase as [| arg1].
      try (inverts Hcomp; fail).
      SSCase "conscase".
      simpl in Hcomp;
        destruct arg1 as [arg1vs arg1nt];
        dlist arg1vs SSSCase as [|arg1v1];
        destruct arg1nt as [v89| arg1o arg1bts];
        inversion Hcomp;
        thin_trivials.
      dopid arg1o as [arg1c | arg1nc ] SSSSCase.

      * SSSSCase "Can". (* arg1 (principle in all cases) is canonical. *)
        dopid_noncan nc SSSSSCase.

        SSSSSCase "NApply".
        applydup compute_step_apply_success in Hcomp; sp; subst.
        unfold compute_step_apply in Hcomp.
        (* XXXXXXXXXXXXXXXX *)
        inversion Hcomp; subst.
        simpl.
        rewrite sub_filter_nil_r.
        rewrite bvar_renamings_subst_isprogram; simpl; auto.

        apply subst_preserves_wf; auto.
        generalize (Hbf (bterm [] (oterm (Can NLambda) [bterm [v] b]))); simpl; sp.
        dimp H.
        inversion hyp; subst.
        inversion H1; subst.
        generalize (H3 (bterm [v] b)); simpl; sp.
        dimp H0.
        inversion hyp0; subst; auto.
        generalize (Hbf (bterm [] arg)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.

        SSSSSCase "NFix".
        simpl in Hcomp.
        applydup compute_step_fix_success in Hcomp; sp; subst.
        unfold compute_step_fix in Hcomp.
        inversion Hcomp; subst.
        constructor; sp.
        allsimpl; sp; subst.
        constructor.
        generalize (Hbf (bterm [] (oterm (Can arg1c) arg1bts))); sp.
        dimp H.
        inversion hyp; subst; auto.
        constructor.
        constructor; sp.

        SSSSSCase "NSpread".
        simpl in Hcomp.
        applydup compute_step_spread_success in Hcomp; sp; subst.
        inversion Hcomp; subst; allsimpl.
        apply lsubst_preserves_wf; allsimpl; sp.
        generalize (Hbf (bterm [va, vb] arg)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.
        inversion H; subst.
        generalize (Hbf (bterm [] ((|u, b|)))); sp.
        dimp H0.
        inversion hyp; subst.
        inversion H2; subst.
        generalize (H4 (bterm [] u)); simpl; sp.
        dimp H1.
        inversion hyp0; subst; auto.
        inversion H; subst.
        generalize (Hbf (bterm [] ((|a, u|)))); sp.
        dimp H0.
        inversion hyp; subst.
        inversion H2; subst.
        generalize (H4 (bterm [] u)); simpl; sp.
        dimp H1.
        inversion hyp0; subst; auto.

        SSSSSCase "NDecide".
        simpl in Hcomp.
        applydup compute_step_decide_success in Hcomp; sp; subst.
        inversion Hcomp; subst; allsimpl.
        apply lsubst_preserves_wf; allsimpl; sp.
        generalize (Hbf (bterm [v1] t1)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.
        inversion H; subst.
        generalize (Hbf (bterm [] (oterm (Can NInl) [bterm [] u0]))); sp.
        dimp H0.
        inversion hyp; subst.
        inversion H2; subst.
        generalize (H4 (bterm [] u0)); simpl; sp.
        dimp H1.
        inversion hyp0; subst; auto.
        inversion Hcomp; subst; allsimpl.
        apply lsubst_preserves_wf; allsimpl; sp.
        generalize (Hbf (bterm [v2] t0)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.
        inversion H; subst.
        generalize (Hbf (bterm [] (oterm (Can NInr) [bterm [] u0]))); sp.
        dimp H0.
        inversion hyp; subst.
        inversion H2; subst.
        generalize (H4 (bterm [] u0)); simpl; sp.
        dimp H1.
        inversion hyp0; subst; auto.

        SSSSSCase "NCbv".
        simpl in Hcomp.
        applydup compute_step_cbv_success in Hcomp; sp; subst.
        inversion Hcomp; subst; allsimpl.
        apply lsubst_preserves_wf; allsimpl; sp.
        generalize (Hbf (bterm [v] x)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.
        inversion H; subst.
        generalize (Hbf (bterm [] (oterm (Can arg1c) arg1bts))); sp.
        dimp H0.
        inversion hyp; subst; auto.

        SSSSSCase "NCompOp".
        acdmit.

        SSSSSCase "NArithOp".
        acdmit.

        SSSSSCase "NCanTest".
        simpl in Hcomp.
        applydup compute_step_can_test_success in Hcomp; sp; subst.
        destruct (canonical_form_test_for c arg1c).
        generalize (Hbf (bterm [] arg2nt)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.
        generalize (Hbf (bterm [] arg3nt)); simpl; sp.
        dimp H.
        inversion hyp; subst; auto.

      * SSSSCase "NCan".
        unfold compute_step in Hcomp; fold (compute_step (oterm (NCan arg1nc) arg1bts)) in Hcomp.
        remember (compute_step (oterm (NCan arg1nc) arg1bts)) as crt2s.
        destruct crt2s; inversion Hcomp; subst.
        symmetry in Heqcrt2s.
        apply IHind with (lv := []) in Heqcrt2s; auto; simpl.
        constructor; simpl; sp; subst.
        constructor; auto.
        apply Hbf; simpl; right; auto.
        left; auto.
        inversion Hiswf; subst.
        generalize (H1 (bterm [] (oterm (NCan arg1nc) arg1bts))); simpl; sp.
        dimp H.
        inversion hyp; subst; sp.
Qed.

Theorem computes_to_value_lsubst :
  forall t1 t2 sub,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> computes_to_value t1 t2
    -> computes_to_value (lsubst t1 sub) t2.
Proof.
  intros.
  allunfold computes_to_value; allunfold reduces_to; sp.
  rewrite compute_at_most_k_steps_eq_f in H0.
  revert t1 t2 H1 H0.
  induction k; allsimpl; sp.
  inversion H0; subst.
  exists 0; simpl.
  rewrite lsubst_trivial; sp.
  apply H with (v := v); sp.
  apply isvalue_closed in H1.
  unfold closed in H1.
  rewrite H1 in H3; allsimpl; sp.

  remember (compute_step t1); destruct c.
  applydup IHk in H0; sp.
Qed.*)

Lemma compute_step_mk_cbv_ncan {p} :
  forall lib c l v u,
    compute_step lib (mk_cbv (oterm (@NCan p c) l) v u)
    = match compute_step lib (oterm (NCan c) l) with
        | csuccess f => csuccess (mk_cbv f v u)
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_mk_cbv_abs {o} :
  forall (lib : @library o) x l v u,
    compute_step lib (mk_cbv (oterm (Abs x) l) v u)
    = match compute_step_lib lib x l with
        | csuccess f => csuccess (mk_cbv f v u)
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; rw @compute_step_eq_unfold; sp.
Qed.

Lemma reduces_to_apply_id {p} :
  forall lib (t : @NTerm p), reduces_to lib (mk_apply mk_id t) t.
Proof.
  unfold reduces_to; sp.
  exists 1.
  simpl.
  unfold subst; simpl; sp.
Qed.

Hint Immediate reduces_to_apply_id.

Lemma reduces_toc_apply_id {p} :
  forall lib (t : @CTerm p), reduces_toc lib (mkc_apply mkc_id t) t.
Proof.
  destruct t; unfold reduces_toc; simpl.
  fold (@mk_id p); sp.
Qed.

Hint Immediate reduces_toc_apply_id.

Lemma is_compute_step_apply {p} :
  forall lib c l a,
    @compute_step p lib (mk_apply (oterm (Can c) l) a)
    = compute_step_apply c (mk_apply (oterm (Can c) l) a) l [nobnd a].
Proof.
  sp.
Qed.

Lemma is_compute_step_decide {p} :
  forall lib c l x f y g,
    compute_step lib (mk_decide (oterm (@Can p c) l) x f y g)
    = compute_step_decide c (mk_decide (oterm (Can c) l) x f y g) l [bterm [x] f, bterm [y] g].
Proof.
  sp.
Qed.



(*
Lemma compute_at_most_k_steps_marker {o} :
  forall (lib : @library o) k t,
    ismrk lib t
    -> compute_at_most_k_steps lib k t
       = csuccess t.
Proof.
  induction k; introv ism; simpl; tcsp.
  rw IHk; auto.
Qed.
*)

(*
Lemma reduces_in_atmost_k_steps_marker {o} :
  forall (lib : @library o) k mrk l v,
    reduces_in_atmost_k_steps lib (oterm (Mrk mrk) l) v k
    -> v = oterm (Mrk mrk) l.
Proof.
  introv h.
  unfold reduces_in_atmost_k_steps in h.
  rw @compute_at_most_k_steps_marker in h; ginv; auto.
Qed.
*)

(*
Lemma ismrk_implies {o} :
  forall lib (t : @NTerm o),
    ismrk lib t ->
    {opabs : opabs
     & {bs : list BTerm
     & t = oterm (Abs opabs) bs
     # find_entry lib opabs bs = None}}.
Proof.
  introv ism.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  dopid op as [can|ncan|exc|abs] Case; allsimpl; tcsp.
  eexists; eexists; dands; eauto.
Qed.
 *)

(*
Lemma reduces_to_marker {p} :
  forall lib e (t : @NTerm p), ismrk lib e -> reduces_to lib e t -> t = e.
Proof.
  introv ism r.
  unfold reduces_to in r; exrepnd.
  revert e t ism r0.
  induction k; introv ism comp.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply ismrk_implies in ism; exrepnd; subst.
    csunf comp1; allsimpl.
    apply compute_step_lib_success in comp1; exrepnd; subst.
    unfold found_entry in comp2.
    rw ism1 in comp2; ginv.
Qed.
 *)

(*
Lemma compute_at_most_k_stepsf_marker {o} :
  forall lib k (t u : @NTerm o),
    ismrk lib t
    -> compute_at_most_k_stepsf lib k t = csuccess u
    -> u = t.
Proof.
  introv i c.
  apply (reduces_to_marker lib t u); auto.
  exists k.
  unfold reduces_in_atmost_k_steps.
  rw @compute_at_most_k_steps_eq_f; auto.
Qed.
 *)

Lemma iscan_mk_exception {o} :
  forall n e : @NTerm o, iscan (mk_exception n e) -> False.
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; ginv.
Qed.

Lemma isvalue_mk_exception {o} :
  forall n e : @NTerm o, isvalue (mk_exception n e) -> False.
Proof.
  introv isv.
  inversion isv as [? isp isc]; subst.
  apply iscan_mk_exception in isc; sp.
Qed.

Lemma cbv_reduce0 {pp} :
  forall lib t v u,
    isprog t
    -> @isprog pp u
    -> hasvalue lib t
    -> reduces_to lib (mk_cbv t v u) u.
Proof.
  unfold hasvalue, computes_to_value, reduces_to.
  introv ispt ispu comp; exrepnd.
  revert t comp2 ispt.
  induction k; simpl; sp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists 1; rw @reduces_in_atmost_k_steps_S.
    inversion comp0 as [? isp isc]; subst.
    rw @compute_step_eq_unfold; simpl.

    apply iscan_implies in isc; repndors; exrepnd; subst;
    eexists; dands; eauto;
    rw @reduces_in_atmost_k_steps_0; unfold apply_bterm; simpl;
    rewrite lsubst_trivial2; simpl; sp; inj;
    rw @isprogram_eq; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @preserve_compute_step in comp2;
      try (complete (allrw @isprogram_eq; sp)).
    allrw @isprogram_eq.
    applydup IHk in comp1; tcsp; exrepnd.
    destruct t as [x|op bs].
    { csunf comp2; ginv. }
    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      rw @compute_step_eq_unfold in comp2; allsimpl; ginv.
      exists k0; auto.

    + Case "NCan".
      exists (S k0); allrw @reduces_in_atmost_k_steps_S.
      rw @compute_step_eq_unfold; simpl.
      rw comp2; simpl.
      eexists; dands; eauto.

    + Case "Exc".
      provefalse.
      rw @compute_step_eq_unfold in comp2; allsimpl; ginv.
      allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst; ginv.
      fold_terms.
      allrw (@fold_exception).
      pose proof (reduces_to_exception lib (mk_exception a t) t') as ee;
        repeat (autodimp ee hyp); sp; try (exists k; auto).
      subst.
      allapply @isvalue_mk_exception; sp.

    + Case "Abs".
      exists (S k0); allrw @reduces_in_atmost_k_steps_S.
      rw @compute_step_eq_unfold; simpl.
      rw comp2; simpl.
      eexists; dands; eauto.
Qed.

Lemma isvalue_ncan {o} :
  forall nc (bs : list (@BTerm o)),
    isvalue (oterm (NCan nc) bs) -> False.
Proof.
  introv isv.
  inversion isv as [? isp isc]; subst.
  apply iscan_implies in isc; repndors; exrepnd; ginv.
Qed.

Lemma isvalue_exc {o} :
  forall (bs : list (@BTerm o)),
    isvalue (oterm Exc bs) -> False.
Proof.
  introv isv.
  inversion isv as [? isp isc]; subst.
  apply iscan_implies in isc; repndors; exrepnd; ginv.
Qed.

Lemma isvalue_abs {o} :
  forall a (bs : list (@BTerm o)),
    isvalue (oterm (Abs a) bs) -> False.
Proof.
  introv isv.
  inversion isv as [? isp isc]; subst.
  apply iscan_implies in isc; repndors; exrepnd; ginv.
Qed.

Lemma isprog_vterm {o} :
  forall v, @isprog o (vterm v) -> False.
Proof.
  introv isp.
  inversion isp; allsimpl; allapply not_assert_false; sp.
Qed.

Lemma cbv_reduce {p} :
  forall lib t v u x,
    @isprog p t
    -> computes_to_value lib t x
    -> reduces_to lib (mk_cbv t v u) (subst u v x).
Proof.
  unfold hasvalue, computes_to_value, reduces_to.
  introv isp comp; exrepnd.
  revert dependent t.
  induction k; simpl; introv isp e.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists 1; rw @reduces_in_atmost_k_steps_S.
    rw @compute_step_eq_unfold; simpl.
    destruct x as [x|op bs].
    { allapply @isprog_vterm; sp. }

    dopid op as [c|nc|exc|abs] Case; tcsp;
    try (apply isvalue_ncan in comp; sp);
    try (apply isvalue_exc in comp; sp);
    try (apply isvalue_abs in comp; sp).

    unfold apply_bterm; simpl.
    eexists; dands; eauto.
    rw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    applydup @preserve_compute_step in e1;
      try (complete (allrw @isprogram_eq; sp)).
    allrw @isprogram_eq.
    applydup IHk in e0; sp.
    destruct t as [z|op bs].
    { allapply @isprog_vterm; sp. }

    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      rw @compute_step_eq_unfold in e1; allsimpl; ginv.
      exists k0; sp.

    + Case "NCan".
      exists (S k0); allrw @reduces_in_atmost_k_steps_S.
      rw @compute_step_eq_unfold; simpl; rw e1; simpl.
      eexists; dands; eauto.

    + Case "Exc".
      provefalse.
      allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst.
      fold_terms.
      allrw @fold_exception.
      rw @compute_step_exception in e1; sp; ginv.
      pose proof (reduces_to_exception lib (mk_exception a t) x) as ee;
        repeat (autodimp ee hyp); sp; try (exists k; auto).
      subst.
      allapply @isvalue_mk_exception; sp.

    + Case "Abs".
      exists (S k0); allrw @reduces_in_atmost_k_steps_S.
      rw @compute_step_eq_unfold; simpl; rw e1; simpl.
      eexists; dands; eauto.
Qed.

Lemma if_hasvalue_cbv0 {p} :
  forall lib t v u,
    @isprog p t
    -> hasvalue lib (mk_cbv t v u)
    -> hasvalue lib t.
Proof.
  unfold hasvalue, computes_to_value, reduces_to, reduces_in_atmost_k_steps.
  intros lib t v u pt hv; exrepd.
  allrewrite @compute_at_most_k_steps_eq_f.
  revert t pt e.
  induction k; simpl; introv isp comp; ginv; tcsp.

  - allapply @isvalue_ncan; sp.

  - destruct t as [x|op bs].
    { allapply @isprog_vterm; sp. }

    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      exists (oterm (Can c) bs); sp.
      exists 0; simpl; sp.
      constructor; simpl; auto.
      rw @isprogram_eq; sp.

    + Case "NCan".
      unfold mk_cbv, nobnd in comp.
      rw @compute_step_ncan_ncan in comp.
      remember (compute_step lib (oterm (NCan nc) bs)); symmetry in Heqc; destruct c;
      try (complete (inversion comp)).

      allrw @fold_nobnd; allrw @fold_cbv.
      assert (isprog n) as in0 by (apply preserve_compute_step in Heqc; sp; allrw @isprogram_eq; sp).
      applydup IHk in in0; sp.
      exists t'0; sp.
      exists (S k0).
      allrewrite @compute_at_most_k_steps_eq_f.
      rewrite compute_at_most_k_stepsf_S.
      rewrite Heqc; sp.

   + Case "Exc".
     simpl in comp.
     provefalse.
     allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst.
     fold_terms.
     allrw @fold_exception.
     rw <- @compute_at_most_k_steps_eq_f in comp.
     generalize (reduces_to_exception lib (mk_exception a t) t');
       intro ee; repeat (autodimp ee hyp); sp; try (exists k; auto).
     subst.
     apply isvalue_exc in i; sp.

   + Case "Abs".
     unfold mk_cbv, nobnd in comp.
     rw @compute_step_ncan_abs in comp.
     remember (compute_step_lib lib abs bs) as c; destruct c; try (complete (inversion comp)).
     pose proof (compute_step_lib_success lib abs bs n) as h.
     autodimp h hyp; exrepnd; subst.
     allrw @fold_nobnd; allrw @fold_cbv.

     assert (isprog (mk_instance vars bs rhs)) as ispi.
     { apply @isprogram_eq.
       apply (isprogram_subst_lib abs oa2 vars rhs lib bs correct); auto.
       apply @isprogram_eq in isp.
       apply isprogram_ot_iff in isp; repnd; auto. }

     apply IHk in comp; auto; exrepnd.

     exists t'0; dands; auto.
     exists (S k0).
     allrw @compute_at_most_k_steps_eq_f.
     rw @compute_at_most_k_stepsf_S.
     rw @compute_step_eq_unfold; simpl; rw <- Heqc; auto.
Qed.

Lemma isprog_can_implies_isvalue {o} :
  forall c (bs : list (@BTerm o)),
    isprog (oterm (Can c) bs) -> isvalue (oterm (Can c) bs).
Proof.
  introv isp; constructor; simpl; auto.
  apply isprogram_eq; auto.
Qed.
Hint Resolve isprog_can_implies_isvalue : slow.

Lemma if_hasvalue_cbv {p} :
  forall lib t v u,
    isprog t
    -> isprog_vars [v] u
    -> hasvalue lib (mk_cbv t v u)
    -> {x : @NTerm p & computes_to_value lib t x # hasvalue lib (subst u v x)}.
Proof.
  unfold hasvalue, computes_to_value, reduces_to, reduces_in_atmost_k_steps.
  introv pt pu hv; exrepd.
  allrewrite @compute_at_most_k_steps_eq_f.
  revert t pt e.
  induction k; simpl; introv pt e; ginv; tcsp.

  - allapply @isvalue_ncan; sp.

  - destruct t as [x|op bs].

    { allapply @isprog_vterm; sp. }

    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      exists (oterm (Can c) bs); dands; eauto 3 with slow.

      * exists 0; simpl; eauto 3 with slow.

      * exists t'; sp.
        exists k; unfold subst; allrewrite @compute_at_most_k_steps_eq_f; sp.

    + Case "NCan".
      unfold mk_cbv, nobnd in e.
      rw @compute_step_ncan_ncan in e.
      remember (compute_step lib (oterm (NCan nc) bs)); symmetry in Heqc; destruct c;
      try (complete (inversion e)).

      allrewrite @fold_cbv.
      assert (isprog n) as in0 by (apply preserve_compute_step in Heqc; sp; allrw @isprogram_eq; sp).
      applydup IHk in in0; exrepd; auto.

      exists x; sp.

      exists (S k1).
      allrewrite @compute_at_most_k_steps_eq_f.
      rewrite compute_at_most_k_stepsf_S.
      rewrite Heqc; sp.

      exists t'0; sp.
      exists k0; sp.

    + Case "Exc".
      simpl in e.
      provefalse.
      allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst.
      fold_terms.
      allrw @fold_exception.
      rw <- @compute_at_most_k_steps_eq_f in e.
      generalize (reduces_to_exception lib (mk_exception a t) t');
        intro ee; repeat (autodimp ee hyp); sp; try (exists k; auto).
      subst.
      allapply @isvalue_exc; sp.

    + Case "Abs".
      unfold mk_cbv, nobnd in e.
      rw @compute_step_ncan_abs in e.
      unfold on_success in e; simpl in e.
      remember (compute_step_lib lib abs bs) as c; destruct c; try (complete (inversion e)).
      pose proof (compute_step_lib_success lib abs bs n) as h.
      autodimp h hyp; exrepnd; subst.
      allrw @fold_nobnd; allrw @fold_cbv.

      assert (isprog (mk_instance vars bs rhs)) as isp.
      { apply @isprogram_eq.
        apply (isprogram_subst_lib abs oa2 vars rhs lib bs correct); auto.
        apply @isprogram_eq in pt.
        apply isprogram_ot_iff in pt; repnd; auto. }

      apply IHk in e; auto; exrepnd.

      exists x; dands; auto.
      exists (S k1).
      allrw @compute_at_most_k_steps_eq_f.
      rw @compute_at_most_k_stepsf_S.
      rw @compute_step_eq_unfold; simpl; rw <- Heqc; auto.
      exists t'0; dands; auto.
      exists k0; auto.
Qed.

Lemma isvalue_mk_choice_seq {o} : forall n, @isvalue o (mk_choice_seq n).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isvalue_mk_choice_seq : slow.

Lemma if_hasvalue_apply {pp} :
  forall lib f a,
    isprog f
    -> isprog a
    -> hasvalue lib (mk_apply f a)
    -> {v : NVar
        & {b : @NTerm pp
        & computes_to_value lib f (mk_lam v b)
        # hasvalue lib (subst b v a)}}
       [+] {n : choice_sequence_name
            & computes_to_value lib f (mk_choice_seq n)
            # hasvalue lib (mk_eapply (mk_choice_seq n) a)}.
Proof.
  unfold hasvalue, computes_to_value, reduces_to.
  introv pf pa hv; exrepd.
  revert dependent f.
  induction k; simpl; introv isp comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allapply @isvalue_ncan; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    rw @compute_step_eq_unfold in comp1; allsimpl.
    destruct f as [v|op bs]; ginv.

    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      apply compute_step_apply_success in comp1.
      repndors; exrepnd; subst; fold_terms; ginv;[|].

      * left.
        exists v b; dands; try (complete (constructor; sp; allrw @fold_lam; sp; rw @isprogram_eq; sp)); eauto with slow.
        exists 0; sp; try (complete (constructor; sp; allrw @fold_lam; sp; rw @isprogram_eq; sp)).

      * right; exists n; dands; eauto 3 with slow;[|].
        { exists 0; allrw @reduces_in_atmost_k_steps_0; auto. }
        { eexists; dands;[eexists;exact comp0|]; auto. }

    + Case "NCan".
      remember (compute_step lib (oterm (NCan nc) bs)); symmetry in Heqc; destruct c; allsimpl; ginv.
      fold_terms.
      assert (isprog n) as in0 by (apply preserve_compute_step in Heqc; sp; allrw @isprogram_eq; sp).
      applydup IHk in comp0; auto; repndors;
        [left|right];
        exrepd; auto.

      * exists v b; sp.

        exists (S k1).

        { rw @reduces_in_atmost_k_steps_S; exists n; dands; auto. }

        { exists t'0; sp.
          exists k0; sp. }

      * exists n0; dands; eauto 3 with slow.
        { exists (S k1).
          allrw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }
        { eexists; dands;[eexists;exact r|]; auto. }

    + Case "Exc".
      ginv.
      provefalse.
      allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst.
      fold_terms.
      allrw @fold_exception.
      generalize (reduces_to_exception lib (mk_exception a0 t) t');
        intro ee; repeat (autodimp ee hyp); sp; try (exists k; auto).
      subst.
      allapply @isvalue_exc; sp.

    + Case "Abs".
      rw @compute_step_eq_unfold in comp1; allsimpl.
      remember (compute_step_lib lib abs bs) as c; destruct c; allsimpl; ginv.
      pose proof (compute_step_lib_success lib abs bs n) as h.
      autodimp h hyp; exrepnd; subst.
      allrw @fold_nobnd; allrw @fold_cbv.

      assert (isprog (mk_instance vars bs rhs)) as isp'.
      { apply @isprogram_eq.
        apply (isprogram_subst_lib abs oa2 vars rhs lib bs correct); auto.
        apply @isprogram_eq in isp.
        apply isprogram_ot_iff in isp; repnd; auto. }

      apply IHk in comp0; auto; repndors;
        [left|right]; exrepnd.

      * exists v b; dands; auto.
        { exists (S k1).
          rw @reduces_in_atmost_k_steps_S.
          rw @compute_step_eq_unfold; simpl.
          simpl; rw <- Heqc; auto.
          eexists; dands; eauto. }
        { exists t'0; dands; auto.
          exists k0; auto. }

      * exists n; dands; eauto 3 with slow.
        { exists (S k1).
          allrw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }
        { eexists; dands;[eexists;exact comp4|]; auto. }
Qed.

Lemma if_computes_to_value_apply {o} :
  forall lib (f a x : @NTerm o),
    isprog f
    -> isprog a
    -> computes_to_value lib (mk_apply f a) x
    -> {v : NVar
        & {b : NTerm
        & computes_to_value lib f (mk_lam v b)
        # computes_to_value lib (subst b v a) x}}
       [+] {n : choice_sequence_name
            & computes_to_value lib f (mk_choice_seq n)
            # computes_to_value lib (mk_eapply (mk_choice_seq n) a) x}.
Proof.
  unfold computes_to_value, reduces_to.
  introv pf pa hv; exrepd.
  revert dependent f.
  induction k; simpl; introv isp comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allapply @isvalue_ncan; sp.

  - destruct f as [|op bs].

    { allapply @isprog_vterm; sp. }

    allrw @reduces_in_atmost_k_steps_S; exrepnd.
    dopid op as [c|nc|exc|abs] Case.

    + Case "Can".
      csunf comp1; allsimpl.
      apply compute_step_apply_success in comp1;
        repndors; exrepnd; subst; fold_terms; ginv.

      * left.
        exists v b; sp; try (complete (constructor; sp; allrw @fold_lam; sp; rw @isprogram_eq; sp)).
        { exists 0; sp; try (complete (constructor; sp; allrw @fold_lam; sp; rw @isprogram_eq; sp)). }
        { exists k; allrewrite @compute_at_most_k_steps_eq_f; sp. }

      * right.
        exists n; dands; eauto 3 with slow.
        { exists 0; allrw @reduces_in_atmost_k_steps_0; auto. }

    + Case "NCan".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan nc) bs)); symmetry in Heqc; destruct c; allsimpl; ginv.
      fold_terms.
      assert (isprog n) as in0 by (apply preserve_compute_step in Heqc; sp; allrw @isprogram_eq; sp).
      applydup IHk in in0; auto; repndors;
        [left|right]; exrepd; auto.

      * exists v b; sp.

        { exists (S k1).
          rw @reduces_in_atmost_k_steps_S.
          exists n; dands; auto. }

        exists k0; sp.

      * exists n0; dands; eauto 3 with slow.
        { exists (S k1).
          allrw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      provefalse.
      allrw @isprog_eq; allapply @isprogram_exception_implies; exrepnd; subst.
      fold_terms.
      allrw @fold_exception.
      generalize (reduces_to_exception lib (mk_exception a0 t) x);
        intro ee; repeat (autodimp ee hyp); sp; try (exists k; auto).
      subst.
      allapply @isvalue_exc; sp.

    + Case "Abs".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_abs in comp1.
      remember (compute_step_lib lib abs bs) as c; destruct c; allsimpl; ginv.
      pose proof (compute_step_lib_success lib abs bs n) as h.
      autodimp h hyp; exrepnd; subst.
      allrw @fold_nobnd; allrw @fold_cbv.

      assert (isprog (mk_instance vars bs rhs)) as isp'.
      { apply @isprogram_eq.
        apply (isprogram_subst_lib abs oa2 vars rhs lib bs correct); auto.
        apply @isprogram_eq in isp.
        apply isprogram_ot_iff in isp; repnd; auto. }

      apply IHk in comp0; auto; repndors;
        [left|right]; exrepnd.

      * exists v b; dands; auto.
        { exists (S k1).
          rw @reduces_in_atmost_k_steps_S.
          exists (mk_instance vars bs rhs); dands; auto. }
        exists k0; auto.

      * exists n; dands; eauto 3 with slow.
        { exists (S k1).
          allrw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }
Qed.

Lemma compute_step_value_like {p} :
  forall lib (t : @NTerm p), isvalue_like t -> compute_step lib t = csuccess t.
Proof.
  introv h.
  dorn h.
  - apply iscan_implies in h; repndors; exrepnd; subst; reflexivity.
  - destruct t as [|op]; allsimpl; tcsp;
    try (complete (dorn h; allsimpl; sp)).
    destruct op; allsimpl; sp;
    try (complete (dorn h; allsimpl; sp)).
Qed.

Lemma reduces_in_atmost_k_steps_if_isvalue_like {o} :
  forall lib k (t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t1 t2 k
    -> isvalue_like t1
    -> t2 = t1.
Proof.
  induction k; introv r iv.
  - rw @reduces_in_atmost_k_steps_0 in r; auto.
  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    rw @compute_step_value_like in r1; auto; ginv.
    apply IHk in r0; auto; subst; auto.
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

Lemma isvalue_like_utoken {o} :
  forall a, @isvalue_like o (mk_utoken a).
Proof.
  introv; unfold isvalue_like; simpl; sp.
Qed.
Hint Resolve isvalue_like_utoken : slow.

Lemma implies_computes_to_value_apply {p} :
  forall lib f a v b x,
    computes_to_value lib f (@mk_lam p v b)
    -> computes_to_value lib (subst b v a) x
    -> computes_to_value lib (mk_apply f a) x.
Proof.
  unfold computes_to_value, reduces_to.
  introv cf cs; exrepnd; dands; auto.
  exists (S (k0 + k)).
  rw @reduces_in_atmost_k_steps_S.
  revert dependent f.
  revert dependent k0.

  induction k0; introv r1.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists (subst b v a); simpl; dands; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct f as [|op bs].

    + csunf r1; simpl in r1; ginv.

    + dopid op as [c|nc|exc|abs] Case.

      * Case "Can".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.
        inversion r0; subst; fold_terms; GC.
        exists (subst b v a); simpl; dands; auto.
        eapply no_change_after_value2; eauto; try omega.

      * Case "NCan".
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_apply u a); dands; tcsp.

        { unfold mk_apply, nobnd.
          rw @compute_step_ncan_ncan.
          rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.

      * Case "Exc".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.

      * Case "Abs".
        csunf r1; simpl in r1.
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_apply u a); dands; tcsp.

        { unfold mk_apply, nobnd; csunf; simpl; csunf; simpl.
          unfold on_success.
          rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.
Qed.

Lemma implies_computes_to_value_inl_decide {pp} :
  forall lib d x f y g a v,
    computes_to_value lib d (@mk_inl pp a)
    -> computes_to_value lib (subst f x a) v
    -> computes_to_value lib (mk_decide d x f y g) v.
Proof.
  unfold computes_to_value, reduces_to.
  introv cd cf; exrepnd; dands; auto.
  exists (S (k0 + k)).
  rw @reduces_in_atmost_k_steps_S.
  clear cd.
  revert dependent d.
  revert dependent k0.
  induction k0; introv r.

  - allrw @reduces_in_atmost_k_steps_0; subst; simpl.
    exists (subst f x a); sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct d as [|op bs].

    + csunf r1; simpl in r1; ginv.

    + dopid op as [c|nc|exc|abs] Case.

      * Case "Can".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.
        inversion r0; subst; fold_terms; GC.
        exists (subst f x a); simpl; dands; auto.
        eapply no_change_after_value2; eauto; try omega.

      * Case "NCan".
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_decide u x f y g); dands; tcsp.

        { unfold mk_decide, nobnd.
          rw @compute_step_ncan_ncan.
          rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.

      * Case "Exc".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.

      * Case "Abs".
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_decide u x f y g); dands; tcsp.

        { unfold mk_decide, nobnd.
          rw @compute_step_ncan_abs.
          csunf r1; simpl in r1; rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.
Qed.

Lemma implies_computes_to_value_inr_decide {pp} :
  forall lib d x f y g a v,
    computes_to_value lib d (@mk_inr pp a)
    -> computes_to_value lib (subst g y a) v
    -> computes_to_value lib (mk_decide d x f y g) v.
Proof.
  unfold computes_to_value, reduces_to.
  introv cd cf; exrepnd; dands; auto.
  exists (S (k0 + k)).
  rw @reduces_in_atmost_k_steps_S.
  clear cd.
  revert dependent d.
  revert dependent k0.
  induction k0; introv r1.

  - allrw @reduces_in_atmost_k_steps_0; subst; simpl.
    exists (subst g y a); sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct d as [|op bs].

    + csunf r1; simpl in r1; ginv.

    + dopid op as [c|nc|exc|abs] Case.

      * Case "Can".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.
        inversion r0; subst; fold_terms; GC.
        exists (subst g y a); simpl; dands; auto.
        eapply no_change_after_value2; eauto; try omega.

      * Case "NCan".
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_decide u x f y g); dands; tcsp.

        { unfold mk_decide, nobnd.
          rw @compute_step_ncan_ncan.
          rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.

      * Case "Exc".
        csunf r1; simpl in r1; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; ginv.

      * Case "Abs".
        pose proof (IHk0 u) as h; repeat (autodimp h hyp); exrepnd.
        exists (mk_decide u x f y g); dands; tcsp.

        { unfold mk_decide, nobnd.
          rw @compute_step_ncan_abs.
          csunf r1; simpl in r1; rw r1; auto. }

        simpl; rw @reduces_in_atmost_k_steps_S.
        exists u0; sp.
Qed.

Definition computes_to_pk {o} lib (t : @NTerm o) (pk : param_kind) :=
  computes_to_value lib t (pk2term pk).

Definition mk_compop_eq {p} (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp CompOpEq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Lemma reduces_in_atmost_k_steps_exception {o} :
  forall lib bs (t : @NTerm o) k,
    reduces_in_atmost_k_steps lib (oterm Exc bs) t k
    -> t = oterm Exc bs.
Proof.
  introv comp.
  unfold reduces_in_atmost_k_steps in comp.
  rw @compute_at_most_k_steps_exception in comp.
  ginv; auto.
Qed.

Lemma implies_computes_to_value_comp {p} :
  forall lib (a b c d : @NTerm p) pk1 pk2 v,
    computes_to_pk lib a pk1
    -> computes_to_pk lib b pk2
    -> computes_to_value lib (if param_kind_deq pk1 pk2 then c else d) v
    -> computes_to_value lib (mk_compop_eq a b c d) v.
Proof.
  unfold computes_to_pk, computes_to_value, reduces_to.
  introv comppk1 comppk2 comp; exrepnd; dands; auto.
  exists (S (k1 + k0 + k)).
  revert dependent a.
  induction k1; introv compk1.

  - allrw @reduces_in_atmost_k_steps_0; subst; allsimpl.
    revert dependent b.
    induction k0; introv compk2.

    + allrw @reduces_in_atmost_k_steps_0; subst; allsimpl.
      rw @reduces_in_atmost_k_steps_S.
      csunf; simpl.
      allrw @pk2term_eq.
      dcwf h; allsimpl;
      [|unfold co_wf in Heqh; allsimpl;allrw @get_param_from_cop_pk2can; complete ginv].
      unfold compute_step_comp; simpl.
      allrw @get_param_from_cop_pk2can.
      eexists; dands; eauto.

    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      applydup IHk0 in compk0; clear IHk0; allsimpl.
      csunf; simpl.
      allrw @pk2term_eq.
      destruct b as [x|op bs];[csunf compk1;allsimpl;ginv|].

      dopid op as [can|ncan|exc|abs] Case.

      * Case "Can".
        csunf compk1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in compk0; tcsp; ginv.
        dcwf h; allsimpl;
        [|unfold co_wf in Heqh; allsimpl;allrw @get_param_from_cop_pk2can; complete ginv].
        unfold compute_step_comp; simpl.
        allrw @get_param_from_cop_pk2can.
        eexists; dands; eauto.
        eapply no_change_after_value2; eauto; try omega.

      * Case "NCan".
        rw compk1; simpl.
        dcwf h; allsimpl;
        [|unfold co_wf in Heqh; allsimpl;allrw @get_param_from_cop_pk2can; complete ginv].
        eexists; dands; eauto.

      * Case "Exc".
        eexists; dands; eauto.
        csunf compk1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_exception in compk0; ginv.

      * Case "Abs".
        rw compk1; simpl.
        dcwf h; allsimpl;
        [|unfold co_wf in Heqh; allsimpl;allrw @get_param_from_cop_pk2can; complete ginv].
        eexists; dands; eauto.

  - rw @reduces_in_atmost_k_steps_S in compk1; exrepnd.
    applydup IHk1 in compk0; clear IHk1; allsimpl.
    destruct a as [x|op bs];[csunf compk1;allsimpl;ginv|].

    dopid op as [can|ncan|exc|abs] Case.

    + Case "Can".
      csunf compk1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in compk0; tcsp; ginv.
      rw @pk2term_eq in compk0; ginv.
      eapply no_change_after_value2; eauto; try omega.

    + Case "NCan".
      rw @reduces_in_atmost_k_steps_S.
      csunf; simpl.
      rw compk1; simpl.
      eexists; dands; eauto.

    + Case "Exc".
      csunf compk1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_exception in compk0; ginv.
      rw @pk2term_eq in compk0; ginv.

    + Case "Abs".
      rw @reduces_in_atmost_k_steps_S.
      csunf; simpl.
      rw compk1; simpl.
      eexists; dands; eauto.
Qed.

Lemma computes_to_value_implies_computes_to_pk {o} :
  forall lib (t : @NTerm o) pk,
    computes_to_value lib t (pk2term pk)
    -> computes_to_pk lib t pk.
Proof. sp. Qed.
Hint Resolve computes_to_value_implies_computes_to_pk : slow.

Lemma reduces_in_atmost_k_steps_implies_computes_to_value {o} :
  forall lib (t : @NTerm o) u k,
    reduces_in_atmost_k_steps lib t u k
    -> isvalue u
    -> computes_to_value lib t u.
Proof.
  introv r isv.
  unfold computes_to_value; dands; auto.
  exists k; auto.
Qed.
Hint Resolve reduces_in_atmost_k_steps_implies_computes_to_value : slow.

Lemma implies_computes_to_value_trycatch {p} :
  forall lib a (t : @NTerm p) v pk x b,
    computes_to_value lib t v
    -> computes_to_pk lib a pk
    -> computes_to_value lib (mk_try t a x b) v.
Proof.
  unfold computes_to_pk, computes_to_value, reduces_to.
  introv compt compa; exrepnd; dands; auto.
  revert dependent t.
  induction k0; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    dup compt as isv.
    apply isvalue_implies_iscan in isv.
    apply iscan_implies in isv; repndors; exrepnd; subst.

    + pose proof (implies_computes_to_value_comp
                    lib a a (oterm (Can c) bterms) mk_bot
                    pk pk (oterm (Can c) bterms)) as h.
      repeat (autodimp h hyp); eauto 3 with slow.
      { boolvar; tcsp; apply computes_to_value_isvalue_refl; tcsp. }
      unfold computes_to_value, reduces_to in h; exrepnd.

      exists (S k0).
      rw @reduces_in_atmost_k_steps_S.
      csunf; simpl; eexists; dands; eauto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [|op bs];[csunf comp1; allsimpl; complete ginv|].

    dopid op as [c|nc|exc|abs] Case; try (complete (allsimpl; auto)).

    + Case "Can".
      csunf comp1; simpl in comp1; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto with slow; ginv; subst.

      pose proof (implies_computes_to_value_comp
                    lib a a (oterm (Can c) bs) mk_bot
                    pk pk (oterm (Can c) bs)) as h.
      repeat (autodimp h hyp); eauto 3 with slow.
      { boolvar; tcsp; apply computes_to_value_isvalue_refl; tcsp. }
      unfold computes_to_value, reduces_to in h; exrepnd.

      exists (S k1).
      rw @reduces_in_atmost_k_steps_S.
      csunf; simpl; eexists; dands; eauto.

    + Case "NCan".
      apply IHk0 in comp0; clear IHk0; exrepnd.
      exists (S k1).
      rw @reduces_in_atmost_k_steps_S.
      rw @compute_step_try_ncan.
      rw comp1.
      eexists; dands; eauto.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto with slow; ginv; subst.
      allapply @isvalue_exc; sp.

    + Case "Abs".
      apply IHk0 in comp0; clear IHk0; exrepnd.
      exists (S k1).
      rw @reduces_in_atmost_k_steps_S.
      rw @compute_step_try_abs.
      csunf comp1; allsimpl; rw comp1.
      eexists; dands; eauto.
Qed.

Lemma can_doesnt_raise_an_exception {p} :
  forall lib a c bterms (e : @NTerm p),
    computes_to_exception lib a (oterm (Can c) bterms) e -> False.
Proof.
  introv ce.
  destruct ce as [k r].
  unfold reduces_to, reduces_in_atmost_k_steps in r; exrepnd.
  rw @compute_at_most_k_steps_eq_f in r.
  induction k; simpl in r; sp.
  inversion r; subst.
Qed.

Lemma not_bot_reduces_to_value {p} :
  forall lib t, @isvalue p t -> !reduces_to lib mk_bot t.
Proof.
  introv isv red.
  unfold reduces_to, reduces_in_atmost_k_steps in red; sp.
  rw @compute_at_most_k_steps_eq_f in e.
  revert t isv e.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct (zerop k); subst; ginv; allsimpl.

  - allapply @isvalue_ncan; sp.

  - destruct k; try (complete (inversion l)).
    simpl in e.
    destruct k; simpl in e; ginv;[allapply @isvalue_ncan; sp|].
    destruct k; simpl in e; ginv.

    + allunfold @apply_bterm; allsimpl.
      allunfold @lsubst; allsimpl.
      allapply @isvalue_ncan; sp.

    + destruct k; ginv; allsimpl;[allapply @isvalue_ncan; sp|].
      allunfold @apply_bterm; allsimpl.
      allunfold @lsubst; allsimpl.
      apply ind in e; sp.
Qed.

Lemma bottom_diverges {p} :
  forall lib t, !@computes_to_value p lib mk_bot t.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  apply not_bot_reduces_to_value in comp0; auto.
Qed.

Lemma not_hasvalue_bot {p} : forall lib, @hasvalue p lib mk_bot -> False.
Proof.
  introv Hsc; repnud Hsc; exrepnd.
  apply bottom_diverges in Hsc0; cpx.
Qed.

Lemma bottom_doesnt_converge {p} :
  forall lib a,
    @computes_to_value p lib mk_bottom a
    -> False.
Proof.
  introv comp.
  apply bottom_diverges in comp; sp.
Qed.

Lemma bottom_doesnt_raise_an_exception {p} :
  forall lib a (e : @NTerm p),
    computes_to_exception lib a mk_bottom e
    -> False.
Proof.
  introv Hcv.
  repnud Hcv.
  repnud Hcv.
  exrepnd.
  unfold reduces_in_atmost_k_steps in Hcv0.
  generalize dependent a.
  generalize dependent k.
  unfold_all_mk.
  induction k as [k  Hind] using comp_ind.
  introv Hc.
  destruct k.

  - inverts Hc.

  - rw @compute_at_most_k_steps_eq_f in Hc.
    rw @compute_at_most_k_stepsf_S in Hc.
    simpl in Hc.
    destruct k.

    + inversion Hc.

    + rw @compute_at_most_k_stepsf_S in Hc.
      simpl in Hc.
      unfold apply_bterm in Hc.
      simpl in Hc.
      revert Hc.
      change_to_lsubst_aux4; simpl; try (complete sp).
      intro Hc.
      rw <- @compute_at_most_k_steps_eq_f in Hc.
      apply Hind in Hc; sp.
Qed.

Lemma not_vbot_reduces_to_value {p} :
  forall lib v t, @isvalue p t -> !reduces_to lib (mk_vbot v) t.
Proof.
  introv isv red.
  unfold reduces_to, reduces_in_atmost_k_steps in red; sp.
  rw @compute_at_most_k_steps_eq_f in e.
  revert t isv e.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct (zerop k); subst; ginv; allsimpl.

  - allapply @isvalue_ncan; sp.

  - destruct k; try (complete (inversion l)).
    simpl in e.
    destruct k; allsimpl; ginv; allapply @isvalue_ncan; tcsp.
    destruct k; allsimpl; ginv.

    + allunfold @apply_bterm; allsimpl.
      allunfold @lsubst; allsimpl.
      boolvar; tcsp.
      allapply @isvalue_ncan; tcsp.

    + destruct k; allsimpl.

      * allunfold @apply_bterm; allsimpl.
        revert e; change_to_lsubst_aux4; simpl; auto; boolvar; simpl; intro e.
        ginv; allapply @isvalue_ncan; tcsp.

      * allunfold @apply_bterm; allsimpl.
        revert e; change_to_lsubst_aux4; simpl; auto; boolvar; simpl.
        unfold apply_bterm; simpl; change_to_lsubst_aux4; simpl; boolvar; intro e.
        apply ind in e; sp.
Qed.

Lemma vbot_diverges {p} :
  forall lib v t, !@computes_to_value p lib (mk_vbot v) t.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  apply not_vbot_reduces_to_value in comp0; auto.
Qed.

Lemma vbot_doesnt_raise_an_exception {p} :
  forall lib a v (e : @NTerm p),
    !computes_to_exception lib a (mk_vbot v) e.
Proof.
  introv Hcv.
  unfold computes_to_exception, reduces_to, reduces_in_atmost_k_steps in Hcv.
  exrepnd.
  generalize dependent e.
  induction k as [k Hind] using comp_ind.
  introv Hc.
  destruct k.

  - inverts Hc.

  - rw @compute_at_most_k_steps_eq_f in Hc.
    rw @compute_at_most_k_stepsf_S in Hc.
    simpl in Hc.
    destruct k.

    + inversion Hc.

    + rw @compute_at_most_k_stepsf_S in Hc.
      simpl in Hc.
      unfold apply_bterm in Hc.
      simpl in Hc.
      revert Hc.
      change_to_lsubst_aux4; simpl; try (complete sp); boolvar.
      intro Hc.
      rw <- @compute_at_most_k_steps_eq_f in Hc.
      apply Hind in Hc; sp.
Qed.

Lemma axiom_doesnt_raise_an_exception {p} :
  forall lib a (e : @NTerm p),
    computes_to_exception lib a mk_axiom e -> False.
Proof.
  introv c.
  apply can_doesnt_raise_an_exception in c; sp.
Qed.

Lemma apply_compute_step_prinargcan {p} :
  forall lib arg1c arg1lbt lbt tc,
    compute_step lib
        (oterm (NCan NApply)
        (bterm [] (oterm (Can arg1c) arg1lbt) :: lbt))
      = csuccess tc
      -> (arg1c = NLambda
          # {lamv : NVar
             & {lamb,applicand : @NTerm p
             $ arg1lbt = [bterm [lamv] lamb]
             # lbt = [bterm [] applicand]
             # tc = subst lamb lamv applicand }})
         [+] {n : choice_sequence_name
              & {arg : NTerm
              & arg1c = Ncseq n
              # arg1lbt = []
              # lbt = [bterm [] arg]
              # tc = mk_eapply (mk_choice_seq n) arg }}.
Proof.
  introv Hcomp.
  simpl in Hcomp.
  csunf Hcomp; allsimpl.
  apply compute_step_apply_success in Hcomp.
  repndors; auto.

  exrepnd; subst.
  left; dands; auto.
  eexists; eexists; eexists; eauto.
Qed.


Ltac destructbt bt:=
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  destruct bt as [btlv btnt].

Ltac destructbtdeep bt Hcomp :=
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  let btlv1 := fresh btlv "1" in
  let btlv2 := fresh btlv "2" in
  let btlv3 := fresh btlv "3" in
  destruct bt as [btlv btnt];
  destruct btlv as [| btlv1]; inverts Hcomp as Hcomp;
  try(destruct btlv as [| btlv2]; inverts Hcomp as Hcomp);
  try(destruct btlv as [| btlv3]; inverts Hcomp as Hcomp).


Lemma compute_step_lib_success_change_bs {o} :
  forall (lib : @library o) oa1 oa2 bs1 bs2 vars rhs correct,
    map num_bvars bs1 = map num_bvars bs2
    -> found_entry lib oa1 bs1 oa2 vars rhs correct
    -> compute_step_lib lib oa1 bs2 = csuccess (mk_instance vars bs2 rhs).
Proof.
  introv e f.
  unfold compute_step_lib.
  rw (unfold_abs_success_change_bs lib oa1 oa2 bs1 bs2 vars rhs correct e f); auto.
Qed.

Lemma eq_num_bvars_if_alpha {o} :
  forall bs1 bs2 : list (@BTerm o),
    length bs1 = length bs2
    -> (forall n : nat, n < length bs1 -> alpha_eq_bterm (bs1 {[n]}) (bs2 {[n]}))
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv l h; allsimpl; auto; cpx.
  apply eq_cons.
  - pose proof (h 0) as k; autodimp k hyp; try omega.
    unfold selectbt in k; simpl in k.
    inversion k; allsimpl.
    unfold num_bvars; simpl; auto.
  - apply IHbs1; auto.
    introv k.
    pose proof (h (S n)) as x.
    autodimp x hyp; omega.
Qed.

Lemma alpha_eq_lsubst_mk_abs_subst {o} :
  forall lib oa1 oa2 rhs vars correct (bs1 bs2 : list (@BTerm o)),
    found_entry lib oa1 bs1 oa2 vars rhs correct
    -> found_entry lib oa1 bs2 oa2 vars rhs correct
    -> map num_bvars bs1 = map num_bvars bs2
    -> (forall n : nat,
            n < length bs1
            -> alpha_eq_bterm (bs1 {[n]}) (bs2 {[n]}))
    -> alpha_eq (mk_instance vars bs1 rhs)
                (mk_instance vars bs2 rhs).
Proof.
  introv fe1 fe2 e hal.
  apply alphaeq_eq.
  apply mk_instance_alpha_congr; auto.

  - apply found_entry_implies_matching_entry in fe1.
    unfold matching_entry in fe1; repnd.
    apply map_eq_length_eq in fe1; auto.

  - apply found_entry_implies_matching_entry in fe2.
    unfold matching_entry in fe2; repnd.
    apply map_eq_length_eq in fe2; auto.

  - inversion correct; sp.

  - inversion correct; sp.

  - apply found_entry_implies_matching_entry in fe1.
    unfold matching_entry in fe1; repnd; auto.

  - apply found_entry_implies_matching_entry in fe2.
    unfold matching_entry in fe2; repnd; auto.

  - unfold bin_rel_bterm, binrel_list.
    applydup map_eq_length_eq in e; auto.
    introv.
    dands; auto.
    introv i; applydup hal in i.
    apply alphaeqbt_eq; auto.
Qed.

Lemma alpha_eq_mk_cbv {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_cbv t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_cbv t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alpha_eq_mk_fresh {o} :
  forall v (a : @NTerm o) u,
    alpha_eq (mk_fresh v a) u
    -> {v' : NVar
        & {a' : NTerm
        & u = mk_fresh v' a'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  fold_terms.
  exists x0 nt2; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alpha_eq_mk_ntry {o} :
  forall en (t : @NTerm o) v a u,
    alpha_eq (mk_try t en v a) u
    -> {en' : NTerm
        & {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_try t' en' v' a'
        # alpha_eq en en'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  repeat (destruct lbt2; allsimpl; repeat cpx).
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  fold_terms.
  exists nt0 nt2 x0 nt3; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alpha_eq_mk_var {o} :
  forall v (u : @NTerm o),
    alpha_eq (mk_var v) u
    -> u = mk_var v.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
Qed.

Lemma alpha_eq_mk_utoken {o} :
  forall a (u : @NTerm o),
    alpha_eq (mk_utoken a) u
    -> u = mk_utoken a.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
Qed.

Lemma alpha_eq_bterm_nobnd {o} :
  forall (t : @NTerm o) b,
    alpha_eq_bterm (nobnd t) b
    -> {u : NTerm & b = nobnd u # alpha_eq t u}.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; dands; eauto; reflexivity.
Qed.

Lemma alpha_eq_mk_compop {o} :
  forall c (t1 t2 t3 t4 u : @NTerm o),
    alpha_eq (mk_compop c t1 t2 t3 t4) u
    -> {t1' : NTerm
        & {t2' : NTerm
        & {t3' : NTerm
        & {t4' : NTerm
        & u = mk_compop c t1' t2' t3' t4'
        # alpha_eq t1 t1'
        # alpha_eq t2 t2'
        # alpha_eq t3 t3'
        # alpha_eq t4 t4'}}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl; cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  pose proof (i 3) as h4; autodimp h4 hyp; allsimpl.
  clear i.
  allunfold @selectbt; allsimpl.
  inversion h1; subst; allsimpl; cpx.
  inversion h2; subst; allsimpl; cpx.
  inversion h3; subst; allsimpl; cpx.
  inversion h4; subst; allsimpl; cpx.
  allrw @var_ren_nil_l.
  allrw @lsubst_nil.
  eexists; eexists; eexists; eexists; sp.
Qed.

Lemma alpha_eq_mk_arithop {o} :
  forall c (t1 t2 u : @NTerm o),
    alpha_eq (mk_arithop c t1 t2) u
    -> {t1' : NTerm
        & {t2' : NTerm
        & u = mk_arithop c t1' t2'
        # alpha_eq t1 t1'
        # alpha_eq t2 t2'}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl; cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  allunfold @selectbt; allsimpl.
  inversion h1; subst; allsimpl; cpx.
  inversion h2; subst; allsimpl; cpx.
  allrw @var_ren_nil_l.
  allrw @lsubst_nil.
  eexists; eexists; sp.
Qed.

Lemma alpha_eq_mk_cantest {o} :
  forall c (t1 t2 t3 u : @NTerm o),
    alpha_eq (mk_can_test c t1 t2 t3) u
    -> {t1' : NTerm
        & {t2' : NTerm
        & {t3' : NTerm
        & u = mk_can_test c t1' t2' t3'
        # alpha_eq t1 t1'
        # alpha_eq t2 t2'
        # alpha_eq t3 t3'}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl; cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  allunfold @selectbt; allsimpl.
  inversion h1; subst; allsimpl; cpx.
  inversion h2; subst; allsimpl; cpx.
  inversion h3; subst; allsimpl; cpx.
  allrw @var_ren_nil_l.
  allrw @lsubst_nil.
  eexists; eexists; eexists; sp.
Qed.

Lemma alpha_eq_bterm_vterm {o} :
  forall vs1 vs2 v (t : @NTerm o),
    alpha_eq_bterm (bterm vs1 (vterm v)) (bterm vs2 t)
    -> {v' : NVar & t = vterm v'}.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; allsimpl; subst; clear aeq.
  rw @lsubst_vterm in a.
  remember (sub_find (var_ren vs1 lv) v) as op.
  destruct op; allsimpl; symmetry in Heqop.
  - apply sub_find_varsub in Heqop; exrepnd; repnd; subst.
    inversion a as [x|]; subst.
    allapply @lsubst_is_vterm; auto.
  - inversion a as [x|]; subst.
    allapply @lsubst_is_vterm; auto.
Qed.

Lemma fold_subst_aux {o} :
  forall (t : @NTerm o) v u,
    lsubst_aux t [(v,u)] = subst_aux t v u.
Proof. sp. Qed.

Lemma alphaeq_preserves_isnoncan_like {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> isnoncan_like t1
    -> isnoncan_like t2.
Proof.
  introv aeq isn.
  allunfold @isnoncan_like; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    inversion aeq; subst; tcsp.
  - apply isabs_implies in isn; exrepnd; subst.
    inversion aeq; subst; tcsp.
Qed.

Lemma isnoncan_like_subst_aux_axiom_implies {o} :
  forall (t : @NTerm o) v,
    isnoncan_like (subst_aux t v mk_axiom)
    -> isnoncan_like t.
Proof.
  introv isn.
  destruct t; allsimpl; tcsp.
  unfold subst_aux in isn; allsimpl; boolvar; tcsp.
Qed.

Lemma isnoncan_like_subst_aux_utoken_implies {o} :
  forall (t : @NTerm o) v a,
    isnoncan_like (subst_aux t v (mk_utoken a))
    -> isnoncan_like t.
Proof.
  introv isn.
  destruct t; allsimpl; tcsp.
  unfold subst_aux in isn; allsimpl; boolvar; tcsp.
Qed.

Lemma null_flat_map :
  forall (A B : tuniv) (f : A -> list B) (l : list A),
    null (flat_map f l)
    <=> (forall a : A, LIn a l -> null (f a)).
Proof.
  induction l; allsimpl; split; introv k; tcsp.
  - rw null_app in k; repnd.
    introv i; repndors; subst; tcsp.
    rw IHl in k; apply k; auto.
  - rw null_app; dands; tcsp.
    apply IHl; introv i.
    apply k; tcsp.
Qed.

Lemma get_utokens_lsubst_aux_trivial1 {o} :
  forall (t : @NTerm o) sub,
    null (get_utokens_sub sub)
    -> get_utokens (lsubst_aux t sub) = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv e; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_some in Heqsf.
    rw null_flat_map in e.
    apply in_sub_eta in Heqsf; repnd.
    apply e in Heqsf; auto.
    rw null_iff_nil in Heqsf; auto.

  - Case "oterm".
    f_equal.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x as [l t]; allsimpl.
    apply (ind t l); auto.
    eapply null_subset;[|exact e].
    apply get_utokens_sub_filter_subset.
Qed.

Lemma get_utokens_subst_aux_trivial1 {o} :
  forall (t : @NTerm o) v u,
    null (get_utokens u)
    -> get_utokens (subst_aux t v u) = get_utokens t.
Proof.
  introv n.
  unfold subst_aux; apply get_utokens_lsubst_aux_trivial1; simpl.
  unfold get_utokens_sub; simpl; rw app_nil_r; auto.
Qed.

Fixpoint size_sub {o} (sub : @Sub o) :=
  match sub with
    | [] => 0
    | (v,t) :: s => (size t - 1) + size_sub s
  end.

Lemma not_in_bound_vars_if_alpha_eq_bterm {o} :
  forall (t1 t2 : @NTerm o) v1 v2,
    alpha_eq_bterm (bterm [v1] t1) (bterm [v2] t2)
    -> (!LIn v1 (free_vars t2) [+] v1 = v2).
Proof.
  introv a.
  destruct (deq_nvar v1 v2); subst; tcsp.
  left; intro k.
  apply alpha_eq_bterm_preserves_free_vars in a; allsimpl.
  assert (LIn v1 (remove_nvars [v2] (free_vars t2))) as i.
  { rw in_remove_nvars; simpl; tcsp. }
  rw <- a in i.
  rw in_remove_nvars in i; allsimpl; tcsp.
Qed.

Lemma atom_sub_compat_refl {o} :
  forall (t : @NTerm o) s vs1 vs2,
    atom_sub_compat t vs1 vs2 s s.
Proof.
  induction s; introv; tcsp.
Qed.
Hint Resolve atom_sub_compat_refl : slow.

Lemma ce_change_atom_sub_trivial {o} :
  forall lib : @compenv o,
    ce_change_atom_sub lib (ce_atom_sub lib) = lib.
Proof.
  introv.
  unfold ce_change_atom_sub, mk_ce; simpl.
  destruct lib; auto.
Qed.

(*
Lemma compute_step_ncan_utoken_success {o} :
  forall lib ncan a (bs : list (@BTerm o)) u,
    compute_step lib (oterm (NCan ncan) (nobnd (mk_utoken a) :: bs))
    = csuccess u
    -> (ncan = NFix
        # bs = []
        # u = mk_apply (mk_utoken a) (mk_fix (mk_utoken a)))
       [+]
       {x : NVar
        & {b : NTerm
        & ncan = NCbv
        # bs = [bterm [x] b]
        # u = subst b x (mk_utoken a)}}
       [+]
       {x : NVar
        & {b : NTerm
        & {en : exc_name
        & ncan = NTryCatch en
        # bs = [bterm [x] b]
        # u = mk_utoken a}}}
        [+]
        {t1 : NTerm
         & {bs1 : list BTerm
         & bs = nobnd t1 :: bs1
         # ncan = NCompOp CompOpAtomeq
        # (
            {t2 : NTerm
             & {t3 : NTerm
             & {a' : get_patom_set o
             & bs1 = [nobnd t2, nobnd t3]
             # (t1 = mk_utoken a'
                [+] {v : NVar
                     & t1 = vterm v
                     # find_atom (ce_atom_sub lib) v = Some a'})
             # ((a = a' # u = t2) [+] (a <> a' # u = t3))}}}
            [+]
            {x : NTerm
             & compute_step lib t1 = csuccess x
             # isnoncan_like t1
             # u = oterm (NCan ncan) (nobnd (mk_utoken a) :: nobnd x :: bs1) }
            [+]
            (isexc t1 # u = t1)
          )}}
       [+]
       {t1 : NTerm
        & {t2 : NTerm
        & {x : CanonicalTest
        & ncan = NCanTest x
        # bs = [nobnd t1, nobnd t2]
        # ((x = CanIsuatom # u = t1) [+] (x <> CanIsuatom # u = t2))}}}.
Proof.
  introv comp.
  allsimpl.
  dopid_noncan ncan Case;
    try (complete (allsimpl; ginv));
    try (complete (destruct bs; ginv)).

  - Case "NFix".
    allsimpl.
    apply compute_step_fix_success in comp; repnd; subst.
    left; auto.

  - Case "NCbv".
    allsimpl.
    apply compute_step_cbv_success in comp; exrepnd; subst.
    right; left.
    eexists; eexists; dands; eauto.

  - Case "NTryCatch".
    allsimpl.
    apply compute_step_try_success in comp; exrepnd; subst.
    right; right; left.
    eexists; eexists; eexists; auto.

  - Case "NCompOp".
    right; right; right; left.
    destruct bs; ginv; try (complete (allsimpl; boolvar; ginv)).
    destruct b as [l t].
    destruct l; ginv; try (complete (allsimpl; boolvar; ginv)).
    destruct t as [v1|op1 bs1]; try (complete (allsimpl; boolvar; ginv)).

    + allsimpl; boolvar; allsimpl; tcsp; GC; ginv.
      unfold compute_var in comp.
      dest_find_atom a' e'; allsimpl.
      unfold compute_step_comp in comp; allsimpl.
      destruct bs; ginv.
      destruct b as [l t].
      destruct l; ginv.
      destruct bs; ginv.
      destruct b as [l t2].
      destruct l; ginv.
      destruct bs; ginv.
      destruct c; ginv.
      exists (@vterm o v1) [nobnd t, nobnd t2]; dands; auto.
      left.
      exists t t2  a'; dands; boolvar; tcsp.
      right.
      exists v1; sp.

    + dopid op1 as [can1|ncan1|exc1|mrk1|abs1] SCase.

      * SCase "Can".
        allsimpl; boolvar; allsimpl; tcsp; GC; ginv.
        unfold compute_step_comp in comp.
        destruct bs1; allsimpl; ginv.
        destruct bs; allsimpl; ginv.
        destruct b as [l t1].
        destruct l; ginv.
        destruct bs; allsimpl; ginv.
        destruct b as [l t2].
        destruct l; ginv.
        destruct bs; allsimpl; ginv.
        destruct c; ginv.

        remember (get_str_from_cop can1) as g.
        symmetry in Heqg; destruct g; ginv.
        allapply @get_param_from_cop_pka; subst.

        exists (mk_utoken g) [nobnd t1, nobnd t2]; dands; auto.
        left.
        exists t1 t2 g; dands; boolvar; auto.

      * SCase "NCan".
        remember (compute_step lib (oterm (NCan ncan1) bs1)) as c1; ginv.
        destruct c1;
          try (complete (allsimpl; boolvar; allsimpl; tcsp; ginv;
                         rw <- Heqc1 in comp; allsimpl; ginv)).
        exists (oterm (NCan ncan1) bs1) bs; dands; auto.
        { simpl in comp; boolvar; ginv; destruct c; allsimpl; allsimpl; tcsp. }
        right; left.
        exists n; dands; auto.
        allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv; auto.

      * SCase "Exc".
        allsimpl; ginv; boolvar; allsimpl; tcsp; ginv.
        exists (oterm (Exc exc1) bs1) bs; dands; auto.
        { destruct c; allsimpl; allsimpl; tcsp. }

      * SCase "Mrk".
        allsimpl; ginv; boolvar; allsimpl; tcsp; ginv.

      * SCase "Abs".
        remember (compute_step lib (oterm (Abs abs1) bs1)) as c1; ginv.
        destruct c1; try (complete (allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv)).
        exists (oterm (Abs abs1) bs1) bs; dands; auto.
        { simpl in comp; boolvar; ginv; destruct c; allsimpl; allsimpl; tcsp. }
        right; left.
        exists n; dands; auto.
        allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv; auto.

  - Case "NArithOp".
    allsimpl; boolvar; allsimpl; tcsp; ginv.

  - Case "NCanTest".
    right; right; right; right.
    allsimpl.
    apply compute_step_can_test_success in comp; exrepnd; subst.
    exists arg2nt arg3nt c; dands; auto.
    destruct c; allsimpl; tcsp;
    try (complete (right; dands; auto; intro k; inversion k)).
Qed.
*)

Lemma free_vars_utok_sub_swap_utok_sub {o} :
  forall (vs1 vs2 : list NVar) (sub : @utok_sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_utok_sub (swap_utok_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (free_vars_utok_sub sub).
Proof.
  induction sub; introv norep disj; allsimpl; tcsp.
  destruct a; allsimpl.
  rw swapbvars_app; f_equal; tcsp.
  apply free_vars_swap; auto.
Qed.

Lemma free_vars_utok_sub_cswap_utok_sub {o} :
  forall (vs1 vs2 : list NVar) (sub : @utok_sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_utok_sub (cswap_utok_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (free_vars_utok_sub sub).
Proof.
  induction sub; introv norep disj; allsimpl; tcsp.
  destruct a; allsimpl.
  rw swapbvars_app; f_equal; tcsp.
  apply free_vars_cswap; auto.
Qed.

Lemma alpha_eq_same_cswap {o} :
  forall (t1 t2 : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> length vs1 = length vs2
    -> alpha_eq t1 t2
    -> alpha_eq (cswap (mk_swapping vs1 vs2) t1) (cswap (mk_swapping vs1 vs2) t2).
Proof.
  introv norep disj len aeq.
  allrw <- @alphaeq_eq.
  pose proof (alphaeq_add_cswap [] vs1 vs2 t1 t2) as h; allrw app_nil_r.
  repeat (autodimp h hyp); eauto with slow.
  - apply alphaeq_implies_alphaeq_vs; auto.
  - rw @alphaeq_exists; eexists; eauto.
Qed.

Lemma subst_utokens_swap_swap {o} :
  forall (t : @NTerm o) vs1 vs2 sub,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> length vs1 = length vs2
    -> alpha_eq
         (cswap (mk_swapping vs1 vs2) (subst_utokens t sub))
         (subst_utokens (cswap (mk_swapping vs1 vs2) t)
                        (cswap_utok_sub (mk_swapping vs1 vs2) sub)).
Proof.
  introv norep disj len.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0.
  rw @cswap_subst_utokens_aux.
  pose proof (unfold_subst_utokens
                (cswap_utok_sub (mk_swapping vs1 vs2) sub)
                (cswap (mk_swapping vs1 vs2) t)) as k; exrepnd.
  rw k0.

  apply alpha_eq_subst_utokens_aux; eauto with slow.
  - rw @bound_vars_cswap.
    rw @free_vars_utok_sub_cswap_utok_sub; auto.
    apply disjoint_swap; eauto with slow.
  - eapply alpha_eq_trans;[|exact k1].
    apply alpha_eq_same_cswap; eauto with slow.
Qed.

Lemma implies_alpha_eq_mk_atom_eq {o} :
  forall (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq c1 c2
    -> alpha_eq d1 d2
    -> alpha_eq (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv aeq1 aeq2 aeq3 aeq4.
  unfold mk_atom_eq, nobnd.
  prove_alpha_eq4.
  introv i.
  repeat (destruct n; cpx); apply alphaeqbt_nilv2; auto.
Qed.

Lemma cswap_alpha_congr {o} :
  forall l1 l2 vs (t1 t2 : @NTerm o),
    length vs = length l1
    -> no_repeats vs
    -> disjoint vs l1
    -> disjoint vs (allvars t1)
    -> disjoint vs l2
    -> disjoint vs (allvars t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq (cswap (mk_swapping l1 vs) t1) (cswap (mk_swapping l2 vs) t2).
Proof.
  introv len norep d1 d2 d3 d4 aeq.
  apply alphaeqbt_eq in aeq.
  rw @alphaeqbt_all in aeq.
  pose proof (aeq vs) as h; clear aeq.
  inversion h as [? ? ? ? ? len1 len2 disj1 norep1 a]; subst; clear h.
  allrw disjoint_app_r; repnd.
  apply (alphaeq_vs_implies_less _ _ _ []) in a; auto.
  apply alphaeq_eq in a.
  apply (alpha_eq_same_cswap _ _ vs0 vs) in a; auto; try omega.
  allrw @cswap_cswap.
  repeat (rw mk_swapping_app in a; auto).
  repeat (rw @cswap_disj_chain in a; auto; try omega;
          allrw disjoint_app_r; dands; eauto 3 with slow).
Qed.

Lemma alpha_eq_mk_apply {o} :
  forall (a b : @NTerm o) t,
    alpha_eq (mk_apply a b) t
    -> {a' : NTerm
        & {b' : NTerm
        & t = mk_apply a' b'
        # alpha_eq a a'
        # alpha_eq b b' }}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq.
  exrepnd; subst; allsimpl; cpx; allsimpl.
  pose proof (aeq0 (nobnd a) x) as h1; autodimp h1 hyp.
  pose proof (aeq0 (nobnd b) y) as h2; autodimp h2 hyp.
  clear aeq0.
  allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
  exists u0 u; dands; auto.
Qed.

Lemma alpha_eq_mk_eapply {o} :
  forall (a b : @NTerm o) t,
    alpha_eq (mk_eapply a b) t
    -> {a' : NTerm
        & {b' : NTerm
        & t = mk_eapply a' b'
        # alpha_eq a a'
        # alpha_eq b b' }}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq.
  exrepnd; subst; allsimpl; cpx; allsimpl.
  pose proof (aeq0 (nobnd a) x) as h1; autodimp h1 hyp.
  pose proof (aeq0 (nobnd b) y) as h2; autodimp h2 hyp.
  clear aeq0.
  allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
  exists u0 u; dands; auto.
Qed.

Lemma implies_alpha_eq_mk_apply {o} :
  forall f1 f2 a1 a2 : @NTerm o,
    alpha_eq f1 f2
    -> alpha_eq a1 a2
    -> alpha_eq (mk_apply f1 a1) (mk_apply f2 a2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_alpha_eq_mk_eapply {o} :
  forall f1 f2 a1 a2 : @NTerm o,
    alpha_eq f1 f2
    -> alpha_eq a1 a2
    -> alpha_eq (mk_eapply f1 a1) (mk_eapply f2 a2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_alpha_eq_mk_fix {o} :
  forall a1 a2 : @NTerm o,
    alpha_eq a1 a2
    -> alpha_eq (mk_fix a1) (mk_fix a2).
Proof.
  introv aeq.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma alpha_eq_mk_nat {o} :
  forall i (u : @NTerm o),
    alpha_eq (mk_nat i) u
    -> u = mk_nat i.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
Qed.

Lemma compute_step_eapply_iscan_isnoncan_like {o} :
  forall lib (x t : @NTerm o) bs,
    eapply_wf_def x
    -> isnoncan_like t
    -> compute_step lib (oterm (NCan NEApply) (nobnd x :: nobnd t :: bs))
       = match compute_step lib t with
           | csuccess u => csuccess (oterm (NCan NEApply) (nobnd x :: nobnd u :: bs))
           | cfailure m u => cfailure m u
         end.
Proof.
  introv ew isn.
  unfold isnoncan_like in isn.
  unfold eapply_wf_def in ew; repndors; exrepnd; subst;
    try (complete (apply isnoncan_implies in isn; exrepnd; subst;
                   csunf; simpl;
                   remember (compute_step lib (oterm (NCan c) bterms)) as comp;
                   destruct comp; simpl; auto));
    try (complete (apply isabs_implies in isn; exrepnd; subst;
                   csunf; simpl;
                   remember (compute_step lib (oterm (Abs abs) bterms)) as comp;
                   destruct comp; simpl; auto;
                   try (complete (unfold compute_step_eapply; dcwf h)))).
Qed.

Lemma compute_step_eapply_lam_iscan {o} :
  forall lib v (b t : @NTerm o) bs,
    iscan t
    -> compute_step lib (oterm (NCan NEApply) (nobnd (mk_lam v b) :: nobnd t :: bs))
       = match bs with
           | [] => csuccess (subst b v t)
           | _ => cfailure
                    bad_args
                    (oterm (NCan NEApply) (nobnd (mk_lam v b) :: nobnd t :: bs))
         end.
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst.
  - csunf; simpl.
    unfold compute_step_eapply2; simpl.
    unfold apply_bterm; simpl; allrw @fold_subst; auto.
Qed.

Lemma alpha_eq_mk_fix {o} :
  forall (t u : @NTerm o),
    alpha_eq (mk_fix t) u
    -> {x : NTerm & u = mk_fix x # alpha_eq t x}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl; cpx.
  pose proof (i 0) as h; autodimp h hyp; allsimpl.
  unfold selectbt in h; allsimpl.
  inversion h; subst; allsimpl; cpx.
  allrw @var_ren_nil_l.
  allrw @lsubst_nil.
  exists nt2; sp.
Qed.

Lemma get_utokens_step_seq_cswap {o} :
  forall s (t : @NTerm o),
    get_utokens_step_seq (cswap s t) = get_utokens_step_seq t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  apply app_if; auto;[].
  - rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma alphaeq_preserves_get_utokens_step_seq {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_utokens_step_seq t1 = get_utokens_step_seq t2.
Proof.
  nterm_ind1s t1 as [v1|op1 bs1 ind1] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply f_equal;[].

    { apply eq_flat_maps_diff; auto.
      introv i; applydup aeq0 in i.
      destruct t1 as [l1 t1].
      destruct t2 as [l2 t2].
      allsimpl.
      apply alphaeqbt_eq in i0.
      inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl; clear i0.
      applydup in_combine in i; repnd.
      pose proof (ind1 t1
                       (cswap (mk_swapping l1 vs) t1)
                       l1) as h;
        repeat (autodimp h hyp); allrw @osize_cswap; eauto 3 with slow.
      pose proof (h (cswap (mk_swapping l2 vs) t2)) as x; clear h.
      apply alphaeq_eq in a.
      autodimp x hyp.
      allrw @get_utokens_step_seq_cswap; auto. }
Qed.

Lemma compute_step_eapply_iscan_isexc {o} :
  forall lib (x t : @NTerm o) bs,
    eapply_wf_def x
    -> iscan x
    -> isexc t
    -> compute_step lib (oterm (NCan NEApply) (nobnd x :: nobnd t :: bs))
       = csuccess t.
Proof.
  introv ew isc ise.
  apply isexc_implies2 in ise.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  csunf; simpl; auto.
  unfold compute_step_eapply; dcwf h; auto.
Qed.

Definition get_utokens_step_seq_sub {o} (sub : @Sub o) :=
  flat_map get_utokens_step_seq (range sub).

Lemma get_utokens_step_seq_sub_filter_subset {o} :
  forall (sub : @Sub o) l,
    subset (get_utokens_step_seq_sub (sub_filter sub l)) (get_utokens_step_seq_sub sub).
Proof.
  unfold get_utokens_step_seq_sub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  apply range_sub_filter_subset in i1; auto.
Qed.

Definition onull {T} (o : OList T) := forall x, !in_olist x o.

Lemma get_cutokens_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    get_cutokens_sub ((v,t) :: sub)
    = oapp (get_cutokens t) (get_cutokens_sub sub).
Proof.
  introv.
  unfold get_cutokens_sub; allsimpl.
  rw @oeqset_oappl_cons; auto.
Qed.

Lemma onull_oapp {T} :
  forall (o1 o2 : OList T),
    onull (oapp o1 o2) <=> (onull o1 # onull o2).
Proof.
  introv.
  unfold onull; split; introv h; repnd; dands; introv i.
  - pose proof (h x) as q.
    allrw @in_olist_oapp; destruct q; sp.
  - pose proof (h x) as q.
    allrw @in_olist_oapp; destruct q; sp.
  - allrw @in_olist_oapp; repndors.
    + apply h0 in i; sp.
    + apply h in i; sp.
Qed.

Lemma onull_get_cutokens_sub_in {o} :
  forall (sub : @Sub o) v t,
    onull (get_cutokens_sub sub)
    -> LIn (v,t) sub
    -> onull (get_cutokens t).
Proof.
  induction sub; introv h1 h2; allsimpl; ginv; tcsp.
  destruct a; allsimpl.
  rw @get_cutokens_sub_cons in h1.
  apply onull_oapp in h1; repnd.
  repndors; tcsp; ginv; auto.
  eapply IHsub; eauto.
Qed.

Lemma subseto_get_utokens_step_seq_get_cutokens {o} :
  forall (t : @NTerm o),
    subseto (get_utokens_step_seq t) (get_cutokens t).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; simpl; eauto 3 with slow;[].
  Case "oterm".
  introv i.
  allrw in_app_iff; repndors.
  - apply in_olist_oappl_app; left.
    unfold oatomvs.
    apply in_olist_oappl.
    apply in_olist_OLL_map.
    eexists; dands; eauto.
    unfold oatomv; constructor.
  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    eapply ind in i0; eauto 3 with slow.
    apply in_olist_oappl_app; right.
    apply in_olist_oappl.
    apply in_olist_OLL_map.
    eexists; dands; eauto.
Qed.

Lemma onull_get_cutokens_implies_null_get_utokens_step_seq {o} :
  forall (t : @NTerm o),
    onull (get_cutokens t)
    -> null (get_utokens_step_seq t).
Proof.
  introv h i.
  apply subseto_get_utokens_step_seq_get_cutokens in i.
  apply h in i; sp.
Qed.

Lemma onull_OLS {T} :
  forall (f : nat -> OList T),
    onull (OLS f) <=> (forall n, onull (f n)).
Proof.
  introv.
  split; intro h; introv.
  - introv i.
    destruct (h x).
    constructor; eexists; eauto.
  - introv i.
    inversion i as [|?|? q]; exrepnd; subst.
    apply h in q0; sp.
Qed.

Definition is_ax_sub {o} (sub : @Sub o) :=
  forall v t, LIn (v,t) sub -> t = mk_axiom.

Lemma get_utokens_step_seq_lsubst_aux_trivial1 {o} :
  forall (t : @NTerm o) sub,
    is_ax_sub sub
    -> get_utokens_step_seq (lsubst_aux t sub) = get_utokens_step_seq t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv e; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_some in Heqsf.
    apply e in Heqsf; subst; simpl; auto.

  - Case "oterm".
    f_equal.
    rw flat_map_map; unfold compose.

    + apply eq_flat_maps; introv i; destruct x as [l t]; allsimpl.
      apply (ind t l); auto.
      introv j; allrw @in_sub_filter; repnd; apply e in j0; auto.
Qed.

Lemma get_utokens_step_seq_subst_aux_trivial1 {o} :
  forall (t : @NTerm o) v,
    get_utokens_step_seq (subst_aux t v mk_axiom) = get_utokens_step_seq t.
Proof.
  introv.
  unfold subst_aux.
  apply get_utokens_step_seq_lsubst_aux_trivial1; simpl.
  introv i; allsimpl; repndors; ginv; tcsp.
Qed.


(* end hide *)


Theorem compute_step_alpha {p} :
  forall lib t1 t2 t1',
    nt_wf t1
    -> alpha_eq t1 t2
    -> compute_step lib t1 = csuccess t1'
    -> { t2' : @NTerm p
        & compute_step lib t2 = csuccess t2'
        # alpha_eq t1' t2'}.
Proof.
  nterm_ind1s t1 as [v1|o1 lbt1 IHind] Case; introv wf Hal Hcomp;
  duplicate Hal as backup;
  [ subst;
    invertsn Hal;
    invertsn Hcomp
  | ].

  - Case "oterm".
    dopid o1 as [c1 | nc1 | exc1 | abs1] SCase.

    + SCase "Can".
      inverts Hcomp; auto; exists t2; split; auto;[]; inverts Hal; refl.

    + SCase "NCan".  (* destruct lbt and the bts inside enough
    times so that the structure re4quired
     for computation rules is visible. need to split
      on whether the opid of arg1(prin_arg) is canonical *)

      dlist lbt1 SSCase as [| arg1];
        [ dopid_noncan nc1 SSSCase;
          inverts Hcomp
        |
        ]; [].
      (*takes care of nilcase as no ncop takes 0 bterms*)

      * SSCase "conscase".
        destruct arg1 as [arg1vs arg1nt];
          dlist arg1vs SSSCase as [|arg1v1].

        { SSSCase "nilcase".
          destruct arg1nt as [v|arg1o arg1bts].

          { csunf Hcomp; allsimpl; ginv. }

          inverts Hal as Hlen Hal. simpl in Hal. lapply (Hal 0); [introv H1al| omega].
          destruct lbt2 as [| bt2 lbt2]; [inverts Hlen|]; [].
          unfold selectbt in H1al. simpl in H1al. apply alphaeqbt_nilv in H1al. exrepnd.
          simpl in H1al1. symmetry in H1al1.
          destruct H1al1.
          duplicate H1al0 as Halarg1.
          invertsna Halarg1 H1alarg. rename lbt3 into t2arg1bts.
          dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase.

          { SSSSCase "Can". GC.
            dopid_noncan nc1 SSSSSCase.

            (* arg1 (principle in all cases) is canonical. *)
            - SSSSSCase "NApply".

              allsimpl; cpx.
              apply @apply_compute_step_prinargcan in Hcomp.
              repndors; exrepnd; subst; allsimpl; cpx; allsimpl;[|].

              + (* some work required to get lbt2 to be of the right shape*)
                allunfold @selectbt. repeat(alphahypsd).
                csunf; simpl. eexists; split; eauto.
                GC. clear backup H1al0 IHind. unfold subst.
                apply al_bterm in H1alarg00bt0;sp.
                eapply lsubst_alpha_congr4; simpl; eauto.
                constructor; auto; apply alphaeq_eq; auto.

              + allunfold @selectbt.
                repeat alphahypsd.
                csunf; simpl.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.

            - SSSSSCase "NEApply".

              allsimpl; cpx; GC.
              csunf Hcomp; allsimpl.
              apply compute_step_eapply_success in Hcomp; exrepnd; subst; fold_terms; GC.
              allsimpl.
              destruct lbt2; allsimpl; cpx;[].
              repndors; exrepnd; subst; allsimpl; fold_terms.

              + apply compute_step_eapply2_success in Hcomp1; exrepnd; subst; allsimpl; cpx.
                repndors; exrepnd; subst; allsimpl; ginv;
                  try (complete (allunfold @mk_choice_seq; ginv;
                                 allsimpl; cpx; GC; fold_terms;
                                 pose proof (Hal 1) as q; autodimp q hyp;
                                 unfold selectbt in q; allsimpl;
                                 allapply @alpha_eq_bterm_nobnd; exrepnd; subst;
                                 allapply @alpha_eq_mk_nat; subst;
                                 csunf; allsimpl; dcwf h; allsimpl; boolvar; try omega;
                                 allrw Znat.Nat2Z.id; allrw;
                                 eexists; dands; eauto));[].

                allunfold @mk_lam; ginv; allsimpl; cpx; fold_terms.
                pose proof (H1alarg0 0) as aeq; autodimp aeq hyp.
                unfold selectbt in aeq; allsimpl.

                destruct x as [l t].
                applydup @alphaeqbt1v2 in aeq; exrepnd; subst; fold_terms.

                allrw disjoint_singleton_l.
                pose proof (Hal 1) as q; autodimp q hyp.
                unfold selectbt in q; allsimpl.
                allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
                applydup @alphaeq_preserves_iscan in q0; auto.
                rw @compute_step_eapply_lam_iscan; auto.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @fold_subst.
                eapply lsubst_alpha_congr4; simpl; eauto.
                constructor; auto; apply alphaeq_eq; auto.

              + pose proof (Hal 1) as q; autodimp q hyp; try omega.
                unfold selectbt in q; allsimpl.
                allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
                applydup @alphaeq_preserves_isexc in q0; auto.
                applydup @alpha_eq_ot_numvars in H1al0; auto.
                rw @compute_step_eapply_iscan_isexc; eauto 3 with slow.

              + pose proof (Hal 1) as q; autodimp q hyp; try omega.
                unfold selectbt in q; allsimpl.
                allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
                applydup @alphaeq_preserves_isnoncan_like in q0; auto.
                applydup @alpha_eq_ot_numvars in H1al0; auto.
                rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.

                allrw @nt_wf_eapply_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.
                allsimpl; cpx.

                pose proof (IHind b b []) as h;
                  repeat (autodimp h hyp); clear IHind; eauto 3 with slow.
                pose proof (h u x) as ih; clear h; repeat (autodimp ih hyp); exrepnd.
                rw ih1.
                eexists; dands; eauto.
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; subst; ginv; auto; try (apply alphaeqbt_nilv2; auto); tcsp.

                (*
            - SSSSSCase "NApseq".

              clear IHind.
              allsimpl; cpx.
              csunf Hcomp; allsimpl.
              apply compute_step_apseq_success in Hcomp; exrepnd; subst; allsimpl; cpx.
              allunfold @selectbt; allsimpl; fold_terms.
              csunf; simpl; boolvar; try omega.
              rw @Znat.Nat2Z.id.
              eexists; dands; eauto.*)

            - SSSSSCase "NFix".

              csunf Hcomp; csunf; allsimpl.
              invertsn Hcomp. simpl. allunfold @compute_step_fix.
              destruct lbt1; inverts Hcomp. allsimpl. destruct lbt2; inverts Hlen.
              eexists; split; eauto. simpl. unfold mk_apply, nobnd.
              prove_alpha_eq3.

            - SSSSSCase "NSpread".

              csunf Hcomp; csunf; allsimpl.
              try(
                  ( (destruct arg1c;inverts Hcomp as Hcomp;[])
                      ||
                      (destruct arg1c;inverts Hcomp as Hcomp;[|]));
                  destruct arg1bts as [|arg1b1t ?]; invertsn Hcomp;
                  try(destructbtdeep arg1b1t Hcomp);
                  try(destruct arg1bts as [|arg1b2t ?]; invertsn Hcomp);
                  try(destructbtdeep arg1b2t Hcomp);
                  try(destruct arg1bts; invertsn Hcomp);
                  destruct lbt1 as [| arg2]; invertsn Hcomp;
                  try(destructbtdeep arg2 Hcomp);
                  try(destruct lbt1 as [| arg3]; invertsn Hcomp);
                  try(destructbtdeep arg3 Hcomp);
                  try(destruct lbt1 as [| arg4]; invertsn Hcomp)).
              simphyps. repeat(alphahypsd). clear backup.
              simpl. eexists; split; eauto. GC.
              clear IHind H1al0 .
              apply al_bterm in Hal1bt0 ;sp;[].
              apply apply_bterm_alpha_congr;sp.
              split;[sp|simpl];[].
              introv Hlt. repeat (destruct n; try(omega));sp.

            - SSSSSCase "NDsup".

              csunf Hcomp; csunf; allsimpl.
              try(
                  ( (destruct arg1c;inverts Hcomp as Hcomp;[])
                      ||
                      (destruct arg1c;inverts Hcomp as Hcomp;[|]));
                  destruct arg1bts as [|arg1b1t ?]; invertsn Hcomp;
                  try(destructbtdeep arg1b1t Hcomp);
                  try(destruct arg1bts as [|arg1b2t ?]; invertsn Hcomp);
                  try(destructbtdeep arg1b2t Hcomp);
                  try(destruct arg1bts; invertsn Hcomp);
                  destruct lbt1 as [| arg2]; invertsn Hcomp;
                  try(destructbtdeep arg2 Hcomp);
                  try(destruct lbt1 as [| arg3]; invertsn Hcomp);
                  try(destructbtdeep arg3 Hcomp);
                  try(destruct lbt1 as [| arg4]; invertsn Hcomp)).
              simphyps. repeat(alphahypsd). clear backup.
              simpl. eexists; split; eauto. GC.
              clear IHind H1al0 .
              apply al_bterm in Hal1bt0 ;sp;[].
              apply apply_bterm_alpha_congr;sp.
              split;[sp|simpl];[].
              introv Hlt. repeat (destruct n; try(omega));sp.

            - SSSSSCase "NDecide".

              csunf Hcomp; csunf; allsimpl.
              apply compute_step_decide_success in Hcomp; exrepnd; subst; allsimpl; cpx.
              allsimpl; cpx; allsimpl.
              repeat(alphahypsd); GC; clear backup IHind H1al0.
              apply al_bterm in Hal1bt0; auto.
              apply al_bterm in Hal2bt0; auto.
              repndors; repnd; subst; allsimpl; eexists; dands; eauto.

              + apply (apply_bterm_alpha_congr _ _ [d] [nt2]) in Hal1bt0; allsimpl; tcsp.
                split;[sp|simpl];[].
                introv Hlt.
                repeat (destruct n; try(omega));sp.

              + apply (apply_bterm_alpha_congr _ _ [d] [nt2]) in Hal2bt0; allsimpl; tcsp.
                split;[sp|simpl];[].
                introv Hlt.
                repeat (destruct n; try(omega));sp.

            - SSSSSCase "NCbv".

              csunf Hcomp; csunf; allsimpl.
              destruct lbt1 as [| arg2]; invertsn Hcomp;
              try(destructbtdeep arg2 Hcomp);
              try(destruct lbt1 as [| arg3]; invertsn Hcomp);
              try(destructbtdeep arg3 Hcomp);
              try(destruct lbt1 as [| arg4]; invertsn Hcomp).
              allsimpl. repeat(alphahypsd).
              allsimpl. eexists; split; eauto.
              clear IHind backup.
              apply al_bterm in Hal1bt0;sp.
              apply apply_bterm_alpha_congr;sp.
              split;[sp|simpl];[].
              introv Hlt. repeat (destruct n; try(omega));sp.

            - SSSSSCase "NSleep".

              csunf Hcomp; csunf; allsimpl.
              allsimpl.
              apply compute_step_sleep_success in Hcomp; exrepnd; subst; allsimpl; cpx.
              destruct lbt2; allsimpl; cpx; GC.
              exists (@mk_axiom p); dands; auto.

            - SSSSSCase "NTUni".

              csunf Hcomp; csunf; allsimpl.
              allsimpl.
              apply compute_step_tuni_success in Hcomp; exrepnd; subst; allsimpl; cpx.
              destruct lbt2; allsimpl; cpx; GC.
              exists (@mk_uni p n); dands; auto.
              unfold compute_step_tuni; simpl.
              destruct (Z_le_gt_dec 0 (Z.of_nat n)); sp; try omega.
              rw Znat.Nat2Z.id; sp.

            - SSSSSCase "NMinus".

              csunf Hcomp; csunf; allsimpl.
              allsimpl.
              apply compute_step_minus_success in Hcomp; exrepnd; subst; allsimpl; cpx.
              destruct lbt2; allsimpl; cpx; GC.
              exists (@mk_integer p (- z)); dands; auto.

            - SSSSSCase "NFresh".
              csunf Hcomp; csunf; allsimpl.
              allsimpl; cpx; ginv.

            - SSSSSCase "NTryCatch".

              csunf Hcomp; csunf; allsimpl.
              apply compute_step_try_success in Hcomp; exrepnd; subst.
              allsimpl; repeat cpx.
              generalize (Hal 1); intro k1; autodimp k1 hyp.
              unfold selectbt in k1; simpl in k1.
              generalize (Hal 2); intro k2; autodimp k2 hyp.
              unfold selectbt in k2; simpl in k2.
              apply alphaeqbt_nilv in k1; exrepnd; subst.
              dup k2 as aeqbt.
              apply alphaeqbt_1v in k2; exrepnd; subst.
              exists (mk_atom_eq nt2 nt2 (oterm (Can arg1c) t2arg1bts) mk_bot); dands; auto.
              apply implies_alpha_eq_mk_atom_eq; eauto 2 with slow.

            - SSSSSCase "NParallel".

              csunf Hcomp; allsimpl.
              apply compute_step_parallel_success in Hcomp; subst; allsimpl.
              exists (@mk_axiom p); dands; auto.

            - SSSSSCase "NCompOp".

              (* the next 2 cases are different because they have 2 prinargs
      i.e. they make recursive calls if the second arg is non-can *)
              destruct lbt1 as [| arg2]; try (complete (csunf Hcomp; allsimpl; dcwf h));[].
              destruct arg2 as [lv2 nt2].
              destruct lv2; try (complete (csunf Hcomp; allsimpl; boolvar; dcwf h));[].
              destruct nt2 as [?| arg2o arg2bts]; try (complete (csunf Hcomp; allsimpl; dcwf h));[].

              allsimpl;[].
              destruct lbt2 as [| t2arg2]; invertsn Hlen;[].
              csunf Hcomp.
              simphyps. alphahypdfv Hal. repeat( alphahypsd).
              simphyps. subst. GC.

              duplicate Hal1bt0 as XXXX.
              invertsna Hal1bt0 Halarg2. rename lbt3 into t2arg2bts.
              boolvar; ginv.

              dopid arg2o as [arg2c| arg2nc | arg2exc | arg2abs] SSSSSSCase.

              + SSSSSSCase "Can".
                dcwf h.
                apply compute_step_compop_success_can_can in Hcomp; exrepnd; subst.
                csunf; allsimpl; tcsp.
                destruct lbt2; allsimpl; repeat cpx.
                boolvar; tcsp.

                repeat(alphahypsd).
                allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
                dcwf h; try (complete (apply co_wf_false_implies_not in Heqh0; tcsp)).

                repndors; exrepnd; subst;
                allrw @get_param_from_cop_some; subst; allsimpl;
                unfold compute_step_comp; simpl;
                allrw @get_param_from_cop_pk2can;
                boolvar; subst; eexists; eauto.

              + SSSSSSCase "NCan".
                dcwf h; allsimpl.
                remember (compute_step lib ((oterm (NCan arg2nc) arg2bts))) as rec.
                destruct rec as [csuccrec | cfail]; inverts Hcomp as Hcomp.
                symmetry in Heqrec.

                allrw @nt_wf_NCompOp; exrepnd; allunfold @nobnd; allsimpl; ginv.
                allsimpl; cpx.

                eapply IHind with (lv:=[]) in Heqrec; eauto 3 with slow; tcsp;[].
                exrepnd. subst.
                exists (oterm (NCan (NCompOp c))
                              (bterm [] (oterm (Can arg1c) t2arg1bts) :: bterm [] t2' :: x :: y ::[])).
                rw @compute_step_ncompop_ncan2.
                dcwf h.
                rewrite Heqrec1.
                split; [refl|].
                prove_alpha_eq2.

              + SSSSSSCase "Exc".
                dcwf h; ginv; subst; GC; allsimpl.
                csunf; simpl.
                dcwf h.
                boolvar; tcsp.
                exists (oterm Exc t2arg2bts); sp.

              + SSSSSSCase "Abs".
                csunf Hcomp; allsimpl.
                dcwf h.
                remember (compute_step_lib lib arg2abs arg2bts) as csl.
                destruct csl; allsimpl; ginv; subst; GC.

                pose proof (compute_step_lib_success lib arg2abs arg2bts n) as h.
                autodimp h hyp; exrepnd; subst.
                pose proof (eq_num_bvars_if_alpha arg2bts t2arg2bts) as e; repeat (autodimp e hyp).
                pose proof (found_entry_change_bs
                              arg2abs oa2 vars rhs
                              lib
                              arg2bts correct t2arg2bts h0 e) as fe.
                pose proof (compute_step_lib_success_change_bs
                              lib arg2abs oa2 arg2bts t2arg2bts
                              vars rhs correct e h0) as k.
                rw @compute_step_ncompop_abs2; boolvar; tcsp.
                dcwf h;[].
                exists (oterm (NCan (NCompOp c))
                              (bterm [] (oterm (Can arg1c) t2arg1bts)
                                     :: bterm [] (mk_instance vars t2arg2bts rhs)
                                     :: lbt2));
                  dands; [complete (simpl; boolvar; tcsp; unfold on_success; rw k; auto)|].
                apply al_oterm; simpl; auto.
                introv h.
                destruct n; unfold selectbt; simpl; cpx;[|destruct n].
                * apply alpha_eq_bterm_congr; auto.
                * apply alpha_eq_bterm_congr.
                  eapply alpha_eq_lsubst_mk_abs_subst; eauto.
                * pose proof (Hal (S (S n))) as x.
                  autodimp x hyp; omega.


            - SSSSSCase "NArithOp".

              destruct lbt1 as [| arg2]; try (complete (csunf Hcomp; allsimpl; dcwf h));[].
              destruct arg2 as [lv2 nt2].
              destruct lv2; destruct nt2 as [?|arg2o arg2bts];
              try (complete (csunf Hcomp; allsimpl; dcwf h));[].

              destruct lbt2 as [| t2arg2]; invertsn Hlen.
              csunf Hcomp.
              simphyps. alphahypdfv Hal. repeat( alphahypsd).
              dcwf h;[].
              simphyps. subst.  GC.

              duplicate Hal1bt0 as XXXX.
              invertsna Hal1bt0 Halarg2. rename lbt3 into t2arg2bts.
              boolvar; ginv.

              dopid arg2o as [arg2c | arg2nc | arg2exc | arg2abs] SSSSSSCase.

              + SSSSSSCase "Can".
                apply compute_step_arithop_success_can_can in Hcomp; exrepnd; subst.
                csunf; allsimpl; tcsp; cpx.
                dcwf h;[].
                boolvar; tcsp.

                repeat(alphahypsd).

                repndors; exrepnd; subst;
                allapply @get_param_from_cop_pki;
                subst; ginv; GC;
                unfold compute_step_arith; simpl; boolvar; eexists; eauto.

              + SSSSSSCase "NCan".
                remember (compute_step lib ((oterm (NCan arg2nc) arg2bts))) as rec.
                destruct rec as [csuccrec | cfail]; allsimpl; ginv.
                symmetry in Heqrec.

                allrw @nt_wf_NArithOp; exrepnd; allunfold @nobnd; ginv; allsimpl; cpx.

                eapply IHind with (lv:=[])  in Heqrec; eauto 3 with slow;[].
                exrepnd. subst.
                exists (oterm (NCan (NArithOp a))
                              (bterm [] (oterm (Can arg1c) t2arg1bts) :: bterm [] t2' :: [])).
                rw @compute_step_narithop_ncan2.
                dcwf h;[].
                rw Heqrec1; dands; auto.
                prove_alpha_eq3.

              + SSSSSSCase "Exc".
                ginv.
                csunf; simpl.
                dcwf h;[].
                boolvar; tcsp.
                exists (oterm Exc t2arg2bts); sp.

              + SSSSSSCase "Abs".
                csunf Hcomp; allsimpl.
                remember (compute_step_lib lib arg2abs arg2bts) as csl.
                destruct csl; allsimpl; ginv; subst; GC.

                pose proof (compute_step_lib_success lib arg2abs arg2bts n) as h.
                autodimp h hyp; exrepnd; subst.
                pose proof (eq_num_bvars_if_alpha arg2bts t2arg2bts) as e; repeat (autodimp e hyp).
                pose proof (found_entry_change_bs
                              arg2abs oa2 vars rhs lib
                              arg2bts correct t2arg2bts h0 e) as fe.
                pose proof (compute_step_lib_success_change_bs
                              lib arg2abs oa2 arg2bts t2arg2bts
                              vars rhs correct e h0) as k.
                rw @compute_step_narithop_abs2.
                dcwf h;[].
                exists (oterm (NCan (NArithOp a))
                              (bterm [] (oterm (Can arg1c) t2arg1bts)
                                     :: bterm [] (mk_instance vars t2arg2bts rhs)
                                     :: lbt2));
                  dands; [complete (simpl; boolvar; tcsp; unfold on_success; rw k; auto)|].
                apply al_oterm; simpl; auto.
                introv h.
                destruct n; unfold selectbt; simpl; cpx;[|destruct n].
                * apply alpha_eq_bterm_congr; auto.
                * apply alpha_eq_bterm_congr.
                  eapply alpha_eq_lsubst_mk_abs_subst; eauto.
                * pose proof (Hal (S (S n))) as x.
                  autodimp x hyp; omega.

            - SSSSSCase "NCanTest".

              csunf Hcomp; csunf; allsimpl.
              simpl in Hcomp. unfold compute_step_can_test in Hcomp.
              destruct lbt1 as [| arg2]; invertsn Hcomp;
              (destructbtdeep arg2 Hcomp);
              (destruct lbt1 as [| arg3]; invertsn Hcomp);
              (destructbtdeep arg3 Hcomp);
              (destruct lbt1 as [| arg4]; invertsn Hcomp).
              simphyps; repeat(alphahypsd).
              simpl. eexists; split; eauto.
              cases_if; auto.
          }

          { SSSSCase "NCan".

            (* computation now occurs in one of the subterms
 (principle arg); hence use the induction hyp*)

            rw @compute_step_ncan_ncan in Hcomp.
            remember (compute_step lib (oterm (NCan arg1nc) arg1bts)) as crt2s.
            symmetry in Heqcrt2s.
            destruct crt2s as [csucct2s | cfail]; ginv.

            rw @compute_step_ncan_ncan.
            apply nt_wf_oterm_iff in wf; repnd; allsimpl.
            pose proof (wf (bterm [] (oterm (NCan arg1nc) arg1bts))) as w1; autodimp w1 hyp.
            allrw @bt_wf_iff.
            eapply IHind with (lv:=[]) in Heqcrt2s; eauto 3 with slow; try(simpl; left; auto); exrepnd.
            exists ((oterm (NCan nc1) (bterm [] t2' :: lbt2))). rename Heqcrt2s1 into Hcomp.
            rename Heqcrt2s0 into H1alcarg.
            rw Hcomp. split; [refl|].
            constructor; auto.
            simpl. introv Hlt.
            apply_clear Hal in Hlt.
            clear Hcomp.
            allunfold @selectbt; allsimpl.
            destruct n; auto;[].
            apply alphaeqbt_nilv2; trivial.
          }

          { SSSSCase "Exc".

            csunf Hcomp; csunf; allsimpl; cpx.
            apply compute_step_catch_success in Hcomp;
              repdors; exrepnd; subst; cpx; allsimpl; auto;
              fold_terms; allrw @fold_exception; cpx.

            + destruct x.
              applydup @alpha_eq_ot_numvars in H1al0.
              simpl in H1al1; cpx; allunfold @num_bvars; allsimpl.
              fold_terms.
              allrw @fold_exception.
              applydup @alpha_eq_ot_numvars in backup.
              simpl in backup0; cpx.
              allunfold @num_bvars; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct x0; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct y; allsimpl; cpx.
              repeat (destruct l; allsimpl; cpx).
              destruct y0; allsimpl; cpx.
              repeat (destruct l; allsimpl; cpx).
              generalize (H1alarg0 0); intro k0; autodimp k0 hyp.
              unfold selectbt in k0; simpl in k0.
              generalize (H1alarg0 1); intro k1; autodimp k1 hyp.
              unfold selectbt in k1; simpl in k1.
              generalize (Hal 1); intro k2; autodimp k2 hyp.
              unfold selectbt in k2; simpl in k2.
              generalize (Hal 2); intro k3; autodimp k3 hyp.
              unfold selectbt in k3; simpl in k3.
              apply alphaeqbt_nilv2 in k0.
              apply alphaeqbt_nilv2 in k1.
              apply alphaeqbt_nilv2 in k2.
              exists (mk_atom_eq n n0 (subst n1 n2 n3) (mk_exception n0 n3)); dands; auto.
              apply implies_alpha_eq_mk_atom_eq; auto.
              generalize (apply_bterm_alpha_congr
                            (bterm [v] b) (bterm [n2] n1) [e] [n3]);
                intro k; repeat (autodimp k hyp).
              unfold bin_rel_nterm; apply binrel_list_cons; dands; auto.
              apply binrel_list_nil.

            + exists (oterm Exc t2arg1bts); dands; auto.
              unfold compute_step_catch; destruct nc1; sp; boolvar; subst; tcsp.
          }

          { SSSSCase "Abs".

            rw @compute_step_ncan_abs in Hcomp.
            rw @compute_step_ncan_abs; allsimpl.
            remember (compute_step_lib lib arg1abs arg1bts) as c; destruct c; allsimpl; ginv.

            pose proof (compute_step_lib_success lib arg1abs arg1bts n) as h.
            autodimp h hyp; exrepnd; subst.
            pose proof (eq_num_bvars_if_alpha arg1bts t2arg1bts) as e; repeat (autodimp e hyp).
            pose proof (found_entry_change_bs
                          arg1abs oa2 vars rhs lib
                          arg1bts correct t2arg1bts h0 e) as fe.
            pose proof (compute_step_lib_success_change_bs
                          lib arg1abs oa2 arg1bts t2arg1bts
                          vars rhs correct e h0) as k.
            rw k.
            exists (oterm (NCan nc1)
                          (bterm [] (mk_instance vars t2arg1bts rhs) :: lbt2));
              dands; auto.
            apply al_oterm; simpl; auto.
            introv h.
            destruct n; unfold selectbt; simpl; cpx.
            + apply alpha_eq_bterm_congr.
              eapply alpha_eq_lsubst_mk_abs_subst; eauto.
            + pose proof (Hal (S n)) as x.
              autodimp x hyp; omega.
          }
        }

        { (* fresh case *)
          csunf Hcomp; allsimpl.
          apply @compute_step_fresh_success in Hcomp; repnd; subst.
          repndors; exrepnd; subst; allsimpl;
          clear backup; apply alpha_eq_mk_fresh in Hal; exrepnd; subst.

          - exists (@mk_fresh p v' (mk_var v')).
            apply alphaeqbt_1v in Hal1; exrepnd; ginv.
            allrw disjoint_singleton_l; simphyps; allrw not_over_or; repnd.

            allrw @lsubst_vterm; simphyps; boolvar; simphyps;
            apply alpha_eq_mk_var in Hal0; symmetry in Hal0;
            applydup @lsubst_is_vterm in Hal0; exrepnd; subst;
            allrw @lsubst_vterm; simphyps; boolvar; simphyps; ginv; GC;
            allrw not_over_or; repnd; tcsp; GC; ginv;
            inversion Hal0; subst; tcsp.

            dands; auto.
            + csunf; simpl; boolvar; auto.
            + apply (implies_alpha_eq_mk_fresh_sub vn); simpl; tcsp.
              unfold lsubst; simpl; boolvar; auto.

          - exists (pushdown_fresh v' a').
            dands.
            + unfold isvalue_like in Hcomp0; repndors.
              * apply iscan_implies in Hcomp0; repndors; exrepnd; subst.
                { applydup @alpha_eq_bterm_oterm in Hal1; exrepnd; subst.
                  csunf; simpl; auto. }
              * apply isexc_implies2 in Hcomp0; exrepnd; subst.
                applydup @alpha_eq_bterm_oterm in Hal1; exrepnd; subst.
                csunf; simpl; auto.
            + apply implies_alpha_eq_pushdown_fresh; auto.

          - remember (get_fresh_atom lib arg1nt) as a.
            pose proof (IHind arg1nt (subst arg1nt arg1v1 (mk_utoken a)) [arg1v1]) as h.
            repeat (autodimp h hyp).
            { rw @simple_osize_subst; eauto 3 with slow. }

            pose proof (lsubst_alpha_congr4 [arg1v1] [v'] arg1nt a' [(arg1v1,mk_utoken a)] [(v',mk_utoken a)]) as aeq.
            repeat (autodimp aeq hyp); eauto with slow.
            pose proof (lsubst_alpha_congr4 [arg1v1] [v'] arg1nt a' [(arg1v1,mk_axiom)] [(v',mk_axiom)]) as aeq'.
            repeat (autodimp aeq' hyp); eauto with slow.

            apply nt_wf_oterm_iff in wf; repnd; allsimpl.
            pose proof (wf (bterm [arg1v1] arg1nt)) as w1; autodimp w1 hyp.
            allrw @bt_wf_iff.

            pose proof (h (subst a' v' (mk_utoken a)) x) as k; clear h.
            repeat (autodimp k hyp).
            { apply nt_wf_subst; eauto 3 with slow. }
            exrepnd.

            repeat (rw @cl_lsubst_lsubst_aux in aeq; eauto with slow).
            repeat (rw @cl_lsubst_lsubst_aux in aeq'; eauto with slow).
            simpl in aeq; allrw @fold_subst_aux.
            simpl in aeq'; allrw @fold_subst_aux.
            pose proof (implies_isnoncan_like_subst_aux arg1nt arg1v1 (mk_utoken a) Hcomp1) as k.
            pose proof (alphaeq_preserves_isnoncan_like (subst_aux arg1nt arg1v1 (mk_utoken a)) (subst_aux a' v' (mk_utoken a)) aeq k) as q.
            apply isnoncan_like_subst_aux_utoken_implies in q.
            rw @compute_step_fresh_if_isnoncan_like; auto.
            simpl; unfold on_success.

            applydup @alphaeq_preserves_utokens in aeq'.
            repeat (rw @get_utokens_subst_aux_trivial1 in aeq'0; simpl; auto).
            pose proof (eq_fresh_atom lib arg1nt a' aeq'0) as e; rw <- e; rw <- Heqa.

            rw k1; eexists; dands; eauto.
            unfold mk_fresh.
            prove_alpha_eq4; introv z; destruct n; tcsp.
            pose proof (ex_fresh_var (arg1v1
                                        :: v'
                                        :: allvars (subst_utokens x [(a, vterm arg1v1)])
                                        ++ allvars (subst_utokens t2' [(a, vterm v')])
                                        ++ allvars x
                                        ++ allvars t2'
                       ))
              as fv; exrepnd; allsimpl.
            allrw in_app_iff; allrw not_over_or; repnd.
            apply alphaeqbt_eq.
            apply (aeqbt _ [v]); allsimpl; auto.
            { rw disjoint_singleton_l; simpl; allrw in_app_iff; sp. }

            pose proof (subst_utokens_swap_swap x [arg1v1] [v] [(a,vterm arg1v1)]) as hh; allsimpl.
            repeat (autodimp hh hyp).
            { apply disjoint_singleton_l; simpl; sp. }
            pose proof (subst_utokens_swap_swap t2' [v'] [v] [(a,vterm v')]) as kk; allsimpl.
            repeat (autodimp kk hyp).
            { apply disjoint_singleton_l; simpl; sp. }

            apply alphaeq_eq.
            unfold oneswapvar in hh; unfold oneswapvar in kk.
            boolvar.
            eapply alpha_eq_trans;[exact hh|].
            eapply alpha_eq_trans ;[|apply alpha_eq_sym; apply kk].
            apply alpha_eq_subst_utokens; eauto with slow.

            assert (!LIn arg1v1 (free_vars x)) as ni1.
            { introv i.
              pose proof (compute_step_preserves
                            lib (subst arg1nt arg1v1 (mk_utoken a))
                            x) as hhh; repnd.
              repeat (autodimp hhh hyp); repnd.
              { apply nt_wf_subst; eauto 3 with slow. }
              rw subvars_prop in hhh0.
              apply hhh0 in i.
              rw @cl_subst_subst_aux in i; eauto with slow; unfold subst_aux in i.
              rw @free_vars_lsubst_aux_cl in i; eauto with slow.
              rw in_remove_nvars in i; simpl in i; sp. }

            applydup @alphaeqbt_preserves_wf in Hal1 as wa'.
            allrw @bt_wf_iff.
            applydup wa' in w1.

            assert (!LIn v' (free_vars t2')) as ni2.
            { introv i.
              pose proof (compute_step_preserves
                            lib (subst a' v' (mk_utoken a))
                            t2') as hhh; repnd.
              repeat (autodimp hhh hyp); repnd.
              { apply nt_wf_subst; eauto 3 with slow. }
              rw subvars_prop in hhh0.
              apply hhh0 in i.
              rw @cl_subst_subst_aux in i; eauto with slow; unfold subst_aux in i.
              rw @free_vars_lsubst_aux_cl in i; eauto with slow.
              rw in_remove_nvars in i; simpl in i; sp. }

            pose proof (alphaeq_cswap_disj_free_vars x [arg1v1] [v]) as hhh;
              allsimpl; repeat (autodimp hhh hyp);
              try (apply disjoint_singleton_r; simpl; tcsp).

            pose proof (alphaeq_cswap_disj_free_vars t2' [v'] [v]) as kkk;
              allsimpl; repeat (autodimp kkk hyp);
              try (apply disjoint_singleton_r; simpl; tcsp).

            allrw @alphaeq_eq.
            eapply alpha_eq_trans;[exact hhh|].
            eapply alpha_eq_trans;[exact k0|]; eauto with slow.
        }

    + SCase "Exc".
      csunf Hcomp; allsimpl; ginv.
      apply alpha_eq_oterm_implies_combine in Hal; exrepnd; subst.
      csunf; simpl.
      eexists; dands; eauto.

    + SCase "Abs".
      csunf Hcomp; allsimpl.
      pose proof (compute_step_lib_success lib abs1 lbt1 t1' Hcomp) as h; exrepnd; subst.
      clear IHind backup Hcomp.

      inversion Hal as [|? ? ? len aeq]; subst.

      pose proof (eq_num_bvars_if_alpha lbt1 lbt2) as e; repeat (autodimp e hyp).
      pose proof (found_entry_change_bs abs1 oa2 vars rhs lib lbt1 correct lbt2 h0 e) as fe.
      pose proof (compute_step_lib_success_change_bs
                    lib abs1 oa2 lbt1 lbt2 vars rhs correct e h0) as k.

      exists (mk_instance vars lbt2 rhs); dands; auto.
      eapply alpha_eq_lsubst_mk_abs_subst; eauto.
Qed.

(*
Theorem compute_step_alpha_exception :
  forall t1 t2 t1' : NTerm,
    alpha_eq t1 t2
    -> compute_step t1 = cexception t1'
   -> { t2':NTerm & compute_step t2 = cexception t2'
        # alpha_eq t1' t2'}.
Proof.
  introv aeq e.
  apply compute_step_alpha_aux with (t1 := t1); auto.
Qed.
*)

(* begin hide *)


Lemma compute_at_most_steps_var {p} :
  forall lib n v,
    compute_at_most_k_steps lib (S n) (vterm v)
    = cfailure compute_step_error_not_closed (@vterm p v) .
Proof.
  induction n; allsimpl; cpx.
  intro. rewrite IHn. refl.
Qed.

Lemma compute_in_k_steps_var {p} :
  forall lib n v,
    computes_k_steps lib (S n) (vterm v)
    = cfailure compute_step_error_not_closed (@vterm p v) .
Proof.
  introv.
  rw @computes_k_steps_eq_f; simpl; sp.
Qed.

Lemma compute_1_step_success_implies_compute_step {p} :
 forall lib (t1 t2 : @NTerm p),
  compute_1_step lib t1 = csuccess t2
  -> compute_step lib t1 = csuccess t2.
Proof.
  introv k.
  unfold compute_1_step in k.
  destruct t1; ginv.
  destruct o; auto; inversion k.
Qed.

Lemma compute_step_ncan_implies_compute_1_step {p} :
 forall lib nc bts res,
  compute_step lib (oterm (@NCan p nc) bts) = res
  -> compute_1_step lib (oterm (NCan nc) bts) = res.
Proof. sp. Qed.

(*
Lemma compute_step_exception_implies_compute_1_step :
 forall t e,
  compute_step t = csuccess (mk_exception e)
  -> compute_1_step t = csuccess (mk_exception e).
Proof.
  introv c.
  unfold compute_1_step.
  destruct t; auto.
  destruct o; auto.
  unfold compute_step in c; inversion c.
Qed.
*)

Lemma compute_step_exact_implies_atmost {p} :
 forall lib n (t1 t2 : @NTerm p),
  computes_k_steps lib n t1 = csuccess t2
  -> compute_at_most_k_steps lib n t1 = csuccess t2.
Proof.
  induction n; introv c; allsimpl; auto.
  remember (computes_k_steps lib n t1) as ck.
  symmetry in Heqck; destruct ck; try (complete (inversion c)).

  apply IHn in Heqck.
  rw Heqck.
  apply compute_1_step_success_implies_compute_step in c; auto.
Qed.

Lemma compute_step_atmost_exact {p} :
 forall lib n (t1 t2 : @NTerm p),
  compute_at_most_k_steps lib n t1 = csuccess t2
  -> { m : nat & m <=n # computes_k_steps lib m t1 = csuccess t2  }.
Proof.
  induction n; introns Hc; sp;
  allsimpl;[ exists 0; cpx|];[].
  destructr (compute_at_most_k_steps lib n t1) as [ss|nn];
    [| inverts Hc]; [].
  symmetry in HeqHdeq. applydup IHn in HeqHdeq.
  exrepnd.
  destruct ss;[inverts Hc|];[].
  dopid o as [c|nc|exc|abs] Case.
  - Case "Can".
    csunf Hc; allsimpl; ginv.
    exists m. allsimpl. split; spc.
  - Case "NCan".
    exists (S m).
    split; spc; [omega|]. simpl.
    rw HeqHdeq1.
    apply compute_step_exact_implies_atmost in HeqHdeq1; auto.
  - Case "Exc".
    rw @compute_step_exception in Hc; sp; ginv.
    exists m; sp.
  - Case "Abs".
    simpl in Hc.
    exists (S m); dands; [omega|]; simpl.
    rw HeqHdeq1; simpl; auto.
Qed.

(*
Lemma compute_step_atmost_exception_exact :
 forall n t1 t2,
  computes_to_exception_in_max_k_steps t1 t2 n
  -> { m : nat & m <=n # computes_k_steps m t1 = cexception t2  }.
Proof.
  induction n; introns Hc; sp;
  allsimpl;[ exists 0; cpx|];[].
  destructr (compute_at_most_k_steps n t1) as [ss|nn|ee];
    [| inverts Hc | inverts Hc].

  - symmetry in HeqHdeq.
    apply compute_step_atmost_exact in HeqHdeq; exrepnd.
    exists (S m); dands; try omega.
    rw computes_k_steps_S.
    rw HeqHdeq0; auto.
    apply compute_step_exception_implies_compute_1_step in Hc; auto.

  - symmetry in HeqHdeq.
    apply IHn in HeqHdeq; exrepnd.
    exists m; auto.
Qed.
*)

Lemma compute_1_step_mk_try {p} :
  forall lib a (t : @NTerm p) x b,
    compute_1_step lib (mk_try t a x b)
    = compute_step lib (mk_try t a x b).
Proof. sp. Qed.

Lemma implies_reduces_to_trycatch {p} :
  forall lib a a' (t : @NTerm p) e x b,
    computes_to_exception lib a t e
    -> reduces_to lib (mk_try t a' x b) (mk_atom_eq a' a (subst b x e) (mk_exception a e)).
Proof.
  unfold computes_to_exception, reduces_to.
  introv comp; exrepnd.
  revert dependent t; induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists 1.
    rw @reduces_in_atmost_k_steps_S.
    csunf; simpl; boolvar; tcsp; GC.
    eexists; dands; eauto.
    rw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply IHk in comp0; exrepnd.

    destruct t as [v|op bs].

    { csunf comp1; allsimpl; ginv. }

    dopid op as [can|ncan|exc|abs] Case.

    + Case "Can".
      csunf comp1; allsimpl; ginv.
      eexists; eauto.

    + Case "NCan".
      exists (S k0).
      rw @reduces_in_atmost_k_steps_S.
      unfold mk_try, nobnd.
      rw @compute_step_ncan_ncan; rw comp1.
      eexists; dands; eauto.

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      eexists; eauto.

    + Case "Abs".
      exists (S k0).
      rw @reduces_in_atmost_k_steps_S.
      unfold mk_try, nobnd.
      csunf comp1; allsimpl.
      rw @compute_step_ncan_abs; rw comp1.
      eexists; dands; eauto.
Qed.

Lemma compute_at_most_k_steps_preserves_wf {o} :
  forall lib k (t1 t2 : @NTerm o),
    compute_at_most_k_steps lib k t1 = csuccess t2
    -> nt_wf t1
    -> nt_wf t2.
Proof.
  induction k; introv comp wf.
  - allsimpl; ginv; auto.
  - allsimpl.
    remember (compute_at_most_k_steps lib k t1) as c;
      destruct c; allsimpl; ginv; symmetry in Heqc.
    apply IHk in Heqc; auto.
    apply preserve_nt_wf_compute_step in comp; auto.
Qed.

Theorem reduces_in_atmost_k_steps_alpha {p} :
  forall lib (t1 t2 : NTerm),
    nt_wf t1
    -> alpha_eq t1 t2
    -> forall k t1',
        reduces_in_atmost_k_steps lib t1 t1' k
        -> { t2':@NTerm p & reduces_in_atmost_k_steps lib t2 t2' k
              # alpha_eq t1' t2'}.
Proof.
  introv wf Hal.
  induction k as [| k Hind]; introv Hc0;
  allunfold @reduces_in_atmost_k_steps;
  [allsimpl; invertsn Hc0; eexists; eauto; fail |].
  allsimpl.
  remember (compute_at_most_k_steps lib k t1) as ck.
  destruct ck as [csk|?]; invertsn Hc0.
  dimp (Hind csk);exrepnd; sp;[].
  clear Hind.
  rw hyp1.
  eapply compute_step_alpha in Hc0; eauto.
  eapply compute_at_most_k_steps_preserves_wf; eauto.
Qed.

Lemma alpha_eq_exception {p} :
  forall a (e t : @NTerm p),
    alpha_eq (mk_exception a e) t
    -> {a' : NTerm
        & {e' : NTerm
        & t = mk_exception a' e'
        # alpha_eq a a'
        # alpha_eq e e'}}.
Proof.
  introv Hal.
  inversion Hal as [|? ? ? len bts]; subst; allsimpl; cpx.
  generalize (bts 0); intro al1; autodimp al1 hyp.
  generalize (bts 1); intro al2; autodimp al2 hyp.
  clear bts.
  allunfold @selectbt; allsimpl.
  allapply @alphaeqbt_nilv; exrepnd; subst.
  allrw @fold_exception.
  exists nt0 nt2; sp.
Qed.

Lemma reduces_in_atmost_k_Steps_preserves_wf {o} :
  forall lib k (t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t1 t2 k
    -> nt_wf t1
    -> nt_wf t2.
Proof.
  introv r w.
  apply compute_at_most_k_steps_preserves_wf in r; auto.
Qed.

Theorem exception_in_atmost_k_steps_alpha {p} :
  forall lib a (t1 t2 : @NTerm p),
    nt_wf t1
    -> alpha_eq t1 t2
    -> forall k t1',
        computes_to_exception_in_max_k_steps lib a t1 t1' k
        -> {a' : NTerm
            & {t2' : NTerm
            & computes_to_exception_in_max_k_steps lib a' t2 t2' k
            # alpha_eq a a'
            # alpha_eq t1' t2'}}.
Proof.
  introv wf Hal.
  induction k as [| k Hind]; introv Hc0;
  allunfold @computes_to_exception_in_max_k_steps;
  allunfold @reduces_in_atmost_k_steps; allsimpl.

  - ginv.
    apply alpha_eq_exception in Hal; exrepnd; subst.
    exists a' e'; sp.

  - remember (compute_at_most_k_steps lib k t1) as ck.
    destruct ck; ginv.

    clear Hind.
    symmetry in Heqck.
    applydup @reduces_in_atmost_k_Steps_preserves_wf in Heqck; auto.
    apply @reduces_in_atmost_k_steps_alpha with (t2 := t2) in Heqck; auto.
    exrepnd.
    rw Heqck2.
    eapply compute_step_alpha in Hc0; eauto; exrepnd.
    apply alpha_eq_exception in Hc1; exrepnd; subst.
    exists a' e'; sp.
Qed.


(*
(* every step is alpha equal*)
Theorem reduces_in_k_steps_alpha :
  forall (t1 t2 :NTerm),
    alpha_eq t1 t2
    -> forall k t1',
        reduces_in_k_steps t1 t1' k
        -> { t2':NTerm & reduces_in_k_steps t2 t2' k
              # alpha_eq t1' t2'}.
destruct t1 as [v1 | o1 lbt1] ; invertsna Hc0 Hcc; sp.
  - exists t1'. split; auto.
  - remember (compute_at_most_k_steps k (oterm o1 lbt1)) as ck;
      destruct ck  as [oc1 |?]; [| inverts Hc0];[].
    symmetry in Heqck.
    pose proof (Hind oc1 Heqck) as XXX.
    exrepnd. rewrite XXX1.
    eapply compute_step_alpha in Hc0; eauto.
Qed. *)








Lemma reduces_to_alpha {o} :
  forall lib (t1 t2 t1' : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> reduces_to lib t1 t1'
    -> {t2' : NTerm
        & reduces_to lib t2 t2'
        # alpha_eq t1' t2'}.
Proof.
  introv wf aeq r.
  allunfold @reduces_to; exrepnd.
  eapply reduces_in_atmost_k_steps_alpha in r0; eauto; exrepnd.
  exists t2'; dands; auto.
  exists k; auto.
Qed.

Theorem compute_to_value_alpha {p} :
  forall lib (t1 t2 t1' : NTerm),
    nt_wf t1
    -> alpha_eq t1 t2
    -> computes_to_value lib t1 t1'
    -> {t2':@NTerm p
        & computes_to_value lib t2 t2'
        # alpha_eq t1' t2'}.
Proof.
  introns Xc.
  unfold computes_to_value in Xc1; repnd.
  eapply reduces_to_alpha in Xc2; eauto.
  exrepnd.
  exists t2'; dands; auto.
  unfold computes_to_value; dands; auto.
  apply alpha_preserves_value in Xc3; auto.
Qed.

Theorem compute_to_exception_alpha {p} :
  forall lib a (t1 t2 t1' : @NTerm p),
    nt_wf t1
    -> alpha_eq t1 t2
    -> computes_to_exception lib a t1 t1'
    -> {a' : NTerm
        & {t2': NTerm
        & computes_to_exception lib a' t2 t2'
        # alpha_eq a a'
        # alpha_eq t1' t2'}}.
Proof.
  introv wf; introns Xc.
  unfold computes_to_exception in Xc0.
  eapply reduces_to_alpha in Xc; eauto.
  exrepnd.
  apply alpha_eq_exception in Xc1; exrepnd; subst.
  exists a' e'; dands; auto.
Qed.

Lemma compute_split {p} :
  forall lib n m (t1 t2 t3 : @NTerm p),
    compute_at_most_k_steps lib n t1 = csuccess t2
    -> compute_at_most_k_steps lib m t1 = csuccess t3
    -> n<=m
    -> compute_at_most_k_steps lib (m-n) t2 = csuccess t3.
Proof.
  induction n as [| n Hind]; introv H1c H2c Hlt.
  - allsimpl. inverts H1c. assert (m-0=m) as Heq by omega. rw Heq;sp.
  - simpl in H1c. remember (compute_at_most_k_steps lib n t1) as cn.
    destruct cn; invertsn H1c. symmetry in Heqcn.
    eapply Hind in H2c; eauto;sp;[| omega].
    assert (S (m - S n) = (m-n)) as XX by omega.
    rw <- XX in H2c. rw  @compute_at_most_k_steps_eq_f in H2c.
    simpl in H2c. rw H1c in H2c. rw  <- @compute_at_most_k_steps_eq_f in H2c.
    sp.
Qed.


Hint Resolve preserve_compute_step is_program_ot_subst1: slow.



Lemma computes_to_val_like_in_max_k_steps_can {p} :
  forall lib c bterms a k,
    @computes_to_val_like_in_max_k_steps p lib (oterm (Can c) bterms) a k
    -> a = oterm (Can c) bterms.
Proof.
  introv comp.
  unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_can in comp0.
  inversion comp0; subst; sp.
Qed.

Lemma computes_to_val_like_in_max_k_steps_exc {p} :
  forall lib bterms (t : @NTerm p) k,
    computes_to_val_like_in_max_k_steps lib (oterm Exc bterms) t k
    -> t = oterm Exc bterms.
Proof.
  introv comp.
  unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_exception in comp0.
  inversion comp0; subst; sp.
Qed.

(*
Lemma compute_at_most_k_stepsf_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs,
    compute_at_most_k_stepsf
      lib
      k
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
    = csuccess (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs)).
Proof.
  induction k; introv; simpl; sp.
  csunf; simpl.
  apply IHk.
Qed.

Lemma compute_at_most_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs,
    compute_at_most_k_steps
      lib
      k
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
    = csuccess (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs)).
Proof.
  induction k; introv; simpl; sp.
  rw IHk.
  csunf; simpl; auto.
Qed.

Lemma reduces_in_atmost_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs a,
    reduces_in_atmost_k_steps
      lib
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
      a
      k
    -> a = oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs).
Proof.
  induction k; introv comp.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl; ginv; tcsp.
Qed.
*)

Lemma compute_step_fresh_if_isvalue_like2 {o} :
  forall lib v vs (t : @NTerm o) bs,
    isvalue_like t
    -> compute_step lib (oterm (NCan NFresh) (bterm (v :: vs) t :: bs))
       = match vs, bs with
           | [],[] => csuccess (pushdown_fresh v t)
           | _,_ => cfailure "check 1st arg" (oterm (NCan NFresh) (bterm (v :: vs) t :: bs))
         end.
Proof.
  introv isv.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst;
    csunf; simpl; auto.
  - apply isexc_implies2 in isv; exrepnd; subst.
    csunf; simpl; auto.
Qed.

Lemma isvalue_like_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    isvalue_like t
    -> isvalue_like (lsubst_aux t sub).
Proof.
  introv isv.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst;
    simpl; eauto with slow.
  - apply isexc_implies2 in isv; exrepnd; subst.
    simpl; eauto with slow.
Qed.
Hint Resolve isvalue_like_lsubst_aux : slow.

Lemma isvalue_like_lsubst {o} :
  forall (t : @NTerm o) sub,
    isvalue_like t
    -> isvalue_like (lsubst t sub).
Proof.
  introv isv.
  pose proof (unfold_lsubst sub t) as h; exrepnd.
  rw h0.
  apply isvalue_like_lsubst_aux.
  apply alpha_eq_preserves_isvalue_like in h1; auto.
Qed.
Hint Resolve isvalue_like_lsubst : slow.

Lemma isvalue_like_subst {o} :
  forall (t : @NTerm o) v u,
    isvalue_like t
    -> isvalue_like (subst t v u).
Proof.
  introv isv.
  unfold subst; eauto with slow.
Qed.
Hint Resolve isvalue_like_subst : slow.

Fixpoint subst_utoken_aux_lsubst_aux {o} (usub : @utok_sub o) (sub : @Sub o) : Sub :=
  match sub with
    | nil => nil
    | (v,t) :: s => (v, subst_utokens_aux t usub) :: subst_utoken_aux_lsubst_aux usub s
  end.

Definition cl_utok_sub {p} (sub : @utok_sub p) :=
  forall a t, LIn (a,t) sub -> closed t.

Lemma sub_find_utok_sub_lsubst_aux {o} :
  forall (usub : @utok_sub o) sub v,
    sub_find (subst_utoken_aux_lsubst_aux usub sub) v
    = match sub_find sub v with
        | Some t => Some (subst_utokens_aux t usub)
        | None => None
      end.
Proof.
  induction sub; introv; simpl; auto.
  destruct a; simpl; boolvar; auto.
Qed.

Lemma cl_utok_sub_cons {o} :
  forall a t (sub : @utok_sub o),
    cl_utok_sub ((a,t) :: sub) <=> (closed t # cl_utok_sub sub).
Proof.
  introv; unfold cl_utok_sub; simpl; split; introv k; repnd; dands; tcsp.
  - eapply k; eauto.
  - introv i.
    eapply k; eauto.
  - introv i; repndors; cpx.
    eapply k; eauto.
Qed.

Lemma implies_cl_utok_sub_cons {o} :
  forall a t (sub : @utok_sub o),
    closed t
    -> cl_utok_sub sub
    -> cl_utok_sub ((a,t) :: sub).
Proof.
  introv c1 c2.
  apply cl_utok_sub_cons; auto.
Qed.
Hint Resolve implies_cl_utok_sub_cons : slow.

Lemma cl_utok_sub_nil {o} :
  @cl_utok_sub o [].
Proof.
  unfold cl_utok_sub; simpl; sp.
Qed.
Hint Resolve cl_utok_sub_nil : slow.

Lemma cl_utok_sub_implies_free_vars_utok_sub_nil {o} :
  forall (sub : @utok_sub o),
    cl_utok_sub sub
    -> free_vars_utok_sub sub = [].
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a.
  rw @cl_utok_sub_cons in cl; repnd.
  rw cl0; sp.
Qed.

Lemma cl_subst_utokens_aux {o} :
  forall (t : @NTerm o) sub,
    cl_utok_sub sub
    -> subst_utokens t sub = subst_utokens_aux t sub.
Proof.
  introv cl.
  unfold subst_utokens.
  rw @cl_utok_sub_implies_free_vars_utok_sub_nil; auto.
  boolvar; tcsp.
  provefalse; sp.
Qed.

Lemma sub_filter_subst_utoken_aux_lsubst_aux {o} :
  forall (usub : @utok_sub o) (sub : @Sub o) l,
    sub_filter (subst_utoken_aux_lsubst_aux usub sub) l
    = subst_utoken_aux_lsubst_aux usub (sub_filter sub l).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; allsimpl; tcsp.
  f_equal; sp.
Qed.

Lemma cl_subst_utokens_lsubst_aux {o} :
  forall (t : @NTerm o) sub usub,
    cl_utok_sub usub
    -> cl_sub sub
    -> subst_utokens_aux (lsubst_aux t sub) usub
       = lsubst_aux (subst_utokens_aux t usub) (subst_utoken_aux_lsubst_aux usub sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cl1 cl2; auto.

  - Case "vterm".
    simpl.
    rw @sub_find_utok_sub_lsubst_aux.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    rw @lsubst_aux_oterm.
    repeat (rw @subst_utokens_aux_oterm).
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst.
      unfold subst_utok.
      remember (utok_sub_find usub g) as usf; symmetry in Hequsf; destruct usf.

      * apply utok_sub_find_some in Hequsf.
        apply cl1 in Hequsf.
        rw @lsubst_aux_trivial_cl_term2; auto.

      * simpl; f_equal.
        unfold lsubst_bterms_aux.
        allrw map_map; allunfold @compose.
        apply eq_maps; introv i.
        destruct x as [l t]; simpl.
        f_equal.
        rw @sub_filter_subst_utoken_aux_lsubst_aux.
        eapply ind; eauto with slow.

    + simpl.
      f_equal.
      unfold lsubst_bterms_aux.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl.
      f_equal.
      rw @sub_filter_subst_utoken_aux_lsubst_aux.
      eapply ind; eauto with slow.
Qed.

Lemma isvalue_like_bot {o} :
  @isvalue_like o mk_bot -> False.
Proof.
  introv isv.
  unfold isvalue_like in isv; sp.
Qed.

Lemma isvalue_like_apply {o} :
  forall (a b : @NTerm o), isvalue_like (mk_apply a b) -> False.
Proof.
  introv isv.
  unfold isvalue_like in isv; tcsp.
Qed.

Lemma not_bot_reduces_to_value_like {p} :
  forall lib (t : @NTerm p), isvalue_like t -> !reduces_to lib mk_bot t.
Proof.
  introv isv r.
  unfold reduces_to in r; sp.
  revert t isv r.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct k.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    apply isvalue_like_bot in isv; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; simpl in r1; ginv.
    destruct k.

    + allrw @reduces_in_atmost_k_steps_0; subst.
      apply isvalue_like_apply in isv; sp.

    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      csunf r0; simpl in r0; ginv.
      unfold apply_bterm, lsubst in r1; allsimpl.
      apply ind in r1; tcsp.
Qed.

Lemma isprogram_fresh {p} :
  forall v (b : @NTerm p),
    isprogram (mk_fresh v b) <=> isprog_vars [v] b.
Proof.
  introv; split; introv k; allrw @isprog_vars_eq; repnd; dands.
  - inversion k as [c w].
    rw subvars_prop; introv i; simpl; left.
    unfold closed in c; allsimpl; allrw app_nil_r.
    destruct (deq_nvar v x); auto.
    assert (LIn x (remove_nvars [v] (free_vars b))) as h.
    { rw in_remove_nvars; simpl; sp. }
    rw c in h; allsimpl; sp.
  - inversion k as [c w].
    allrw @nt_wf_eq.
    apply wf_fresh_iff in w; auto.
  - split.
    + unfold closed.
      rw <- null_iff_nil.
      introv i; allsimpl; allrw app_nil_r.
      allrw in_remove_nvars; repnd; allsimpl; allrw not_over_or; repnd; GC.
      rw subvars_prop in k0; apply k0 in i0; allsimpl; sp.
    + allrw @nt_wf_eq.
      apply wf_fresh_iff; auto.
Qed.

Definition isprog_vars_utok_sub {o} (vs : list NVar) (sub : @utok_sub o) :=
  forall a t, LIn (a,t) sub -> isprog_vars vs t.

Lemma isprog_vars_utok_sub_nil {o} :
  forall vs, @isprog_vars_utok_sub o vs [].
Proof.
  introv i; allsimpl; sp.
Qed.
Hint Resolve isprog_vars_utok_sub_nil : slow.

Lemma isprog_vars_utok_sub_cons {o} :
  forall a (t : @NTerm o) sub vs,
    isprog_vars_utok_sub vs ((a,t) :: sub)
    <=> (isprog_vars vs t # isprog_vars_utok_sub vs sub).
Proof.
  introv; unfold isprog_vars_utok_sub; split; introv k; allsimpl; repnd; dands.
  - eapply k; eauto.
  - introv i; eapply k; eauto.
  - introv i; repndors; cpx.
    eapply k; eauto.
Qed.

Lemma implies_isprog_vars_utok_sub_cons {o} :
  forall a (t : @NTerm o) sub vs,
    isprog_vars vs t
    -> isprog_vars_utok_sub vs sub
    -> isprog_vars_utok_sub vs ((a,t) :: sub).
Proof.
  introv ispt isps.
  apply isprog_vars_utok_sub_cons; sp.
Qed.
Hint Resolve implies_isprog_vars_utok_sub_cons : slow.

Lemma isprog_vars_utok_sub_subvars {o} :
  forall (sub : @utok_sub o) vs1 vs2,
    subvars vs1 vs2
    -> isprog_vars_utok_sub vs1 sub
    -> isprog_vars_utok_sub vs2 sub.
Proof.
  induction sub; introv sv isp; allsimpl; eauto with slow.
  destruct a.
  allrw @isprog_vars_utok_sub_cons; repnd; dands; eauto with slow.
Qed.
Hint Resolve isprog_vars_utok_sub_subvars : slow.

Lemma implies_isprog_vars_subst_utokens_aux {o} :
  forall (t : @NTerm o) sub vs,
    isprog_vars_utok_sub vs sub
    -> isprog_vars vs t
    -> isprog_vars vs (subst_utokens_aux t sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv isps ipst; auto.
  Case "oterm".
  rw @subst_utokens_aux_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

  - apply get_utok_some in Heqguo; subst.
    unfold subst_utok.
    remember (utok_sub_find sub g) as usf; symmetry in Hequsf; destruct usf; auto.

    + apply utok_sub_find_some in Hequsf.
      apply isps in Hequsf; auto.

    + allrw @isprog_vars_ot_iff; allrw map_map; unfold compose; repnd; dands.

      * rw <- ipst0.
        apply eq_maps; introv i; destruct x as [l t]; unfold num_bvars; simpl; auto.

      * introv i.
        rw in_map_iff in i; exrepnd.
        destruct a as [l1 t1]; allsimpl; ginv.
        eapply ind; eauto with slow.

  - allrw @isprog_vars_ot_iff; allrw map_map; unfold compose; repnd.
    rw <- ipst0; dands.

    + apply eq_maps; introv i; destruct x as [l t]; unfold num_bvars; simpl; auto.

    + introv i.
      rw in_map_iff in i; exrepnd.
      destruct a as [l1 t1]; allsimpl; ginv.
      eapply ind; eauto with slow.
Qed.

Lemma implies_isprog_vars_subst_utokens {o} :
  forall (t : @NTerm o) sub vs,
    isprog_vars_utok_sub vs sub
    -> isprog_vars vs t
    -> isprog_vars vs (subst_utokens t sub).
Proof.
  introv isps ispt.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0.
  apply implies_isprog_vars_subst_utokens_aux; auto.
  eapply alphaeq_preserves_isprog_vars in h1; eauto.
Qed.

(* !!MOVE *)
Hint Resolve isprog_vars_mk_var : slow.
Hint Resolve nt_wf_utoken : slow.

Definition covered_sub {p} (sub1 sub2 : @Sub p) :=
  sub_range_sat sub1 (fun t => covered t (dom_sub sub2)).

Lemma covered_sub_nil {o} :
  forall (sub : @Sub o),
    covered_sub [] sub.
Proof.
  introv; unfold covered_sub, sub_range_sat; allsimpl; sp.
Qed.

Lemma covered_sub_cons {o} :
  forall v t (sub1 sub2 : @Sub o),
    covered_sub ((v,t) :: sub1) sub2
    <=> (covered t (dom_sub sub2) # covered_sub sub1 sub2).
Proof.
  unfold covered_sub, sub_range_sat; introv; split; intro k; repnd; dands; introv.
  - apply (k v t); simpl; sp.
  - intro i; apply (k v0 t0); simpl; sp.
  - intro i; simpl in i; dorn i; cpx.
    apply (k v0 t0); auto.
Qed.

Lemma implies_cl_sub_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub2
    -> covered_sub sub1 sub2
    -> cl_sub (lsubst_aux_sub sub1 sub2).
Proof.
  induction sub1; introv cl cov; allsimpl; auto.
  - apply cl_sub_nil.
  - destruct a.
    rw @covered_sub_cons in cov; repnd.
    apply cl_sub_cons; dands; auto.
    apply closed_lsubst_aux; auto.
Qed.

Lemma simple_lsubst_aux_lsubst_aux_sub_aeq {o} :
  forall (t t' : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> covered_sub sub1 sub2
    -> disjoint (bound_vars t') (sub_free_vars sub1)
    -> alpha_eq t t'
    -> alpha_eq
         (lsubst_aux (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                     (lsubst_aux_sub sub1 sub2))
         (lsubst_aux (lsubst_aux t' sub1) sub2).
Proof.
  introv cl cov disj aeq.
  pose proof (simple_lsubst_aux_lsubst_aux_sub t' sub1 sub2 cl disj) as h.
  rw <- h; clear h.
  repeat (apply lsubst_aux_alpha_congr_same_cl_sub); auto.
  - apply implies_cl_sub_filter; auto.
  - apply implies_cl_sub_lsubst_aux_sub; auto.
Qed.

Lemma simple_lsubst_lsubst_aux_sub_aeq {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> covered_sub sub1 sub2
    -> alpha_eq
         (lsubst (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                 (lsubst_aux_sub sub1 sub2))
         (lsubst_aux (lsubst t sub1) sub2).
Proof.
  introv cl cov.
  unfold lsubst; allsimpl; boolvar; allsimpl;
  try (complete (destruct n;
                 pose proof (implies_cl_sub_lsubst_aux_sub sub1 sub2 cl cov) as h;
                 apply flat_map_free_vars_range_cl_sub in h; rw h; auto)).

  - rw @simple_lsubst_aux_lsubst_aux_sub; auto.
    rw @sub_free_vars_is_flat_map_free_vars_range; auto.

  - pose proof (change_bvars_alpha_spec t (flat_map free_vars (range sub1))) as h;
    simpl in h; repnd.
    remember (change_bvars_alpha (flat_map free_vars (range sub1)) t) as t';
      clear Heqt'.

    apply simple_lsubst_aux_lsubst_aux_sub_aeq; eauto with slow.
    rw @sub_free_vars_is_flat_map_free_vars_range; eauto with slow.
Qed.

Lemma alpha_eq_oterm_snd_subterm {o} :
  forall op b b1 b2 (bs : list (@BTerm o)),
    alpha_eq_bterm b1 b2
    -> alpha_eq (oterm op (b :: b1 :: bs)) (oterm op (b :: b2 :: bs)).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv k.
  destruct n; cpx.
  destruct n; cpx.
Qed.

Lemma alpha_eq_oterm_fst_subterm {o} :
  forall op b1 b2 (bs : list (@BTerm o)),
    alpha_eq_bterm b1 b2
    -> alpha_eq (oterm op (b1 :: bs)) (oterm op (b2 :: bs)).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv k.
  destruct n; cpx.
Qed.

Lemma compute_step_catch_non_trycatch {o} :
  forall ncan (bts bs : list (@BTerm o)),
    ncan <> NTryCatch
    -> compute_step_catch
         ncan
         (oterm (NCan ncan) (bterm [] (oterm Exc bts) :: bs))
         bts
         bs
       = csuccess (oterm Exc bts).
Proof.
  introv d.
  unfold compute_step_catch; destruct ncan; auto; cpx.
Qed.

Lemma implies_prog_sub_cons {o} :
  forall (sub : @Sub o) (v : NVar) (t : NTerm),
    isprogram t
    -> prog_sub sub
    -> prog_sub ((v, t) :: sub).
Proof.
  introv a b.
  rw @prog_sub_cons; auto.
Qed.
Hint Resolve implies_prog_sub_cons : slow.

(* !! MOVE *)
Hint Resolve prog_sub_sub_filter : slow.

Lemma cl_lsubst_aux_swap_cons_snoc {o} :
  forall (t : @NTerm o) sub v u,
    cl_sub sub
    -> closed u
    -> !LIn v (dom_sub sub)
    -> lsubst_aux t ((v, u) :: sub) = lsubst_aux t (snoc sub (v, u)).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cls clu ni; allsimpl; auto.

  - Case "vterm".
    rw @sub_find_snoc; boolvar; auto.

    + remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.
      apply sub_find_some in Heqsf.
      apply in_sub_eta in Heqsf; sp.

    + remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    f_equal; simpl.
    boolvar; tcsp.

    + rw @sub_filter_snoc; boolvar; tcsp.

    + rw @sub_filter_snoc; boolvar; tcsp.
      eapply ind; eauto with slow.
      rw <- @dom_sub_sub_filter.
      rw in_remove_nvars; sp.
Qed.

Lemma cl_sub_snoc {o} :
  forall (sub : @Sub o) v t,
    cl_sub (snoc sub (v,t))
    <=> (cl_sub sub # closed t).
Proof.
  induction sub; introv; allsimpl; split; intro k; repnd; dands; eauto with slow;
  allrw @cl_sub_cons; repnd; dands; eauto with slow.
  - apply IHsub in k; sp.
  - apply IHsub in k; sp.
  - apply IHsub; sp.
Qed.

Lemma implies_cl_sub_snoc {o} :
  forall (sub : @Sub o) v t,
    cl_sub sub
    -> closed t
    -> cl_sub (snoc sub (v,t)).
Proof.
  introv cls clt.
  apply cl_sub_snoc; sp.
Qed.
Hint Resolve implies_cl_sub_snoc : slow.

Lemma cl_lsubst_swap {o} :
  forall (t : @NTerm o) sub v u,
    cl_sub sub
    -> closed u
    -> !LIn v (dom_sub sub)
    -> lsubst t ((v, u) :: sub) = lsubst t (snoc sub (v, u)).
Proof.
  introv cls clu ni.
  unfold lsubst; simpl.
  rw clu; allsimpl.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_if_cl_sub; eauto with slow.
  boolvar; tcsp; try (complete (provefalse; tcsp)).
  apply cl_lsubst_aux_swap_cons_snoc; auto.
Qed.

Lemma cl_simple_lsubst_cons3 {o} :
  forall (t : @NTerm o) v u sub,
    cl_sub ((v, u) :: sub)
    -> !LIn v (dom_sub sub)
    -> subst (lsubst t sub) v u = lsubst t ((v, u) :: sub).
Proof.
  introv Hps Hd.
  allrw @cl_sub_cons; repnd.
  rw @cl_lsubst_swap; auto.
  rw snoc_as_append.
  rw @cl_lsubst_app; eauto with slow.
Qed.

Lemma cl_simple_lsubst_cons2 {o} :
  forall (t : @NTerm o) v u sub,
    cl_sub ((v, u) :: sub)
    -> lsubst (subst t v u) sub = lsubst t ((v, u) :: sub).
Proof.
  introv cl.
  allrw @cl_sub_cons; repnd.
  unfold subst.
  rw <- @cl_lsubst_app; eauto with slow.
Qed.

Lemma isnoncan_like_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    isnoncan_like t
    -> isnoncan_like (lsubst_aux t sub).
Proof.
  introv isv.
  unfold isnoncan_like in isv; repndors.
  - apply isnoncan_implies in isv; exrepnd; subst.
    simpl; eauto with slow.
  - apply isabs_implies in isv; exrepnd; subst.
    simpl; eauto with slow.
Qed.
Hint Resolve isnoncan_like_lsubst_aux : slow.

Lemma iscan_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    iscan t
    -> iscan (lsubst_aux t sub).
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst; allsimpl; auto.
Qed.
Hint Resolve iscan_lsubst_aux : slow.

Lemma isexc_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    isexc t
    -> isexc (lsubst_aux t sub).
Proof.
  introv ise.
  apply isexc_implies2 in ise; exrepnd; subst; allsimpl; auto.
Qed.
Hint Resolve isexc_lsubst_aux : slow.

Lemma alpha_eq_preserves_isnoncan_like {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> isnoncan_like a
    -> isnoncan_like b.
Proof.
  introv aeq iv.
  unfold isnoncan_like in iv.
  repndors.
  - apply isnoncan_implies in iv; exrepnd; subst.
    inversion aeq; subst; left; sp.
  - apply isabs_implies in iv; exrepnd; subst.
    inversion aeq; subst; right; sp.
Qed.

Lemma isnoncan_like_lsubst {o} :
  forall (t : @NTerm o) sub,
    isnoncan_like t
    -> isnoncan_like (lsubst t sub).
Proof.
  introv isv.
  pose proof (unfold_lsubst sub t) as h; exrepnd.
  rw h0.
  apply isnoncan_like_lsubst_aux.
  apply alpha_eq_preserves_isnoncan_like in h1; auto.
Qed.
Hint Resolve isnoncan_like_lsubst : slow.

Lemma compute_step_ncan_vterm_success {o} :
  forall lib ncan (bs : list (@BTerm o)) u a,
    compute_step lib (oterm (NCan ncan) (bterm [] (mk_utoken a) :: bs))
    = csuccess u
    -> (
         (ncan = NParallel # u = mk_axiom)
         [+]
         (ncan = NFix
          # bs = []
          # u = mk_apply (mk_utoken a) (mk_fix (mk_utoken a)))
         [+]
         {x : NVar
          & {b : NTerm
          & ncan = NCbv
          # bs = [bterm [x] b]
          # u = subst b x (mk_utoken a)}}
         [+]
         {a' : NTerm
          & {x : NVar
          & {b : NTerm
          & ncan = NTryCatch
          # bs = [nobnd a', bterm [x] b]
          # u = mk_atom_eq a' a' (mk_utoken a) mk_bot}}}
         [+]
         {t1 : NTerm
          & {bs1 : list BTerm
          & bs = nobnd t1 :: bs1
          # ncan = NCompOp CompOpEq
          # (
              {t2 : NTerm
               & {t3 : NTerm

                       & {pk : param_kind
               & bs1 = [nobnd t2, nobnd t3]
               # t1 = pk2term pk
               # ((pk = PKa a # u = t2) [+] (pk <> PKa a # u = t3))}}}
              [+]
              {x : NTerm
               & compute_step lib t1 = csuccess x
               # isnoncan_like t1
               # u = oterm (NCan ncan) (nobnd (mk_utoken a) :: nobnd x :: bs1) }
              [+]
              (isexc t1 # u = t1)
            )}}
         [+]
         {t1 : NTerm
          & {t2 : NTerm
          & {x : CanonicalTest
          & ncan = NCanTest x
          # bs = [nobnd t1, nobnd t2]
          # ((x = CanIsuatom # u = t1) [+] (x <> CanIsuatom # u = t2))}}}
       ).
Proof.
  introv comp.
  csunf comp.
  allsimpl.
  unfold compute_step_can in comp.
  dopid_noncan ncan Case;
    try (complete (allsimpl; ginv));
    try (complete (destruct bs; ginv)).

  - Case "NFix".
    apply compute_step_fix_success in comp; repnd; subst.
    right; left; auto.

  - Case "NCbv".
    apply compute_step_cbv_success in comp; exrepnd; subst.
    right; right; left.
    exists v x; auto.

  - Case "NTryCatch".
    apply compute_step_try_success in comp; exrepnd; subst.
    right; right; right; left.
    exists a0 v x; auto.

  - Case "NParallel".
    apply compute_step_parallel_success in comp; subst; tcsp.

  - Case "NCompOp".
    right; right; right; right; left.
    boolvar; tcsp; ginv.
    destruct bs; ginv; try (complete (allsimpl; dcwf h));[].
    destruct b as [l t].
    destruct l; ginv; try (complete (allsimpl; dcwf h));[].
    destruct t as [v1|op1 bs1]; try (complete (allsimpl; dcwf h));[].

    dcwf h.
    allunfold @co_wf_def; exrepnd; allsimpl; ginv; GC.
    repndors; exrepnd; subst; ginv;[].
    dopid op1 as [can1|ncan1|exc1|abs1] SCase.

    + SCase "Can".
      apply compute_step_compop_success_can_can in comp; exrepnd; subst; GC.
      repndors; exrepnd; subst; allsimpl; ginv.
      allrw @get_param_from_cop_some; subst.
      exists (oterm (Can (pk2can pk2)) []) [nobnd t1, nobnd t2]; dands; auto.
      left.
      exists t1 t2 pk2.
      allrw @pk2term_eq; dands; auto.
      boolvar; tcsp.

    + SCase "NCan".
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as c1; ginv.
      destruct c1; allsimpl; ginv.
      exists (oterm (NCan ncan1) bs1) bs; dands; auto.
      right; left.
      exists n; dands; auto.

    + SCase "Exc".
      ginv.
      exists (oterm Exc bs1) bs; dands; auto.

    + SCase "Abs".
      remember (compute_step lib (oterm (Abs abs1) bs1)) as c1; ginv.
      destruct c1; allsimpl; ginv.
      exists (oterm (Abs abs1) bs1) bs; dands; auto.
      right; left.
      exists n; dands; auto.

  - Case "NCanTest".
    right; right; right; right; right.
    apply compute_step_can_test_success in comp; exrepnd; subst.
    exists arg2nt arg3nt c; dands; auto.
    destruct c; allsimpl; tcsp;
    try (complete (right; dands; auto; intro k; inversion k)).
Qed.

Lemma singleton_disjoint :
  forall T (x y : T),
    x <> y -> disjoint [x] [y].
Proof.
  introv ni.
  apply disjoint_singleton_l; simpl; sp.
Qed.
Hint Resolve singleton_disjoint : slow.

Lemma allvars_sub_nil {o} :
  @allvars_sub o [].
Proof.
  unfold allvars_sub, sub_range_sat; simpl; sp.
Qed.
Hint Resolve allvars_sub_nil : slow.

Lemma isvariable_implies {o} :
  forall (t : @NTerm o), isvariable t -> {v : NVar & t = vterm v}.
Proof.
  introv isv.
  destruct t; allsimpl; tcsp.
  eexists; eauto.
Qed.

Lemma allvars_sub_cons {o} :
  forall v t (s : @Sub o),
    allvars_sub ((v,t) :: s) <=> (isvariable t # allvars_sub s).
Proof.
  introv; unfold allvars_sub, sub_range_sat; simpl; split; intro k; repnd; dands.
  - pose proof (k v t) as h; autodimp h hyp.
    unfold isvarc in h; exrepnd; subst; simpl; auto.
  - introv h; eapply k; eauto.
  - introv h; repndors; cpx; repdors.
    + apply isvariable_implies in k0; auto.
    + eapply k; eauto.
Qed.

Lemma implies_allvars_sub_cons {o} :
  forall v t (s : @Sub o),
    isvariable t
    -> allvars_sub s
    -> allvars_sub ((v,t) :: s).
Proof.
  introv a b; apply allvars_sub_cons; sp.
Qed.
Hint Resolve implies_allvars_sub_cons : slow.

Lemma isvariable_var {o} :
  forall v, @isvariable o (mk_var v).
Proof. sp. Qed.
Hint Resolve isvariable_var : slow.

Lemma lsubst_aux_utoken_eq_utoken_implies {o} :
  forall (t : @NTerm o) a sub,
    lsubst_aux t sub = mk_utoken a
    -> !LIn a (get_utokens t)
    -> {v : NVar & sub_find sub v = Some (mk_utoken a) # t = mk_var v}.
Proof.
  destruct t as [v|op bs ind]; introv e ni; allsimpl; GC; ginv.

  - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; subst; ginv.
    eexists; dands; eauto.

  - inversion e; subst.
    destruct bs; allsimpl; cpx; GC; fold_terms.
    allrw not_over_or; sp.
Qed.

Lemma lsubst_aux_utoken_eq_utoken_implies2 {o} :
  forall (t : @NTerm o) a sub,
    lsubst_aux t sub = mk_utoken a
    -> !LIn a (get_utokens_sub sub)
    -> t = mk_utoken a.
Proof.
  destruct t as [v|op bs ind]; introv e ni; allsimpl; GC; ginv.

  - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; subst; ginv.
    apply sub_find_some in Heqsf.
    destruct ni; unfold get_utokens_sub.
    rw lin_flat_map.
    exists (mk_utoken a); simpl; dands; tcsp.
    apply in_sub_eta in Heqsf; sp.

  - inversion e; subst.
    destruct bs; allsimpl; cpx; GC; fold_terms.
Qed.

Lemma memvar_cons :
  forall x v vs,
    memvar x (v :: vs) =
    if deq_nvar x v then true else memvar x vs.
Proof.
  introv.
  unfold memvar; simpl.
  boolvar; tcsp.
Qed.

Lemma remove_nvars_swapbvars_nil :
  forall vs vs1 vs2,
    length vs1 = length vs2
    -> subvars vs vs1
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> remove_nvars vs2 (swapbvars (mk_swapping vs1 vs2) vs) = [].
Proof.
  induction vs; introv len sv norep disj; allsimpl.
  - rw remove_nvars_nil_r; auto.
  - allrw subvars_cons_l; repnd.
    rw remove_nvars_cons_r; boolvar; tcsp.
    rw IHvs; auto.
    destruct Heqb.
    apply swapvar_implies3; auto.
Qed.

Lemma compute_step_ncompop_can1_success {o} :
  forall lib c can (bts bs : list (@BTerm o)) u,
    compute_step lib (oterm (NCan (NCompOp c)) (bterm [] (oterm (Can can) bts) :: bs))
    = csuccess u
    -> co_wf_def c can bts
       #
       (
          {can' : CanonicalOp
           & {t1 : NTerm
           & {t2 : NTerm
           & bs = [nobnd (oterm (Can can') []),nobnd t1,nobnd t2]
           # compute_step_comp
               c can can' bts [] [nobnd t1, nobnd t2]
               (oterm (NCan (NCompOp c)) (bterm [] (oterm (Can can) bts) :: bs))
             = csuccess u}}}
          [+]
          {t : NTerm
           & {t' : NTerm
           & {bs' : list BTerm
           & bs = bterm [] t :: bs'
           # isnoncan_like t
           # compute_step lib t = csuccess t'
           # u = oterm (NCan (NCompOp c)) (bterm [] (oterm (Can can) bts) :: bterm [] t' :: bs')}}}
          [+]
           {t : NTerm
           & {bs' : list BTerm
           & isexc t
           # bs = nobnd t :: bs'
           # u = t}}
         ).
Proof.
  introv comp.
  csunf comp; allsimpl.
  dcwf h; dands; auto;[].
  destruct bs as [|b bs]; ginv;[].
  destruct b as [l t].
  destruct l as [|v vs]; ginv;[].
  destruct t as [v|op bs1]; ginv;[].
  dopid op as [can1|ncan1|exc1|abs1] Case; ginv.
  - Case "Can".
    dup comp as comp'.
    apply compute_step_compop_success_can_can in comp; exrepnd; subst.
    left; exists can1 t1 t2; dands; auto.
  - Case "NCan".
    remember (compute_step lib (oterm (NCan ncan1) bs1)) as nc.
    symmetry in Heqnc; destruct nc; allsimpl; ginv.
    right; left.
    exists (oterm (NCan ncan1) bs1) n bs; dands; auto.
  - Case "Exc".
    right; right.
    exists (oterm Exc bs1) bs; simpl; sp.
  - Case "Abs".
    remember (compute_step lib (oterm (Abs abs1) bs1)) as nc.
    symmetry in Heqnc; destruct nc; allsimpl; ginv.
    right; left.
    exists (oterm (Abs abs1) bs1) n bs; dands; auto.
Qed.

Lemma compute_step_narithop_can1_success {o} :
  forall lib c can (bts bs : list (@BTerm o)) u,
    compute_step lib (oterm (NCan (NArithOp c)) (bterm [] (oterm (Can can) bts) :: bs))
    = csuccess u
    -> ca_wf_def can bts
       # (
          {can' : CanonicalOp
           & bs = [nobnd (oterm (Can can') [])]
           # compute_step_arith
               c can can' bts [] []
               (oterm (NCan (NArithOp c)) (bterm [] (oterm (Can can) bts) :: bs))
             = csuccess u}
          [+]
          {t : NTerm
           & {t' : NTerm
           & {bs' : list BTerm
           & bs = bterm [] t :: bs'
           # isnoncan_like t
           # compute_step lib t = csuccess t'
           # u = oterm (NCan (NArithOp c)) (bterm [] (oterm (Can can) bts) :: bterm [] t' :: bs')}}}
          [+]
           {t : NTerm
           & {bs' : list BTerm
           & isexc t
           # bs = nobnd t :: bs'
           # u = t}}
         ).
Proof.
  introv comp.
  csunf comp; allsimpl.
  dcwf h; dands; auto;[].
  destruct bs as [|b bs]; ginv;[].
  destruct b as [l t];[].
  destruct l as [|v vs]; ginv;[].
  destruct t as [v|op bs1]; ginv;[].
  dopid op as [can1|ncan1|exc1|abs1] Case; ginv.
  - Case "Can".
    apply compute_step_arithop_success_can_can in comp; exrepnd; subst.
    allapply @get_param_from_cop_pki; subst; allsimpl.
    left; exists (@Nint o n2); dands; auto.
  - Case "NCan".
    remember (compute_step lib (oterm (NCan ncan1) bs1)) as nc.
    symmetry in Heqnc; destruct nc; allsimpl; ginv.
    right; left.
    exists (oterm (NCan ncan1) bs1) n bs; dands; auto.
  - Case "Exc".
    right; right.
    exists (oterm Exc bs1) bs; simpl; sp.
  - Case "Abs".
    remember (compute_step lib (oterm (Abs abs1) bs1)) as nc.
    symmetry in Heqnc; destruct nc; allsimpl; ginv.
    right; left.
    exists (oterm (Abs abs1) bs1) n bs; dands; auto.
Qed.

Lemma lsubst_aux_eq_spcan_implies {o} :
  forall (t : @NTerm o) sub can,
    lsubst_aux t sub = oterm (Can can) []
    -> ({v : NVar & sub_find sub v = Some (oterm (Can can) []) # t = mk_var v}
        [+] t = oterm (Can can) []).
Proof.
  introv e.
  destruct t as [v|op bs]; allsimpl; auto.
  - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; subst; ginv.
    left; exists v; dands; auto.
  - destruct bs; allsimpl; ginv; sp.
Qed.

Lemma lsubst_aux_eq_vterm_implies {o} :
  forall (t : @NTerm o) sub v,
    lsubst_aux t sub = vterm v
    -> ({x : NVar & sub_find sub x = Some (vterm v) # t = mk_var x}
        [+] t = vterm v).
Proof.
  introv e.
  destruct t as [z|op bs]; allsimpl; auto.
  - remember (sub_find sub z) as sf; symmetry in Heqsf; destruct sf; subst; ginv; tcsp.
    left; exists z; dands; auto.
  - destruct bs; allsimpl; ginv; sp.
Qed.

Lemma compute_step_narithop_ncanlike2 {p} :
  forall lib ar c cbts (t : @NTerm p) rest,
    isnoncan_like t
    -> compute_step
         lib
         (oterm (NCan (NArithOp ar))
                (bterm [] (oterm (Can c) cbts)
                       :: bterm [] t
                       :: rest))
       = if ca_wf c cbts
         then match compute_step lib t with
                | csuccess f => csuccess (oterm (NCan (NArithOp ar))
                                                (bterm [] (oterm (Can c) cbts)
                                                       :: bterm [] f
                                                       :: rest))
                | cfailure str ts => cfailure str ts
              end
         else cfailure bad_args (oterm (NCan (NArithOp ar))
                                       (bterm [] (oterm (Can c) cbts)
                                              :: bterm [] t
                                              :: rest)).
Proof.
  introv isn.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    rw @compute_step_eq_unfold; sp.
  - apply isabs_implies in isn; exrepnd; subst.
    rw @compute_step_eq_unfold; sp.
Qed.

Lemma alpha_eq_mk_vbot_lsubst_aux {o} :
  forall v1 v2 (sub : @Sub o),
    alpha_eq (mk_vbot v1) (lsubst_aux (mk_vbot v2) sub).
Proof.
  introv; simpl.
  allrw @sub_filter_nil_r.
  rw @sub_find_sub_filter_eq; rw memvar_singleton; boolvar; tcsp.
  unfold mk_vbot.
  prove_alpha_eq4; introv h; destruct n; cpx.
  apply alphaeqbt_nilv2.
  prove_alpha_eq4; introv k; destruct n; cpx.
  pose proof (ex_fresh_var [v1,v2]) as fv; exrepnd.
  apply (al_bterm _ _ [v]); allsimpl; auto;
  allrw disjoint_singleton_l; allsimpl; tcsp.
  unfold lsubst; simpl; boolvar; auto.
Qed.
Hint Resolve alpha_eq_mk_vbot_lsubst_aux : slow.

Lemma alpha_eq_mk_bot_implies {o} :
  forall (t : @NTerm o),
    alpha_eq mk_bot t
    -> {v : NVar & t = mk_vbot v}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len imp]; subst; allsimpl; cpx; clear aeq.
  pose proof (imp 0) as h; clear imp; autodimp h hyp.
  unfold selectbt in h; allsimpl.
  apply alphaeqbt_nilv in h; exrepnd; subst.
  inversion h0 as [|? ? ? len imp]; subst; allsimpl; cpx; clear h0.
  pose proof (imp 0) as h; clear imp; autodimp h hyp.
  unfold selectbt in h; allsimpl.
  apply alphaeqbt_1v in h; exrepnd; subst; allrw disjoint_singleton_l.
  allunfold @lsubst; allsimpl.
  allrw not_over_or; repnd; boolvar; allrw disjoint_singleton_r.
  - destruct nt2 as [v|op bs]; allsimpl; allrw not_over_or; repnd; boolvar; tcsp;
    inversion h0; subst; tcsp.
    exists v; auto.
  - destruct n; allunfold @all_vars; allrw in_app_iff; sp.
Qed.

Lemma alpha_eq_mk_bot_lsubst {o} :
  forall (sub : @Sub o),
    alpha_eq mk_bot (lsubst mk_bot sub).
Proof.
  introv.
  pose proof (unfold_lsubst sub mk_bot) as h; exrepnd; rw h0.
  apply alpha_eq_mk_bot_implies in h1; exrepnd; subst.
  apply alpha_eq_mk_vbot_lsubst_aux.
Qed.
Hint Resolve alpha_eq_mk_bot_lsubst : slow.

Lemma compute_step_fresh_if_isnoncan_like {o} :
  forall lib v vs (t : @NTerm o) bs,
    isnoncan_like t
    -> compute_step lib (oterm (NCan NFresh) (bterm (v :: vs) t :: bs))
       = match vs with
           | [] =>
             match bs with
               | [] =>
                 on_success
                   (compute_step lib (subst t v (mk_utoken (get_fresh_atom lib t))))
                   (fun r : NTerm => mk_fresh v (subst_utokens r [(get_fresh_atom lib t, mk_var v)]))
               | _ :: _ =>
                 cfailure "check 1st arg"
                          (oterm (NCan NFresh) (bterm (v :: vs) t :: bs))
             end
           | _ :: _ =>
             cfailure "check 1st arg"
                      (oterm (NCan NFresh) (bterm (v :: vs) t :: bs))
         end.
Proof.
  introv isn.
  csunf; simpl.
  destruct vs; auto.
  destruct bs; auto.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst; auto.
  - apply isabs_implies in isn; exrepnd; subst; auto.
Qed.

Lemma implies_alpha_eq_mk_fresh_subst_utokens {o} :
  forall n a (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (mk_fresh n (subst_utokens t1 [(a, mk_var n)]))
                (mk_fresh n (subst_utokens t2 [(a, mk_var n)])).
Proof.
  introv aeq.
  unfold mk_fresh.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; cpx.
  apply alpha_eq_bterm_congr; auto.
  apply alpha_eq_subst_utokens; eauto with slow.
Qed.

Lemma alpha_eq_oterm_combine2 {o} :
  forall op1 op2 (bs1 bs2 : list (@BTerm o)),
    alpha_eq (oterm op1 bs1) (oterm op2 bs2)
    <=> (op1 = op2
         # length bs1 = length bs2
         # (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> alpha_eq_bterm b1 b2)).
Proof.
  introv; split; intro k.
  - inversion k; subst; dands; auto.
    introv i.
    allunfold @selectbt.
    allrw in_combine_sel_iff; exrepnd.
    discover.
    rw (nth_select1 n bs1 (@default_bt o)) in i3; auto.
    rw (nth_select1 n bs2 (@default_bt o)) in i0; auto.
    ginv; auto.
  - repnd; subst; constructor; auto.
    introv i.
    unfold selectbt.
    apply k.
    apply in_combine_sel_iff.
    exists n; dands; auto; try omega.
    + rw (nth_select1 n bs1 (@default_bt o)); auto.
    + rw (nth_select1 n bs2 (@default_bt o)); auto; try omega.
Qed.

Lemma lsubst_subst_utokens_aux_disj {o} :
  forall (t : @NTerm o) (sub : Sub) (usub : utok_sub),
    disjoint (get_utokens_sub sub) (utok_sub_dom usub)
    -> disjoint (free_vars_utok_sub usub) (dom_sub sub)
    -> disjoint (sub_free_vars sub) (bound_vars (subst_utokens_aux t usub))
    -> disjoint (sub_free_vars sub) (bound_vars t)
    -> lsubst (subst_utokens_aux t usub) sub
       = subst_utokens_aux (lsubst t sub) usub.
Proof.
  introv d1 d2 d3 d4.
  unfold lsubst; boolvar; tcsp;
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  - apply lsubst_aux_subst_utokens_aux_disj; auto.
  - provefalse; destruct n; eauto with slow.
  - provefalse; destruct n; eauto with slow.
  - provefalse; destruct n; eauto with slow.
Qed.

Lemma sub_free_vars_var_ren {o} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> @sub_free_vars o (var_ren vs1 vs2) = vs2.
Proof.
  induction vs1; introv len; allsimpl; cpx.
  destruct vs2; allsimpl; cpx.
  f_equal; tcsp.
  fold (@var_ren o vs1 vs2); sp.
Qed.

Lemma get_utokens_sub_allvars_sub {o} :
  forall (sub : @Sub o),
    allvars_sub sub
    -> get_utokens_sub sub = [].
Proof.
  induction sub; introv av; allsimpl; tcsp.
  destruct a.
  allrw @allvars_sub_cons; repnd.
  apply isvariable_implies in av0; exrepnd; subst.
  unfold get_utokens_sub; simpl; sp.
Qed.

Lemma get_utokens_sub_var_ren {o} :
  forall vs1 vs2,
    @get_utokens_sub o (var_ren vs1 vs2) = [].
Proof.
  introv; apply get_utokens_sub_allvars_sub; eauto with slow.
Qed.

Lemma allvars_sub_sub_keep_first {o} :
  forall (sub : @Sub o) vs,
    allvars_sub sub
    -> allvars_sub (sub_keep_first sub vs).
Proof.
  induction sub; introv av; allsimpl; tcsp.
  destruct a; allrw @allvars_sub_cons; repnd.
  boolvar; tcsp.
  rw @allvars_sub_cons; dands; auto.
Qed.
Hint Resolve allvars_sub_sub_keep_first : slow.

Lemma lsubst_sub_trivial {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub2
    -> disjoint (sub_free_vars sub1) (dom_sub sub2)
    -> lsubst_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv cl d; allsimpl; auto.
  destruct a.
  allrw disjoint_app_l; repnd.
  f_equal; tcsp.
  rw @cl_lsubst_trivial; eauto with slow.
Qed.

Lemma simple_alphaeq_subst_utokens_aux_lsubst_aux {o} :
  forall (t' t : @NTerm o) v a,
    !LIn a (get_utokens t)
    -> !LIn v (bound_vars t')
    -> alpha_eq (lsubst_aux t [(v, mk_utoken a)]) t'
    -> alpha_eq (subst_utokens_aux t' [(a, mk_var v)]) t.
Proof.
  nterm_ind1s t' as [v|op bs ind] Case; introv ni1 ni2 aeq; auto.

  - Case "vterm".
    allsimpl; GC.
    destruct t as [v1|op1 bs1]; allsimpl; boolvar; allsimpl; GC;
    inversion aeq; subst; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    destruct t as [v1|op1 bs1]; allsimpl; boolvar; GC;
    try (complete (inversion aeq)).

    + inversion aeq; subst; allsimpl; cpx; allsimpl; fold_terms; GC.
      unfold subst_utok; simpl; boolvar; tcsp.

    + allrw in_app_iff; allrw not_over_or; repnd.
      rw @alpha_eq_oterm_combine2 in aeq; repnd; subst.
      allrw map_length.
      remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

      * apply get_utok_some in Heqguo; subst; allsimpl; allrw not_over_or; repnd; GC.
        unfold subst_utok; simpl; boolvar; subst; tcsp.
        apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
        introv i.
        rw <- map_combine_left in i.
        rw in_map_iff in i; exrepnd; cpx; allsimpl.
        destruct a1 as [l1 t1].
        destruct a0 as [l2 t2]; allsimpl.

        pose proof (aeq (lsubst_bterm_aux (bterm l2 t2) [(v,mk_utoken a)]) (bterm l1 t1)) as h.
        autodimp h hyp.
        { rw <- map_combine_left.
          rw in_map_iff.
          apply in_combine_swap in i1; auto.
          eexists; dands; eauto. }

        allsimpl.
        applydup in_combine in i1; repnd.
        apply alphaeq_bterm3_if
        with (lva := v
                       :: all_vars (subst_utokens_aux t1 [(a, mk_var v)])
                       ++ all_vars t2
                       ++ bound_vars (lsubst t2 [(v, mk_utoken a)])
             )
          in h.

        inversion h as [? ? ? ? ? disj len1 len2 norep al]; subst; clear h.
        allrw disjoint_app_r; allrw disjoint_cons_r; allrw disjoint_app_r; repnd.

        apply (al_bterm _ _ lv); allrw disjoint_app_r; dands; try omega; eauto with slow.

        assert (!LIn v l1) as ni.
        { intro k; destruct ni2.
          rw lin_flat_map; eexists; dands; eauto.
          simpl; rw in_app_iff; sp. }

        rw @lsubst_subst_utokens_aux_disj; simpl;
        allrw @dom_sub_var_ren;
        allrw @sub_free_vars_var_ren;
        allrw @get_utokens_sub_var_ren;
        allrw disjoint_singleton_l;
        try omega; eauto with slow.

        pose proof (ind t1 (lsubst t1 (var_ren l1 lv)) l1) as h; clear ind.
        repeat (autodimp h hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }
        pose proof (h (lsubst t2 (var_ren l2 lv)) v a) as k; clear h.
        repeat (autodimp k hyp).

        { intro k.
          apply get_utokens_lsubst in k.
          rw @get_utokens_sub_allvars_sub in k; eauto with slow.
          allrw in_app_iff; allsimpl; repndors; tcsp.
          destruct ni1; rw lin_flat_map; eexists; dands; eauto. }

        { rw @boundvars_lsubst_vars; auto; try omega.
          intro k; destruct ni2; rw lin_flat_map; eexists; dands; eauto; simpl.
          rw in_app_iff; sp. }

        { apply alpha_eq_if3 in al.
          boolvar.

          - allrw @lsubst_aux_nil.
            pose proof (simple_lsubst_lsubst_sub_aeq3
                          t2 (var_ren l2 lv) [(v, mk_utoken a)]) as h.
            repeat (autodimp h hyp); simpl; eauto 2 with slow.
            allsimpl; rw @dom_sub_var_ren in h; auto; boolvar; tcsp.
            allrw @lsubst_nil.
            repeat (rw <- @lsubst_lsubst_aux2 in al; try omega; eauto 2 with slow).
            rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
            rw @lsubst_sub_trivial in h; simpl;
            try (rw @sub_free_vars_var_ren); try (rw disjoint_singleton_r);
            eauto with slow.

          - rw <- (lsubst_lsubst_aux2 t1) in al; try omega; eauto 2 with slow.
            eapply alpha_eq_trans;[|exact al].
            rw <- (cl_lsubst_lsubst_aux t2); eauto 2 with slow.
            rw <- (cl_lsubst_lsubst_aux (lsubst t2 (var_ren l2 lv))); eauto 2 with slow.
            pose proof (simple_lsubst_lsubst_sub_aeq3
                          t2 (var_ren l2 lv) [(v, mk_utoken a)]) as h.
            repeat (autodimp h hyp); simpl; eauto 2 with slow.
            allsimpl; rw @dom_sub_var_ren in h; auto; boolvar; tcsp.
            eapply alpha_eq_trans;[apply alpha_eq_sym; apply h|].
            rw @lsubst_sub_trivial; simpl;
            try (rw @sub_free_vars_var_ren); try (rw disjoint_singleton_r);
            eauto 2 with slow.
            rw <- @lsubst_lsubst_aux2; try omega; eauto 2 with slow.
        }

      * apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
        introv i.
        rw <- map_combine_left in i.
        rw in_map_iff in i; exrepnd; cpx; allsimpl.
        destruct a1 as [l1 t1].
        destruct a0 as [l2 t2]; allsimpl.

        pose proof (aeq (lsubst_bterm_aux (bterm l2 t2) [(v,mk_utoken a)]) (bterm l1 t1)) as h.
        autodimp h hyp.
        { rw <- map_combine_left.
          rw in_map_iff.
          apply in_combine_swap in i1; auto.
          eexists; dands; eauto. }

        allsimpl.
        applydup in_combine in i1; repnd.
        apply alphaeq_bterm3_if
        with (lva := v
                       :: all_vars (subst_utokens_aux t1 [(a, mk_var v)])
                       ++ all_vars t2
                       ++ bound_vars (lsubst t2 [(v, mk_utoken a)])
             )
          in h.

        inversion h as [? ? ? ? ? disj len1 len2 norep al]; subst; clear h.
        allrw disjoint_app_r; allrw disjoint_cons_r; allrw disjoint_app_r; repnd.

        apply (al_bterm _ _ lv); allrw disjoint_app_r; dands; try omega; eauto with slow.

        assert (!LIn v l1) as ni.
        { intro k; destruct ni2.
          rw lin_flat_map; eexists; dands; eauto.
          simpl; rw in_app_iff; sp. }

        rw @lsubst_subst_utokens_aux_disj; simpl;
        allrw @dom_sub_var_ren;
        allrw @sub_free_vars_var_ren;
        allrw @get_utokens_sub_var_ren;
        allrw disjoint_singleton_l;
        try omega; eauto with slow.

        pose proof (ind t1 (lsubst t1 (var_ren l1 lv)) l1) as h; clear ind.
        repeat (autodimp h hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }
        pose proof (h (lsubst t2 (var_ren l2 lv)) v a) as k; clear h.
        repeat (autodimp k hyp).

        { intro k.
          apply get_utokens_lsubst in k.
          rw @get_utokens_sub_allvars_sub in k; eauto with slow.
          allrw in_app_iff; allsimpl; repndors; tcsp.
          destruct ni1; rw lin_flat_map; eexists; dands; eauto. }

        { rw @boundvars_lsubst_vars; auto; try omega.
          intro k; destruct ni2; rw lin_flat_map; eexists; dands; eauto; simpl.
          rw in_app_iff; sp. }

        { apply alpha_eq_if3 in al.
          boolvar.

          - allrw @lsubst_aux_nil.
            pose proof (simple_lsubst_lsubst_sub_aeq3
                          t2 (var_ren l2 lv) [(v, mk_utoken a)]) as h.
            repeat (autodimp h hyp); simpl; eauto 2 with slow.
            allsimpl; rw @dom_sub_var_ren in h; auto; boolvar; tcsp.
            allrw @lsubst_nil.
            repeat (rw <- @lsubst_lsubst_aux2 in al; try omega; eauto 2 with slow).
            rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
            rw @lsubst_sub_trivial in h; simpl;
            try (rw @sub_free_vars_var_ren); try (rw disjoint_singleton_r);
            eauto with slow.

          - rw <- (lsubst_lsubst_aux2 t1) in al; try omega; eauto 2 with slow.
            eapply alpha_eq_trans;[|exact al].
            rw <- (cl_lsubst_lsubst_aux t2); eauto 2 with slow.
            rw <- (cl_lsubst_lsubst_aux (lsubst t2 (var_ren l2 lv))); eauto 2 with slow.
            pose proof (simple_lsubst_lsubst_sub_aeq3
                          t2 (var_ren l2 lv) [(v, mk_utoken a)]) as h.
            repeat (autodimp h hyp); simpl; eauto 2 with slow.
            allsimpl; rw @dom_sub_var_ren in h; auto; boolvar; tcsp.
            eapply alpha_eq_trans;[apply alpha_eq_sym; apply h|].
            rw @lsubst_sub_trivial; simpl;
            try (rw @sub_free_vars_var_ren); try (rw disjoint_singleton_r);
            eauto 2 with slow.
            rw <- @lsubst_lsubst_aux2; try omega; eauto 2 with slow.
        }
Qed.

Lemma simple_alphaeq_subst_utokens_subst {o} :
  forall (t : @NTerm o) v a,
    !LIn a (get_utokens t)
    -> alpha_eq (subst_utokens (subst t v (mk_utoken a)) [(a, mk_var v)]) t.
Proof.
  introv ni.
  unfsubst.
  pose proof (unfold_subst_utokens [(a,mk_var v)] (lsubst_aux t [(v,mk_utoken a)])) as h.
  exrepnd; rw h0; allsimpl; allrw disjoint_singleton_r.
  apply simple_alphaeq_subst_utokens_aux_lsubst_aux; auto.
Qed.

Lemma cl_subst_swap {o} :
  forall (t : @NTerm o) v1 v2 u1 u2,
    closed u1
    -> closed u2
    -> v1 <> v2
    -> subst (subst t v1 u1) v2 u2 = subst (subst t v2 u2) v1 u1.
Proof.
  introv cl1 cl2 d.
  unfold subst.
  apply substitution3.cl_lsubst_swap; simpl; eauto with slow.
Qed.

Definition is_utok {o} (t : @NTerm o) :=
  match t with
    | oterm (Can (NUTok _)) [] => True
    | _ => False
  end.

Lemma is_utok_implies {o} :
  forall t : @NTerm o,
    is_utok t -> {a : get_patom_set o & t = mk_utoken a}.
Proof.
  introv i.
  destruct t as [v|op bs]; allsimpl; tcsp.
  destruct op as [c|nc|e|a]; allsimpl; tcsp.
  destruct c; allsimpl; tcsp.
  destruct bs; allsimpl; tcsp.
  exists g; sp.
Qed.

(*
Inductive nr_ut_sub {o} : @Sub o -> Type :=
| nr_ut_sub_nil : nr_ut_sub []
| nr_ut_sub_cons :
    forall v a s,
      !LIn a (get_utokens_sub s)
      -> nr_ut_sub s
      -> nr_ut_sub ((v,mk_utoken a) :: s).
*)

Inductive nr_ut_sub {o} lib : @NTerm o -> @Sub o -> Type :=
| nr_ut_sub_nil : forall t, nr_ut_sub lib t []
| nr_ut_sub_cons :
    forall v a s t,
      (LIn v (free_vars t) -> !LIn a (get_utokens_lib lib t))
      -> nr_ut_sub lib (subst t v (mk_utoken a)) s
      -> nr_ut_sub lib t ((v,mk_utoken a) :: s).
Hint Constructors nr_ut_sub.

Lemma nr_ut_sub_cons_iff {o} :
  forall lib v t (s : @Sub o) u,
    nr_ut_sub lib u ((v,t) :: s)
    <=> {a : get_patom_set o
         & t = mk_utoken a
         # (LIn v (free_vars u) -> !LIn a (get_utokens_lib lib u))
         # nr_ut_sub lib (subst u v (mk_utoken a)) s}.
Proof.
  introv; split; intro k; exrepnd; subst; auto.
  inversion k; subst; eexists; dands; eauto.
Qed.

Lemma cl_nr_ut_sub {o} :
  forall lib (sub : @Sub o) u,
    nr_ut_sub lib u sub
    -> cl_sub sub.
Proof.
  induction sub; introv nrut; eauto with slow.
  destruct a; allrw @cl_sub_cons.
  apply nr_ut_sub_cons_iff in nrut; exrepnd; subst.
  dands; eauto with slow.
Qed.
Hint Resolve cl_nr_ut_sub : slow.

Lemma in_nr_ut_sub {o} :
  forall lib (s : @Sub o) v t u,
    LIn (v,t) s
    -> nr_ut_sub lib u s
    -> {a : get_patom_set o & t = mk_utoken a}.
Proof.
  induction s; introv i nr; allsimpl; tcsp.
  destruct a; allrw @nr_ut_sub_cons_iff; exrepnd.
  repndors; cpx; subst; tcsp.
  - eexists; dands; eauto.
  - eapply IHs; eauto.
Qed.

Lemma sub_find_some_eq_doms_nr_ut_sub {o} :
  forall lib (sub1 sub2 : @Sub o) v u,
    nr_ut_sub lib u sub2
    -> dom_sub sub1 = dom_sub sub2
    -> match sub_find sub1 v with
         | Some _ => {a : get_patom_set o & sub_find sub2 v = Some (mk_utoken a)}
         | None => sub_find sub2 v = None
       end.
Proof.
  induction sub1; destruct sub2; introv nr eqdoms; allsimpl; tcsp.
  destruct a, p; allsimpl; cpx.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar; allsimpl; tcsp.
  - eexists; dands; eauto.
  - pose proof (IHsub1 sub2 v (subst u n1 (mk_utoken a))) as h; sp.
Qed.

Lemma lsubst_aux_utoken_eq_utoken_implies_or {o} :
  forall (t : @NTerm o) a sub,
    lsubst_aux t sub = mk_utoken a
    -> ({v : NVar & sub_find sub v = Some (mk_utoken a) # t = mk_var v}
        [+] t = mk_utoken a).
Proof.
  destruct t as [v|op bs ind]; introv e; allsimpl; GC; ginv.
  - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; subst; ginv.
    left; exists v; auto.
  - inversion e; subst.
    destruct bs; allsimpl; cpx.
Qed.

Lemma lsubst_aux_pk2term_eq_utoken_implies_or {o} :
  forall (t : @NTerm o) pk sub,
    lsubst_aux t sub = pk2term pk
    -> ({v : NVar & sub_find sub v = Some (pk2term pk) # t = mk_var v}
        [+] t = pk2term pk).
Proof.
  destruct t as [v|op bs ind]; introv e; allsimpl; GC; ginv.
  - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; subst; ginv.
    left; exists v; auto.
  - allrw @pk2term_eq; inversion e; subst.
    destruct bs; allsimpl; cpx; GC.
Qed.

Lemma get_utokens_lib_subst {o} :
  forall lib (t : @NTerm o) v u,
    eqset (get_utokens_lib lib (subst t v u))
          (get_utokens_lib lib t ++ (if memvar v (free_vars t) then get_utokens u else [])).
Proof.
  introv; unfold get_utokens_lib; introv; split; introv h; allrw in_app_iff; repndors; tcsp.
  - apply get_utokens_subst in h; allrw in_app_iff; repndors; tcsp.
  - left; apply get_utokens_subst; allrw in_app_iff; repndors; tcsp.
  - left; apply get_utokens_subst; allrw in_app_iff; repndors; tcsp.
Qed.

Lemma get_utokens_subset_get_utokens_lib {o} :
  forall lib (t : @NTerm o),
    subset (get_utokens t) (get_utokens_lib lib t).
Proof.
  introv i; unfold get_utokens_lib; apply in_app_iff; tcsp.
Qed.

Lemma in_get_utokens_implies_in_get_utokens_lib {o} :
  forall lib (t : @NTerm o) v,
    LIn v (get_utokens t) -> LIn v (get_utokens_lib lib t).
Proof.
  introv i; apply get_utokens_subset_get_utokens_lib; auto.
Qed.
Hint Resolve in_get_utokens_implies_in_get_utokens_lib : slow.

Lemma nr_ut_sub_in_false {o} :
  forall lib (sub : @Sub o) v a u,
    nr_ut_sub lib u sub
    -> sub_find sub v = Some (mk_utoken a)
    -> LIn a (get_utokens_lib lib u)
    -> LIn v (free_vars u)
    -> False.
Proof.
  induction sub; introv nr sf ia iv; allsimpl; ginv.
  destruct a; allsimpl.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar; tcsp.
  - autodimp nr2 hyp; ginv; tcsp.
  - pose proof (IHsub v a0 (subst u n (mk_utoken a))) as h.
    repeat (autodimp h hyp).
    + apply get_utokens_lib_subst; rw in_app_iff; sp.
    + pose proof (eqvars_free_vars_disjoint u [(n,mk_utoken a)]) as h.
      rw eqvars_prop in h; apply h; clear h; simpl.
      rw in_app_iff; left.
      rw in_remove_nvars; simpl; sp.
Qed.

Lemma nr_ut_sub_some_eq {o} :
  forall lib (sub : @Sub o) v1 v2 a u,
    nr_ut_sub lib u sub
    -> sub_find sub v1 = Some (mk_utoken a)
    -> sub_find sub v2 = Some (mk_utoken a)
    -> LIn v1 (free_vars u)
    -> LIn v2 (free_vars u)
    -> v1 = v2.
Proof.
  induction sub; introv nrut sf1 sf2 i1 i2; allsimpl; tcsp.
  destruct a.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst; allsimpl.
  boolvar; ginv; tcsp; GC.

  - provefalse.
    autodimp nrut2 hyp.
    eapply nr_ut_sub_in_false in nrut0; eauto.
    + apply get_utokens_lib_subst; rw in_app_iff; boolvar; tcsp.
    + pose proof (eqvars_free_vars_disjoint u [(v2,mk_utoken a0)]) as h.
      rw eqvars_prop in h; apply h; clear h; simpl.
      rw in_app_iff; left.
      rw in_remove_nvars; simpl; sp.

  - provefalse.
    autodimp nrut2 hyp.
    eapply nr_ut_sub_in_false in nrut0; eauto.
    + apply get_utokens_lib_subst; rw in_app_iff; boolvar; tcsp.
    + pose proof (eqvars_free_vars_disjoint u [(v1,mk_utoken a0)]) as h.
      rw eqvars_prop in h; apply h; clear h; simpl.
      rw in_app_iff; left.
      rw in_remove_nvars; simpl; sp.

  - eapply IHsub; eauto.
    + pose proof (eqvars_free_vars_disjoint u [(n,mk_utoken a)]) as h.
      rw eqvars_prop in h; apply h; clear h; simpl.
      rw in_app_iff; left.
      rw in_remove_nvars; simpl; sp.
    + pose proof (eqvars_free_vars_disjoint u [(n,mk_utoken a)]) as h.
      rw eqvars_prop in h; apply h; clear h; simpl.
      rw in_app_iff; left.
      rw in_remove_nvars; simpl; sp.
Qed.


Lemma nr_ut_sub_some_diff2 {o} :
  forall lib (sub : @Sub o) v1 v2 a1 a2 u,
    nr_ut_sub lib u sub
    -> sub_find sub v1 = Some (mk_utoken a1)
    -> sub_find sub v2 = Some (mk_utoken a2)
    -> LIn v1 (free_vars u)
    -> LIn v2 (free_vars u)
    -> v1 <> v2
    -> a1 <> a2.
Proof.
  introv nrut e1 e2 i1 i2 d e; subst.
  pose proof (nr_ut_sub_some_eq lib sub v1 v2 a2 u); sp.
Qed.

Lemma nr_ut_sub_some_diff {o} :
  forall lib (sub : @Sub o) v1 v2 a1 a2 u,
    nr_ut_sub lib u sub
    -> sub_find sub v1 = Some (mk_utoken a1)
    -> sub_find sub v2 = Some (mk_utoken a2)
    -> a1 <> a2
    -> v1 <> v2.
Proof.
  induction sub; introv nrut e1 e2 d; allsimpl; tcsp.
  destruct a; allsimpl.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar; tcsp; ginv; tcsp.
  eapply IHsub; eauto.
Qed.

Lemma isnoncan_like_lsubst_aux_nr_ut_implies {o} :
  forall lib (t : @NTerm o) sub u,
    nr_ut_sub lib u sub
    -> isnoncan_like (lsubst_aux t sub)
    -> isnoncan_like t.
Proof.
  introv nrut isn.
  destruct t as [v|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; tcsp.
  apply sub_find_some in Heqsf.
  eapply in_nr_ut_sub in Heqsf; eauto.
  exrepnd; subst; inversion isn; sp.
Qed.

Lemma lsubst_sub_nr_ut_sub {o} :
  forall lib (sub1 sub2 : @Sub o) u,
    nr_ut_sub lib u sub1
    -> lsubst_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv nrut; allsimpl; auto.
  destruct a.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  erewrite IHsub1; eauto.
Qed.

(*
Lemma nr_ut_sub_sub_filter {o} :
  forall (sub : @Sub o) vs u,
    nr_ut_sub u sub
    -> nr_ut_sub u (sub_filter sub vs).
Proof.
  induction sub; introv nrut; allsimpl; auto.
  destruct a.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar; tcsp.
  apply IHsub.
  apply nr_ut_sub_cons_iff; eexists; dands; eauto.
  intro k; apply get_utokens_sub_filter_subset in k; sp.
Qed.
Hint Resolve nr_ut_sub_sub_filter : slow.
*)

Lemma isexc_lsubst_aux_nr_ut_sub {o} :
  forall lib (t : @NTerm o) sub u,
    nr_ut_sub lib u sub
    -> isexc (lsubst_aux t sub)
    -> isexc t.
Proof.
  destruct t as [v|op bs]; introv nrut ise; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
  apply sub_find_some in Heqsf.
  eapply in_nr_ut_sub in Heqsf; eauto; exrepnd; subst; allsimpl; tcsp.
Qed.

Lemma isvalue_like_lsubst_aux_implies {o} :
  forall (t : @NTerm o) sub,
    isvalue_like (lsubst_aux t sub)
    -> (isvalue_like t
        [+] {u : NTerm
             & {v : NVar
             & sub_find sub v = Some u
             # t = mk_var v
             # isvalue_like u}}).
Proof.
  introv isv.
  destruct t as [v|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf.
  + right.
    exists n v; sp.
  + unfold isvalue_like in isv; allsimpl; sp.
Qed.

Lemma simple_size_lsubst {o} :
  forall (t : @NTerm o) sub,
    shallow_sub sub
    -> size (lsubst t sub) = size t.
Proof.
  introv sh.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  rw @simple_size_lsubst_aux; auto.
  apply alpha_eq_preserves_size; eauto with slow.
Qed.

Lemma shallow_sub_app {o} :
  forall (sub1 sub2 : @Sub o),
    shallow_sub sub1
    -> shallow_sub sub2
    -> shallow_sub (sub1 ++ sub2).
Proof.
  introv.
  unfold shallow_sub.
  introv h1 h2 i.
  allrw @range_app; allrw in_app_iff; repndors; tcsp.
Qed.
Hint Resolve shallow_sub_app : slow.

Lemma shallow_sub_nil {o} :
  @shallow_sub o [].
Proof.
  unfold shallow_sub; simpl; sp.
Qed.
Hint Resolve shallow_sub_nil : slow.

Lemma shallow_sub_cons {o} :
  forall v t (sub : @Sub o),
    shallow_sub ((v,t) :: sub)
    <=> (size t = 1 # shallow_sub sub).
Proof.
  introv; split; introv k; repnd.
  - unfold shallow_sub in k; allsimpl.
    pose proof (k t) as h; autodimp h hyp; dands; auto.
    introv j; eapply k; eauto.
  - introv i; allsimpl; repndors; subst; tcsp.
Qed.

Lemma implies_shallow_sub_cons {o} :
  forall v t (sub : @Sub o),
    size t = 1
    -> shallow_sub sub
    -> shallow_sub ((v,t) :: sub).
Proof.
  introv e s.
  rw @shallow_sub_cons; sp.
Qed.
Hint Resolve implies_shallow_sub_cons : slow.

Lemma nr_ut_sub_is_shallow {o} :
  forall lib (sub : @Sub o) u,
    nr_ut_sub lib u sub
    -> shallow_sub sub.
Proof.
  induction sub; introv nrut; eauto with slow.
  destruct a.
  rw @nr_ut_sub_cons_iff in nrut; exrepnd; subst.
  eauto with slow.
Qed.
Hint Resolve nr_ut_sub_is_shallow : slow.

Lemma lsubst_sub_shallow_cl_sub {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub1
    -> shallow_sub sub1
    -> lsubst_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv cl sh; allsimpl; auto.
  destruct a.
  allrw @cl_sub_cons; exrepnd; subst.
  allrw @shallow_sub_cons; repnd.
  erewrite IHsub1; eauto; f_equal; f_equal.
  destruct n0 as [v|op bs]; tcsp; allsimpl; cpx.
  - unfold closed in cl0; allsimpl; ginv.
  - assert (bs = []); subst.
    { destruct bs; allsimpl; cpx.
      destruct b as [l t]; allsimpl.
      destruct t; allsimpl; cpx. }
    unfold lsubst; simpl; auto.
Qed.

Lemma get_utokens_sub_nil {o} :
  @get_utokens_sub o [] = [].
Proof. sp. Qed.
Hint Rewrite @get_utokens_sub_nil : slow.

Lemma get_utokens_sub_cons {o} :
  forall v t (sub : @Sub o),
    get_utokens_sub ((v,t) :: sub)
    = get_utokens t ++ get_utokens_sub sub.
Proof. sp. Qed.

Lemma get_utokens_sub_app {o} :
  forall (sub1 sub2 : @Sub o),
    get_utokens_sub (sub1 ++ sub2)
    = get_utokens_sub sub1 ++ get_utokens_sub sub2.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; allsimpl.
  allrw @get_utokens_sub_cons; rw IHsub1.
  rw app_assoc; auto.
Qed.

(*
Lemma implies_nr_ut_sub_app {o} :
  forall (sub1 sub2 : @Sub o),
    disjoint (get_utokens_sub sub1) (get_utokens_sub sub2)
    -> nr_ut_sub sub1
    -> nr_ut_sub sub2
    -> nr_ut_sub (sub1 ++ sub2).
Proof.
  induction sub1; introv d n1 n2; allsimpl; eauto with slow.
  destruct a; allsimpl.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst; allsimpl.
  exists a; dands; tcsp.
  - intro i.
    rw @get_utokens_sub_app in i; allrw in_app_iff.
    allrw @get_utokens_sub_cons; allsimpl; allrw disjoint_cons_l; repnd.
    repndors; tcsp.
  - allrw @get_utokens_sub_cons; allsimpl; allrw disjoint_cons_l; repnd.
    apply IHsub1; auto.
Qed.
Hint Resolve implies_nr_ut_sub_app : slow.
*)

Lemma subset_eqset_l :
  forall (T : tuniv) (s1 s2 s3 : list T),
    eqset s1 s2 -> subset s1 s3 -> subset s2 s3.
Proof.
  introv eqs ss i; apply eqset_sym in eqs; apply eqs in i; apply ss in i; auto.
Qed.

Lemma subset_get_utokens_implies_subset_get_utokens_lib {o} :
  forall lib (t u : @NTerm o),
    subset (get_utokens t) (get_utokens u)
    -> subset (get_utokens_lib lib t) (get_utokens_lib lib u).
Proof.
  introv ss i; allunfold @get_utokens_lib; allrw in_app_iff; repndors; tcsp.
Qed.

Lemma nr_ut_sub_change_term {o} :
  forall lib sub (t u : @NTerm o),
    subvars (free_vars t) (free_vars u)
    -> subset (get_utokens t) (get_utokens u)
    -> nr_ut_sub lib u sub
    -> nr_ut_sub lib t sub.
Proof.
  induction sub; introv sv ss nrut; tcsp.
  destruct a; allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  exists a; dands; auto.
  - intro i.
    rw subvars_prop in sv; apply sv in i; apply nrut2 in i.
    apply (subset_get_utokens_implies_subset_get_utokens_lib lib) in ss.
    intro k; apply ss in k; sp.
  - apply (IHsub _ (subst u n (mk_utoken a))); auto.
    + repeat unfsubst; repeat (rw @free_vars_lsubst_aux_cl; eauto with slow); simpl.
      apply subars_remove_nvars_lr; auto.
    + eapply subset_eqset_r;[apply eqset_sym; apply get_utokens_subst|].
      eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_subst|].
      boolvar; allsimpl; allrw app_nil_r; tcsp; eauto with slow.
      rw subvars_prop in sv; apply sv in Heqb; sp.
Qed.
Hint Resolve nr_ut_sub_change_term : slow.

Lemma shallow_sub_sub_filter {o} :
  forall (sub : @Sub o) vs,
    shallow_sub sub
    -> shallow_sub (sub_filter sub vs).
Proof.
  induction sub; introv sh; allsimpl; tcsp.
  destruct a; allrw @shallow_sub_cons; repnd.
  boolvar; tcsp.
  apply shallow_sub_cons; sp.
Qed.
Hint Resolve shallow_sub_sub_filter : slow.

Lemma in_cl_sub {o} :
  forall (sub : @Sub o) v t,
  cl_sub sub
  -> LIn (v, t) sub
  -> closed t.
Proof.
  introv cl i.
  rw @cl_sub_eq2 in cl; eapply cl; eauto.
Qed.

Lemma nr_ut_sub_sub_filter_disj {o} :
  forall lib (sub : @Sub o) vs u,
    disjoint vs (free_vars u)
    -> nr_ut_sub lib u sub
    -> nr_ut_sub lib u (sub_filter sub vs).
Proof.
  induction sub; introv d nrut; allsimpl; auto.
  destruct a.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar; tcsp.
  - apply IHsub; auto.
    rw @cl_subst_trivial in nrut0; eauto with slow.
  - apply nr_ut_sub_cons_iff; eexists; dands; eauto.
    apply IHsub; auto.
    unfsubst.
    rw @free_vars_lsubst_aux_cl; eauto with slow.
Qed.
Hint Resolve nr_ut_sub_sub_filter_disj : slow.

Lemma implies_nr_ut_sub_app {o} :
  forall lib (sub1 sub2 : @Sub o) t,
    nr_ut_sub lib t sub1
    -> nr_ut_sub lib (lsubst t sub1) sub2
    -> nr_ut_sub lib t (sub1 ++ sub2).
Proof.
  induction sub1; introv n1 n2; allsimpl; eauto with slow.
  - allrw @lsubst_nil; auto.
  - destruct a; allsimpl.
    allrw @nr_ut_sub_cons_iff; exrepnd; subst; allsimpl.
    exists a; dands; tcsp.
    apply IHsub1; auto.
    unfold subst.
    rw <- @cl_lsubst_app; eauto with slow.
Qed.
Hint Resolve implies_nr_ut_sub_app : slow.

Lemma nr_ut_sub_sub_filter_change_term_disj {o} :
  forall lib sub (t u : @NTerm o) vs,
    disjoint vs (free_vars u)
    -> subvars (free_vars t) (free_vars u ++ vs)
    -> subset (get_utokens t) (get_utokens u)
    -> nr_ut_sub lib u sub
    -> nr_ut_sub lib t (sub_filter sub vs).
Proof.
  induction sub; introv d sv ss nrut; tcsp.
  destruct a; allsimpl.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst.
  boolvar.
  - eapply IHsub; eauto.
    apply d in Heqb.
    unfsubst in nrut0.
    rw @lsubst_aux_trivial_cl_term in nrut0; simpl; eauto with slow.
    apply disjoint_singleton_r; auto.
  - rw @nr_ut_sub_cons_iff; exists a; dands; eauto with slow.
    + intro i.
      rw subvars_prop in sv; apply sv in i; tcsp.
      allrw in_app_iff; repndors; tcsp.
    + apply (IHsub _ (subst u n (mk_utoken a))); auto.
      * repeat unfsubst; repeat (rw @free_vars_lsubst_aux_cl; eauto with slow); simpl.
      * repeat unfsubst; repeat (rw @free_vars_lsubst_aux_cl; eauto with slow); simpl.
        allrw subvars_prop; introv i; allrw in_remove_nvars; allsimpl; allrw not_over_or; repnd.
        apply sv in i0; allrw in_app_iff; allrw in_remove_nvars; allsimpl; repndors; tcsp.
        left; sp.
      * eapply subset_eqset_r;[apply eqset_sym; apply get_utokens_subst|].
        eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_subst|].
        boolvar; allsimpl; allrw app_nil_r; tcsp; eauto with slow.
        provefalse.
        rw subvars_prop in sv; apply sv in Heqb0; sp.
        allrw in_app_iff; sp.
Qed.

Lemma get_utokens_sub_sub_keep_first {o} :
  forall (sub : @Sub o) l,
    subset (get_utokens_sub (sub_keep_first sub l)) (get_utokens_sub sub).
Proof.
  unfold get_utokens_sub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  allrw @in_range_iff; exrepnd.
  allrw @in_sub_keep_first; repnd.
  apply sub_find_some in i1; eexists; eauto.
Qed.

Lemma implies_subvars_cons_l :
  forall (v : NVar) (vs1 vs2 : list NVar),
    LIn v vs2
    -> subvars vs1 vs2
    -> subvars (v :: vs1) vs2.
Proof.
  introv i sv.
  rw subvars_cons_l; dands; auto.
Qed.
Hint Resolve implies_subvars_cons_l : slow.

Lemma in_get_utokens_sub {o} :
  forall (sub : @Sub o) a,
    LIn a (get_utokens_sub sub)
    <=> {v : NVar & {t : NTerm & LIn (v,t) sub # LIn a (get_utokens t)}}.
Proof.
  induction sub; introv.
  - rw @get_utokens_sub_nil; simpl; split; introv k; tcsp.
  - destruct a; rw @get_utokens_sub_cons; rw in_app_iff; simpl.
    rw IHsub; clear IHsub; split; intro k; repndors; exrepnd; subst.
    + exists n n0; tcsp.
    + exists v t; tcsp.
    + repndors; cpx; tcsp.
      right; exists v t; tcsp.
Qed.

Lemma alpha_eq_option_refl {o} :
  forall (op : option (@NTerm o)),
    alpha_eq_option op op.
Proof.
  introv.
  destruct op; simpl; auto.
Qed.
Hint Resolve alpha_eq_option_refl : slow.

Lemma cl_lsubst_pushdown_fresh {o} :
  forall (t : @NTerm o) v sub,
    cl_sub sub
    -> isvalue_like t
    -> alpha_eq
         (lsubst (pushdown_fresh v t) sub)
         (pushdown_fresh v (lsubst t (sub_filter sub [v]))).
Proof.
  introv cl isv.
  repeat unflsubst.
  destruct t as [x|op bs]; simpl; tcsp.

  - unfold isvalue_like in isv; allsimpl; sp.

  - f_equal.
    unfold mk_fresh_bterms.
    allrw map_map; unfold compose.
    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; cpx.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl; fold_terms.
    unfold maybe_new_var; boolvar.

    + apply alpha_eq_bterm_congr.

      pose proof (ex_fresh_var
                    (all_vars (lsubst_aux t (sub_filter (sub_filter sub l) [newvar t]))
                              ++ all_vars (lsubst_aux t (sub_filter (sub_filter sub [v]) l)))
                 ) as h; exrepnd.
      apply (implies_alpha_eq_mk_fresh_sub v0); auto.
      allrw in_app_iff; allrw not_over_or; repnd.

      pose proof (lsubst_trivial4
                    (lsubst_aux t (sub_filter (sub_filter sub l) [newvar t]))
                    (var_ren [newvar t] [v0])) as k1.
      repeat (autodimp k1 hyp).
      { rw @dom_sub_var_ren; simpl; auto.
        apply disjoint_singleton_l; auto.
        rw @free_vars_lsubst_aux_cl; eauto with slow.
        allrw <- @dom_sub_sub_filter.
        allrw in_remove_nvars.
        intro k; repnd.
        apply newvar_prop in k0; sp. }
      { simpl; introv i; repndors; cpx.
        simpl.
        apply disjoint_singleton_l; auto. }

      pose proof (lsubst_trivial4
                    (lsubst_aux t (sub_filter (sub_filter sub [v]) l))
                    (var_ren [newvar (lsubst_aux t (sub_filter (sub_filter sub [v]) l))] [v0])) as k2.
      repeat (autodimp k2 hyp).
      { rw @dom_sub_var_ren; simpl; auto.
        apply disjoint_singleton_l; auto.
        apply newvar_prop. }
      { simpl; introv i; repndors; cpx.
        simpl.
        apply disjoint_singleton_l; auto. }

      rw k1; rw k2; clear k1 k2.

      apply alpha_eq_lsubst_aux_if_ext_eq; auto;
      try (rw @sub_free_vars_if_cl_sub; eauto with slow).

      allrw <- @sub_filter_app_r.
      unfold ext_alpha_eq_subs; introv i.
      allrw @sub_find_sub_filter_eq.
      allrw memvar_app; allrw memvar_singleton.
      boolvar; simpl; tcsp; eauto with slow.
      apply newvar_prop in i; sp.

    + rw @sub_filter_swap; auto.
Qed.

Lemma alpha_eq_mk_atom_eq_lsubst {o} :
  forall (a b c d : @NTerm o) sub,
    alpha_eq (lsubst (mk_atom_eq a b c d) sub)
             (mk_atom_eq (lsubst a sub) (lsubst b sub) (lsubst c sub) (lsubst d sub)).
Proof.
  introv.
  pose proof (unfold_lsubst sub a) as ha; exrepnd; rw ha0.
  pose proof (unfold_lsubst sub b) as hb; exrepnd; rw hb0.
  pose proof (unfold_lsubst sub c) as hc; exrepnd; rw hc0.
  pose proof (unfold_lsubst sub d) as hd; exrepnd; rw hd0.
  unfold lsubst; simpl.
  allrw @var_ren_nil_l.
  allrw @sub_filter_nil_r.
  allrw app_nil_r.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @lsubst_aux_nil.
  boolvar; unfold mk_atom_eq, nobnd.
  - allrw disjoint_app_l; repnd.
    apply implies_alpha_eq_mk_atom_eq;
      apply lsubst_aux_alpha_congr_same_disj;
      auto.
  - apply implies_alpha_eq_mk_atom_eq; auto;
    t_change u;
    apply lsubst_aux_alpha_congr_same_disj;
    eauto with slow.
Qed.

Lemma alpha_eq_mk_exception_lsubst {o} :
  forall (a b : @NTerm o) sub,
    alpha_eq (lsubst (mk_exception a b) sub)
             (mk_exception (lsubst a sub) (lsubst b sub)).
Proof.
  introv.
  pose proof (unfold_lsubst sub a) as ha; exrepnd; rw ha0.
  pose proof (unfold_lsubst sub b) as hb; exrepnd; rw hb0.
  unfold lsubst; simpl.
  allrw @var_ren_nil_l.
  allrw @sub_filter_nil_r.
  allrw app_nil_r.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @lsubst_aux_nil.
  boolvar; unfold mk_atom_eq, nobnd.
  - allrw disjoint_app_l; repnd.
    apply implies_alphaeq_exception;
      apply lsubst_aux_alpha_congr_same_disj;
      auto.
  - apply implies_alphaeq_exception; auto;
    t_change u;
    apply lsubst_aux_alpha_congr_same_disj;
    eauto with slow.
Qed.

Lemma nr_ut_some_implies {o} :
  forall lib (sub : @Sub o) v t u,
    nr_ut_sub lib u sub
    -> sub_find sub v = Some t
    -> {a : get_patom_set o & t = mk_utoken a}.
Proof.
  induction sub; introv nrut sf; allsimpl; ginv.
  destruct a as [x z].
  inversion nrut as [|? ? ? ? imp nrut1]; subst; clear nrut.
  boolvar; ginv.
  - eexists; dands; eauto.
  - eapply IHsub in sf; eauto.
Qed.

Lemma lsubst_aux_pk2term {o} :
  forall (pk : @param_kind o) sub,
    lsubst_aux (pk2term pk) sub = pk2term pk.
Proof.
  introv; destruct pk; simpl; auto.
Qed.

Hint Resolve covered_sub_nil : slow.

Lemma nt_wf_oterm_fst {o} :
  forall op (t : @NTerm o) vs bs,
    nt_wf (oterm op (bterm vs t :: bs)) -> nt_wf t.
Proof.
  introv w.
  allrw @nt_wf_oterm_iff; repnd; allsimpl.
  pose proof (w (bterm vs t)) as w1; autodimp w1 hyp.
  allrw @bt_wf_iff; auto.
Qed.
