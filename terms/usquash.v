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


Require Export psquash.


Definition mk_usquash_per {o} v1 v2 (t : @NTerm o) :=
  mk_lam v1 (mk_lam v2 t).

Definition mk_usquash {o} (t : @NTerm o) :=
  match newvars2 [t] with
    | (v1,v2) => mk_pertype (mk_usquash_per v1 v2 t)
  end.

Definition mkc_usquash_per {o} v1 v2 (t : @CTerm o) :=
  mkc_lam v1 (mkcv_lam _ v2 (mk_cv _ t)).

Lemma wf_mk_usquash {o} :
  forall (t : @NTerm o),
    wf_term (mk_usquash t) <=> wf_term t.
Proof.
  introv.
  unfold mk_usquash.
  remember (newvars2 [t]) as v; destruct v.
  rw <- @wf_pertype_iff.
  unfold mk_usquash_per.
  allrw <- @wf_lam_iff; tcsp.
Qed.

Lemma cover_vars_usquash {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_usquash t) s <=> cover_vars t s.
Proof.
  introv.
  unfold mk_usquash.
  remember (newvars2 [t]) as v; destruct v.
  rw @cover_vars_pertype.
  unfold mk_usquash_per.
  rw @cover_vars_lam.
  rw @cover_vars_upto_lam.

  allrw <- @csub_filter_app_r; simpl.
  apply newvars2_prop2 in Heqv; allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cover_vars_upto_csub_filter_disjoint
                t s [n, n0] [n, n0]) as h1.
  allrw disjoint_cons_r.
  repeat (autodimp h1 hyp); allsimpl; tcsp.
  pose proof (cover_vars_upto_eqvars
                t (csub_filter s [n, n0])
                [n,n0] [n0,n]) as e1.
  autodimp e1 hyp.
  { rw eqvars_prop; simpl; introv; split; sp. }
  rw <- e1; rw h1; clear h1 e1.

  split; intro k; repnd; dands; tcsp.
Qed.


Lemma lsubstc_mk_usquash_ex {o} :
  forall (t : @NTerm o) w s c,
    {w' : wf_term t
     & {c' : cover_vars t s
     & alphaeqc
         (lsubstc (mk_usquash t) w s c)
         (mkc_pertype (mkc_usquash_per nvarx nvary (lsubstc t w' s c')))}}.
Proof.
  introv.

  dup w as w'.
  rw @wf_mk_usquash in w'.
  exists w'.

  dup c as c'.
  rw @cover_vars_usquash in c'.
  exists c'.

  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow;simpl.
  autorewrite with slow list in *.

  pose proof (newvarlst_prop [t]) as nvp1.
  remember (newvarlst [t]) as v1; clear Heqv1.
  pose proof (newvarlst_prop [t,mk_var v1]) as nvp2.
  remember (newvarlst [t, mk_var v1]) as v2; clear Heqv2.

  allsimpl; autorewrite with list in *.
  repeat (allrw in_app_iff; allsimpl).
  allrw not_over_or; repnd; GC.

  allrw <- @sub_filter_app_r; allsimpl.

  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (v1 :: v2
                               :: nvarx
                               :: nvary
                               :: (allvars_op
                                     (oterm (Can NLambda)
                                            [bterm [v2] (lsubst_aux t (sub_filter (csub2sub s) [v1, v2]))]))
                               ++ (allvars_op (oterm (Can NLambda) [bterm [nvary] (lsubst t (csub2sub s))])))) as fv.
  exrepnd; allsimpl.
  rw in_app_iff in fv0.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v]); simpl; auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff; sp. }

  autorewrite with slow; boolvar; tcsp; GC.

  repeat (prove_alpha_eq4).
  fold_terms.

  pose proof (ex_fresh_var (v :: v1
                              :: v2
                              :: nvarx
                              :: nvary
                              :: (allvars_op (lsubst_aux (lsubst_aux t (sub_filter (csub2sub s) [v1, v2])) [(v1, mk_var v)]))
                              ++ (allvars_op (lsubst_aux (lsubst t (csub2sub s)) [(nvarx, mk_var v)])))) as fv'.
  exrepnd; allsimpl.
  rw in_app_iff in fv'0.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v0]); allsimpl; fold_terms; auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff; sp. }

  applydup @cover_vars_iff_closed_lsubst_aux in c'.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
  rw @lsubst_aux_sub_filter;[|repeat (rw disjoint_cons_r); dands; complete auto].
  repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto;[]).
  rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto.
Qed.

Definition mkc_usquash {o} (t : @CTerm o) :=
  mkc_pertype (mkc_usquash_per nvarx nvary t).

Lemma lsubstc_mk_usquash_ex2 {o} :
  forall (t : @NTerm o) w s c,
    {w' : wf_term t
     & {c' : cover_vars t s
     & alphaeqc (lsubstc (mk_usquash t) w s c)
                (mkc_usquash (lsubstc t w' s c')) }}.
Proof.
  introv.
  apply lsubstc_mk_usquash_ex.
Qed.
