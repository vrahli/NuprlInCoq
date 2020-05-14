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


Require Export csubst_ref.
Require Export approx_star_props2.
Require Export computation6.
Require Export computation_choice_seq.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(* begin hide *)

Lemma range_utok_ren_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> length sub1 = length sub2
    -> range_utok_ren (nrut_subs_to_utok_ren sub1 sub2)
       = get_utokens_sub sub2.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 len; simphyps; tcsp.
  destruct a as [v1 t1]; destruct p as [v2 t2].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx.
  allrw @get_utokens_sub_cons; allsimpl.
  erewrite IHsub1; eauto.
Qed.

Lemma dom_utok_ren_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> length sub1 = length sub2
    -> dom_utok_ren (nrut_subs_to_utok_ren sub1 sub2)
       = get_utokens_sub sub1.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 len; simphyps; tcsp.
  destruct a as [v1 t1]; destruct p as [v2 t2].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx.
  allrw @get_utokens_sub_cons; allsimpl.
  erewrite IHsub1; eauto.
Qed.

Lemma approx_star_change_nrut_sub {o} :
  forall lib (t1 t2 : @NTerm o) sub l sub' l',
    nrut_sub l sub
    -> nrut_sub l' sub'
    -> dom_sub sub = dom_sub sub'
    -> subset (get_utokens_library lib) l
    -> subset (get_utokens_library lib) l'
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> subset (get_utokens t1) l'
    -> subset (get_utokens t2) l'
    -> approx_star lib (lsubst t1 sub) (lsubst t2 sub)
    -> approx_star lib (lsubst t1 sub') (lsubst t2 sub').
Proof.
  introv nrut1 nrut2 eqdoms ssl1 ssl2 ss1 ss2 ss3 ss4 apr.

  pose proof (length_dom sub) as len.
  rw eqdoms in len; rw @length_dom in len.

  pose proof (change_nr_ut_sub_in_lsubst_aux_approx_star
                (lsubst t1 sub) (lsubst t2 sub) lib
                (nrut_subs_to_utok_ren sub sub')) as h.
  erewrite @range_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  erewrite @dom_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  repeat (autodimp h hyp); eauto 3 with slow.

  - unfold nrut_sub in nrut1; repnd.
    eapply subset_disjoint;[|eauto]; auto.

  - unfold nrut_sub in nrut2; repnd.
    eapply subset_disjoint;[|eauto]; auto.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lib_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss3 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

    + unfold nrut_sub in nrut2; repnd.
      apply ssl2 in j0.
      apply nrut2 in j0; tcsp.

    + apply in_get_utokens_sub in j0; exrepnd.
      apply in_sub_keep_first in j1; repnd.
      apply sub_find_some in j2.
      destruct j.
      apply in_sub_eta in j2; repnd.
      unfold get_utokens_sub; rw lin_flat_map.
      eexists; dands; eauto.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lib_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss4 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

    + unfold nrut_sub in nrut1; repnd.
      apply ssl2 in j0.
      apply nrut2 in j0; tcsp.

    + apply in_get_utokens_sub in j0; exrepnd.
      apply in_sub_keep_first in j1; repnd.
      apply sub_find_some in j2.
      destruct j.
      apply in_sub_eta in j2; repnd.
      unfold get_utokens_sub; rw lin_flat_map.
      eexists; dands; eauto.

  - assert (disjoint (get_utokens_sub sub) (get_utokens t1)) as disj1.
    { introv i j.
      apply ss1 in j; unfold nrut_sub in nrut1; repnd.
      apply nrut1 in j; sp. }

    assert (disjoint (get_utokens_sub sub) (get_utokens t2)) as disj2.
    { introv i j.
      apply ss2 in j; unfold nrut_sub in nrut1; repnd.
      apply nrut1 in j; sp. }

    repeat (rw @lsubst_ren_utokens in h).
    repeat (rw @ren_utokens_trivial in h;[|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; eauto]).
    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in h; eauto.
Qed.

Lemma alpha_eq_bterm_preserves_osize2 {p} :
  forall bt1 bt2,
    @alpha_eq_bterm p bt1 bt2
    -> osize (get_nt bt1) = osize (get_nt bt2).
Proof.
  introv Hal.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  simpl; eapply alpha_eq_bterm_preserves_osize; eauto.
Qed.

Lemma approx_star_btermd_sw {p} :
  forall lib sw bt1 bt2 lva,
    approx_star_bterm (NSwapCs2 sw) lib bt1 bt2
    -> {lvn : list NVar
        & {nt1',nt2' : @NTerm p
          $ approx_star lib (swap_cs_term sw nt1') (swap_cs_term sw nt2')
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # no_repeats lvn
          # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva } }.
Proof.
  introv Hab.
  unfold approx_star_bterm in Hab.
  repnud Hab; exrepnd.
  pose proof (alpha_bterm_pair_change _ _ _ _ _ lva Hab2 Hab0) as Hp.
  exrepnd.
  exists lvn.

  repndors; exrepnd; subst; simpl in *; tcsp; ginv;[].

  exists (lsubst nt1n (var_ren lv lvn))
         (lsubst nt2n (var_ren lv lvn)).
  repeat rewrite <- lsubst_swap_cs_term_var_ren.
  dands; eauto 3 with slow.
  { apply approx_star_lsubst_vars; auto.
    eapply approx_star_alpha_fun_l;
      try eapply approx_star_alpha_fun_r;
      try exact Hab3; eauto 3 with slow. }
  disjoint_reasoningv; spcls;
    apply disjoint_bound_vars_lsubst;
    spcls; disjoint_reasoningv.
Qed.


Hint Rewrite @minus0 : slow.
Hint Rewrite @Nat.add_0_r : slow.

Lemma push_swap_cs_sub_term_nil {o} :
  forall sw (a : @NTerm o),
    push_swap_cs_sub_term sw [] a = a.
Proof.
  introv; unfold push_swap_cs_sub_term; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @push_swap_cs_sub_term_nil : slow.

Lemma computes_to_val_like_in_max_k_steps_swap_cs2_implies {o} :
  forall lib k sw n (v : @NTerm o),
    wf_term n
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NSwapCs2 sw) [nobnd n])
         v
         k
    -> {can : CanonicalOp
       $ {bs : list BTerm
       $ {k1 : nat
       $ k1+1 <= k
       # computes_to_can_in_max_k_steps lib k1 (swap_cs_term sw n) (oterm (Can can) bs)
       # reduces_in_atmost_k_steps lib
           (oterm (NSwapCs2 sw) [nobnd n])
           (oterm (NSwapCs2 sw)
                  [nobnd (oterm (Can (swap_cs_can sw can)) (map (swap_cs_bterm sw) bs))])
           k1
       # computes_to_val_like_in_max_k_steps lib
           (push_swap_cs_can sw (swap_cs_can sw can) (map (swap_cs_bterm sw) bs))
           v
           (k - (k1 + 1))
       }}}
       [+]
       {en, e : NTerm
       $ {k1 : nat
       $ k1 + 1 <= k
       # v = mk_exception (mk_swap_cs2 sw (swap_cs_term sw en)) (mk_swap_cs2 sw (swap_cs_term sw e))
       # computes_to_exception_in_max_k_steps lib en (swap_cs_term sw n) e k1
       # reduces_in_atmost_k_steps lib
           (mk_swap_cs2 sw n)
           (mk_swap_cs2 sw (mk_exception (swap_cs_term sw en) (swap_cs_term sw e)))
           k1
       }}.
Proof.
  induction k; introv wf comp.

  - destruct comp as [r is].
    inversion r; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n; try (complete (inversion comp1));[].
    dopid o0 as [can1|ncan1|nsw1|exc1|abs1] Case.

    + Case "Can".
      csunf comp1; simpl in *; ginv.
      left.
      exists (swap_cs_can sw can1) (map (swap_cs_bterm sw) l) 0; simpl; dands; try omega;
        allrw @computes_to_can_in_max_k_steps_0;
        allrw @reduces_in_atmost_k_steps_0;
        autorewrite with slow; dands; eauto 3 with slow.

    + Case "NCan".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      applydup (@implies_wf_term_swap_cs_term o sw) in wf; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *;
        autorewrite with slow in *; eauto 3 with slow.

      * left.
        exists can bs (S k1); dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

    + Case "NSwapCs2".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      applydup (@implies_wf_term_swap_cs_term o sw) in wf; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *;
        autorewrite with slow in *; eauto 3 with slow.

      * left.
        exists can bs (S k1); dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply wf_exception_implies in wf; exrepnd; subst; simpl in *; fold_terms.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right; simpl; fold_terms; autorewrite with slow.

      exists (swap_cs_term sw a) (swap_cs_term sw t) 0; dands; autorewrite with slow; auto; try omega.
      { apply computes_to_exception_in_max_k_steps_exc; sp. }
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      applydup (@implies_wf_term_swap_cs_term o sw) in wf; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *;
        autorewrite with slow in *; eauto 3 with slow.

      * left.
        exists can bs (S k1); dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.
Qed.

Lemma compute_on_can {o} :
  forall lib (t : @NTerm o) k,
    iscan t
    -> compute_at_most_k_steps lib k t = csuccess t.
Proof.
  induction k; introv isc; simpl in *; auto.
  rewrite IHk; auto.
  apply iscan_compute_step; auto.
Qed.

Lemma reduces_to_if_can {o} :
  forall lib (t u : @NTerm o),
    reduces_to lib t u
    -> iscan t
    -> t = u.
Proof.
 unfold reduces_to, reduces_in_atmost_k_steps; introv Hc Hisv; exrepnd.
 rewrite compute_on_can in Hc0; ginv; auto.
Qed.

Lemma iscan_push_swap_cs_can {o} :
  forall sw c (bs : list (@BTerm o)),
    iscan (push_swap_cs_can sw c bs).
Proof.
  tcsp.
Qed.
Hint Resolve iscan_push_swap_cs_can : slow.

Lemma swap_cs2_computes_to_value_implies {o} :
  forall lib sw (t : @NTerm o) u,
    isprog t
    -> (mk_swap_cs2 sw t) =v>(lib) u
    -> {c : CanonicalOp & {bs : list BTerm
       & ((swap_cs_term sw t) =v>(lib) (oterm (Can c) bs))
       # u = (push_swap_cs_can sw (swap_cs_can sw c) (map (swap_cs_bterm sw) bs)) }}.
Proof.
  introv wf comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.

  pose proof (computes_to_val_like_in_max_k_steps_swap_cs2_implies lib k sw t u) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
  repndors; exrepnd; subst; simpl in *;
    allapply @isvalue_mk_exception; tcsp;[].

  exists can bs; dands; auto.
  { unfold computes_to_can_in_max_k_steps in *; repnd.
    applydup @reduces_atmost_preserves_program in q4; eauto 3 with slow. }

  unfold computes_to_val_like_in_max_k_steps in *; repnd; eauto 3 with slow.
  apply reduces_in_atmost_k_steps_implies_reduces_to in q4.
  apply reduces_to_if_can in q4; eauto 3 with slow.
Qed.

Lemma implies_isprog_vars_swap_cs_term {o} :
  forall vs sw (t : @NTerm o),
    isprog_vars vs t
    -> isprog_vars vs (swap_cs_term sw t).
Proof.
  introv isp.
  unfold isprog_vars in *; simpl in *; autorewrite with slow; repnd; dands; auto.
  eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_vars_swap_cs_term : slow.

Lemma isvalue_implies_isvalue_push_swap_cs_can {o} :
  forall sw c (bs : list (@BTerm o)),
    isvalue (oterm (Can c) bs)
    -> isvalue (push_swap_cs_can sw c bs).
Proof.
  introv isv.
  inversion isv; subst.
  constructor; simpl; auto; eauto 3 with slow.
Qed.
Hint Resolve isvalue_implies_isvalue_push_swap_cs_can : slow.

Lemma isvalue_implies_isvalue_push_swap_cs_can_swap {o} :
  forall sw c (bs : list (@BTerm o)),
    isvalue (oterm (Can c) bs)
    -> isvalue (push_swap_cs_can sw (swap_cs_can sw c) (map (swap_cs_bterm sw) bs)).
Proof.
  introv isv.
  inversion isv as [? isp]; subst.
  apply (implies_isprogram_swap_cs_term sw) in isp.
  constructor; simpl; auto; eauto 3 with slow.
Qed.
Hint Resolve isvalue_implies_isvalue_push_swap_cs_can_swap : slow.

Lemma eapply_choice_seq_computes_to_value_implies {o} :
  forall lib n (t : @NTerm o) v,
    mk_eapply (mk_choice_seq n) t =v>(lib) v
    -> {k : nat
        & {val : ChoiceSeqVal
        & computes_to_value lib t (mk_nat k)
        # find_cs_value_at lib n k = Some val
        # computes_to_value lib (CSVal2term val) v}}.
Proof.
  introv comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.
  apply reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue_like in comp1; eauto 3 with slow;[].
  repndors; exrepnd.
  { exists n0 val.
    unfold computes_to_value, reduces_to.
    dands; eauto 3 with slow. }
  { apply isvalue_implies_iscan in comp; apply iscan_implies_not_isexc in comp; tcsp. }
Qed.

Lemma is_nat_implies {o} :
  forall k (val : @ChoiceSeqVal o),
    is_nat k val
    -> {n : nat & val = mkc_nat n}.
Proof.
  introv isn.
  unfold is_nat in *.
  destruct val as [t isp].
  destruct t as [v|op bs].
  { assert False; tcsp; clear isn; apply isprog_vterm in isp; auto. }
  destruct op as [can|ncan|nsw|exc|abs]; simpl in *;
    try (complete (assert False; tcsp; exrepnd; inversion isn0)).
  destruct can; simpl in *; try (complete (assert False; tcsp; exrepnd; inversion isn0)).
  destruct bs; simpl in *; try (complete (assert False; tcsp; exrepnd; inversion isn0)).
  fold_terms.
  destruct (Z_le_gt_dec 0 z).
  { exists (Z.to_nat z).
    apply cterm_eq; simpl; unfold mk_nat.
    rewrite Z2Nat.id; auto. }
  assert False; tcsp; exrepnd; inversion isn0; subst; omega.
Qed.

Lemma is_bool_implies {o} :
  forall k (val : @ChoiceSeqVal o),
    is_bool k val
    -> {b : bool & val = mkc_boolean b}.
Proof.
  introv isn.
  unfold is_bool in *.
  destruct val as [t isp].
  destruct t as [v|op bs].
  { assert False; tcsp; clear isn; apply isprog_vterm in isp; auto. }
  destruct op as [can|ncan|nsw|exc|abs]; simpl in *;
    try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0));[].
  destruct can; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0));[].
  destruct bs; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0));[].
  destruct bs; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b1; inversion isn0));[].
  destruct b as [l t].
  destruct l; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0)).
  destruct t as [v|op bs].
  { assert False; tcsp; clear isn; apply @closed_if_isprog in isp; unfold closed in *; simpl in *; tcsp. }
  destruct op as [can|ncan|nsw|exc|abs]; simpl in *;
    try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0));[].
  destruct can; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b; inversion isn0));[].
  destruct bs; simpl in *; try (complete (assert False; tcsp; exrepnd; destruct b0; inversion isn0));[].
  destruct c.
  { exists true; apply cterm_eq; simpl; auto. }
  { exists false; apply cterm_eq; simpl; auto. }
Qed.

Lemma find_cs_value_at_if_safe_library {o} :
  forall lib name k (val : @ChoiceSeqVal o),
    safe_library lib
    -> find_cs_value_at lib name k = Some val
    -> {n : nat
        & csn_kind name = cs_info_nat
        # val = mkc_nat n}
       [+]
       {b : bool
        & csn_kind name = cs_info_bool
        # val = mkc_boolean b}.
Proof.
  introv safe fcs.
  unfold find_cs_value_at in fcs.
  remember (find_cs lib name) as q; symmetry in Heqq; destruct q; ginv.
  applydup @find_cs_some_implies_entry_in_library in Heqq as i.
  apply safe in i; simpl in *.
  destruct c as [vals restr]; simpl in *; repnd.
  rewrite find_value_of_cs_at_is_select in fcs.
  destruct name as [name kind]; simpl in *.
  unfold correct_restriction in *; simpl in *.
  destruct restr; simpl in *.
  destruct kind; simpl in *.

  { apply i in fcs; apply i0 in fcs.
    apply is_nat_implies in fcs; exrepnd; subst.
    left; eauto. }

  { apply i in fcs; apply i0 in fcs.
    apply is_bool_implies in fcs; exrepnd; subst.
    right; eauto. }
Qed.

Lemma iscvalue_mkc_boolean {o} :
  forall b, @iscvalue o (mkc_boolean b).
Proof.
  introv; destruct b; repeat constructor; simpl; introv i; repndors;
    subst; tcsp; allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_mkc_boolean : slow.

Lemma find_cs_value_at_if_safe_library_implies_isvalue {o} :
  forall lib name k (val : @ChoiceSeqVal o),
    safe_library lib
    -> find_cs_value_at lib name k = Some val
    -> iscvalue val.
Proof.
  introv safe fcs.
  apply find_cs_value_at_if_safe_library in fcs; auto.
  repndors; exrepnd; subst; eauto 3 with slow.
Qed.

Lemma isvalue_inl_axiom {o} : @isvalue o (mk_inl mk_axiom).
Proof.
  repeat constructor; simpl; introv i; repndors; subst; tcsp; allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve isvalue_inl_axiom : slow.

Lemma isvalue_inr_axiom {o} : @isvalue o (mk_inr mk_axiom).
Proof.
  repeat constructor; simpl; introv i; repndors; subst; tcsp; allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve isvalue_inr_axiom : slow.

Inductive def_kind :=
| defk_abs (a : opabs)
| defk_cs  (c : choice_sequence_name).

Definition def_kinds := list def_kind.

Definition get_defs_c {p} (c : @CanonicalOp p) : def_kinds :=
  match c with
  | Ncseq c => [defk_cs c]
  | _ => []
  end.

Definition get_defs_sw (sw : cs_swap) : def_kinds :=
  let (n1,n2) := sw in [defk_cs n1, defk_cs n2].

(*Definition get_defs_n (n : NonCanonicalOp) : def_kinds :=
  match n with
  | NSwapCs2 nfo => get_defs_nfo nfo
  | _ => []
  end.*)

Definition get_defs_o {p} (o : @Opid p) : def_kinds :=
  match o with
  | Can c => get_defs_c c
  | NCan n => [](*get_defs_n n*)
  | NSwapCs2 sw => get_defs_sw sw
  | Abs a => [defk_abs a]
  | Exc => []
  end.

Fixpoint get_defs {p} (t : @NTerm p) : def_kinds :=
  match t with
  | vterm _ => []
  | oterm o bterms => (get_defs_o o) ++ (flat_map get_defs_b bterms)
  end
with get_defs_b {p} (bt : @BTerm p) : def_kinds :=
       match bt with
       | bterm _ t => get_defs t
       end.

Definition nodefs {o} (t : @NTerm o) := get_defs t = [].

Inductive two_swap_cs2 {o} sw : @NTerm o -> @NTerm o -> Type :=
| two_sw_v : forall v, two_swap_cs2 sw (vterm v) (vterm v)
| two_sw_same :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
      -> two_swap_cs2 sw (oterm op bs1) (oterm op bs2)
| two_sw_diff :
    forall t u,
      two_swap_cs2 sw t u
      -> two_swap_cs2 sw (mk_swap_cs2 sw (mk_swap_cs2 sw t)) u
with two_swap_cs2_bterm {o} sw : @BTerm o -> @BTerm o -> Type :=
| two_sw_bterm :
    forall l t u,
      two_swap_cs2 sw t u
      -> two_swap_cs2_bterm sw (bterm l t) (bterm l u).
Hint Constructors two_swap_cs2.
Hint Constructors two_swap_cs2_bterm.

Lemma or_two_swap_cs2_bterm_implies {o} :
  forall sw (x y : @BTerm o) F,
    (forall b1 b2, (x, y) = (b1, b2) [+] (F b1 b2) -> two_swap_cs2_bterm sw b1 b2)
    -> two_swap_cs2_bterm sw x y # (forall b1 b2, F b1 b2 -> two_swap_cs2_bterm sw b1 b2).
Proof.
  introv h; dands.
  { apply h; auto. }
  { introv q; apply h; auto. }
Qed.

Ltac inv_two_sw_term h :=
  let len := fresh "len" in
  let imp := fresh "imp" in
  let dif := fresh "diff" in
  inversion h as [|? ? ? len imp|? ? dif]; subst; clear h.

Ltac inv_two_sw_bterm h :=
  let dif := fresh "diff" in
  inversion h as [? ? ? dif]; subst; clear h.

Ltac inv_two_sw_bterms :=
  match goal with
  | [ H : (forall b1 b2, (_ [+] _) -> two_swap_cs2_bterm _ _ _) |- _ ] => apply or_two_swap_cs2_bterm_implies in H; repnd
  | [ H : (forall b1 b2, False -> two_swap_cs2_bterm _ _ _) |- _ ] => clear H
  | [ H : two_swap_cs2_bterm _ _ _ |- _ ] => inv_two_sw_bterm H
  end.

Ltac cpxpp_step :=
  match goal with
  | [ H : S _ = length ?l |- _ ] => destruct l; simpl in *; cpx
  end.

Ltac cpxpp := repeat first [cpxpp_step | cpx].

Tactic Notation "inv_two_sw" ident(h) := inv_two_sw_term h; simpl in *; cpxpp; simpl in *; repeat inv_two_sw_bterms.

Tactic Notation "inv_two_sw" :=
  match goal with
  | [ H : two_swap_cs2 _ (_ _) _ |- _ ] => inv_two_sw_term H; simpl in *; cpxpp; simpl in *; repeat inv_two_sw_bterms
  | [ H : two_swap_cs2 _ _ (_ _) |- _ ] => inv_two_sw_term H; simpl in *; cpxpp; simpl in *; repeat inv_two_sw_bterms
  | [ H : two_swap_cs2 _ (_ _) _ |- _ ] => inv_two_sw_term H; simpl in *
  | [ H : two_swap_cs2 _ _ (_ _) |- _ ] => inv_two_sw_term H; simpl in *
  end.

Lemma two_swap_cs2_can {o} :
  forall sw c bs (t : @NTerm o),
    two_swap_cs2 sw (oterm (Can c) bs) t
    -> {bs' : list BTerm
        & t = oterm (Can c) bs'
        # length bs = length bs'
        # (forall b1 b2, LIn (b1,b2) (combine bs bs') -> two_swap_cs2_bterm sw b1 b2)}.
Proof.
  introv tsw.
  inv_two_sw tsw.
  eexists; dands; eauto.
Qed.

(* !!MOVE *)
Lemma computes_to_value_implies_isprogram {o} :
  forall lib (t1 t2 : @NTerm o), (t1 =v>( lib) t2) -> isprogram t2.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  apply isvalue_implies in comp; tcsp.
Qed.
Hint Resolve computes_to_value_implies_isprogram : slow.

Lemma isprogam_bt_nt_wf_eauto {p} :
  forall (lv : list NVar) (nt : @NTerm p), isprogram_bt (bterm lv nt) -> nt_wf nt.
Proof.
  introv Hb.
  repnud Hb.
  apply bt_wf_iff in Hb; sp.
Qed.

Lemma isprogram_bt_implies_bt_wf {o} :
  forall (b : @BTerm o), isprogram_bt b -> bt_wf b.
Proof.
  introv isp.
  destruct b.
  apply isprogam_bt_nt_wf_eauto in isp.
  apply wfbt; auto.
Qed.
Hint Resolve isprogram_bt_implies_bt_wf : slow.

Lemma two_swap_cs2_bterms_implies_eq_map_num_bvars {o} :
  forall sw (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; introv len imp; simpl in *; cpxpp.
  inv_two_sw_bterms.
  inv_two_sw_bterm imp0; simpl; f_equal; tcsp.
Qed.

Lemma two_swap_cs2_preserves_nt_wf {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> nt_wf t
    -> nt_wf u.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv d wf; inv_two_sw d; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).

  { allrw @nt_wf_oterm_iff; repnd.
    rewrite <- wf0.
    erewrite (two_swap_cs2_bterms_implies_eq_map_num_bvars sw bs bs2); eauto; dands; auto.
    introv i.
    dup len as j; symmetry in j; eapply implies_in_combine in j; eauto; exrepnd.
    apply in_combine_swap in j0; auto.
    applydup imp in j0.
    inv_two_sw_bterm j1.
    apply in_combine in j0; repnd.
    applydup wf in j1.
    allrw @bt_wf_iff.
    eapply ind; eauto 3 with slow. }

  { repeat apply nt_wf_mk_swap_cs2_implies in wf.
    eapply ind; simpl; eauto; try (complete (left; reflexivity)); simpl; eauto 3 with slow. }
Qed.
Hint Resolve two_swap_cs2_preserves_nt_wf : slow.

Lemma isprogram_bt_implies_subset_free_vars {o} :
  forall l (t : @NTerm o),
    isprogram_bt (bterm l t)
    -> subset (free_vars t) l.
Proof.
  introv isp.
  unfold isprogram_bt in *; repnd.
  unfold closed_bt in *; simpl in *.
  introv i.
  destruct (in_deq _ deq_nvar x l); auto.
  assert (LIn x (remove_nvars l (free_vars t))) as w by (apply in_remove_nvars; tcsp).
  rewrite isp0 in *; simpl in *; tcsp.
Qed.
Hint Resolve isprogram_bt_implies_subset_free_vars : slow.

Inductive two_swap_cs2_sub {o} sw : @Sub o -> @Sub o -> Type :=
| two_sw_sub_nil : two_swap_cs2_sub sw [] []
| two_sw_sub_cons :
    forall (v : NVar) (t1 t2 : NTerm) (s1 s2 : Sub),
      two_swap_cs2 sw t1 t2
      -> two_swap_cs2_sub sw s1 s2
      -> two_swap_cs2_sub sw ((v, t1) :: s1) ((v, t2) :: s2).
Hint Constructors two_swap_cs2_sub.

Lemma sub_find_two_swap_cs2_if_some {o} :
  forall sw (s1 s2 : @Sub o) v t,
    two_swap_cs2_sub sw s1 s2
    -> sub_find s1 v = Some t
    -> {u : NTerm & sub_find s2 v = Some u # two_swap_cs2 sw t u}.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
Qed.

Lemma sub_find_two_swap_cs2_if_none {o} :
  forall sw (s1 s2 : @Sub o) v,
    two_swap_cs2_sub sw s1 s2
    -> sub_find s1 v = None
    -> sub_find s2 v = None.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
Qed.

Lemma implies_two_swap_cs2_sub_filter {o} :
  forall sw (s1 s2 : @Sub o) l,
    two_swap_cs2_sub sw s1 s2
    -> two_swap_cs2_sub sw (sub_filter s1 l) (sub_filter s2 l).
Proof.
  introv d; induction d; simpl in *; boolvar; eauto.
Qed.
Hint Resolve implies_two_swap_cs2_sub_filter : slow.

Lemma implies_two_swap_cs2_lsubst_aux {o} :
  forall sw (t u : @NTerm o) (s1 s2 : @Sub o),
    two_swap_cs2 sw t u
    -> two_swap_cs2_sub sw s1 s2
    -> two_swap_cs2 sw (lsubst_aux t s1) (lsubst_aux u s2).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv h q; simpl in *.

  { inv_two_sw.
    remember (sub_find s1 v) as sfa; symmetry in Heqsfa; destruct sfa.
    { eapply sub_find_two_swap_cs2_if_some in q; eauto; exrepnd; allrw; auto. }
    eapply sub_find_two_swap_cs2_if_none in q; eauto; allrw; auto. }

  inv_two_sw.

  { constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    destruct a0,a; simpl in *.
    inv_two_sw_bterm i0; constructor.
    applydup in_combine in i1; repnd.
    eapply ind; eauto; eauto 3 with slow. }

  constructor; autorewrite with slow.
  eapply ind; eauto; try (left; try reflexivity); simpl; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_lsubst_aux : slow.

Lemma two_swap_cs2_implies_same_bound_vars {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> bound_vars t = bound_vars u.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv d; inv_two_sw; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); simpl; eauto 3 with slow));[].
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_two_sw_bterm i0; simpl.
  f_equal.
  apply in_combine in i; repnd.
  eapply ind; eauto 3 with slow.
Qed.
Hint Resolve two_swap_cs2_implies_same_bound_vars : slow.

Lemma two_swap_cs2_implies_same_free_vars {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> free_vars t = free_vars u.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv d; inv_two_sw; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); simpl; eauto 3 with slow));[].
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_two_sw_bterm i0; simpl.
  f_equal.
  apply in_combine in i; repnd.
  eapply ind; eauto 3 with slow.
Qed.
Hint Resolve two_swap_cs2_implies_same_free_vars : slow.

Lemma two_swap_cs2_sub_implies_same_free_vars {o} :
  forall sw (s1 s2 : @Sub o),
    two_swap_cs2_sub sw s1 s2
    -> flat_map free_vars (range s1) = flat_map free_vars (range s2).
Proof.
  introv d; induction d; simpl; auto; f_equal; auto; eauto 3 with slow.
Qed.

Lemma two_swap_cs2_implies_same_all_vars {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> all_vars t = all_vars u.
Proof.
  introv d.
  applydup @two_swap_cs2_implies_same_free_vars in d.
  applydup @two_swap_cs2_implies_same_bound_vars in d.
  unfold all_vars; allrw; auto.
Qed.
Hint Resolve two_swap_cs2_implies_same_all_vars : slow.

Lemma two_swap_cs2_refl {o} :
  forall sw (t : @NTerm o),
    two_swap_cs2 sw t t.
Proof.
  nterm_ind t as [v|op bs ind] Case; auto.
  apply two_sw_same; auto.
  introv i.
  apply in_combine_same in i; repnd; subst.
  destruct b2; constructor; eapply ind; eauto.
Qed.
Hint Resolve two_swap_cs2_refl : slow.

Lemma two_swap_cs2_sub_refl {o} :
  forall sw (s : @Sub o),
    two_swap_cs2_sub sw s s.
Proof.
  induction s; introv; simpl; repnd; constructor; eauto 3 with slow.
Qed.
Hint Resolve two_swap_cs2_sub_refl : slow.

Lemma implies_two_swap_cs2_change_bvars_alpha {o} :
  forall sw (t u : @NTerm o) l,
    two_swap_cs2 sw t u
    -> two_swap_cs2 sw (change_bvars_alpha l t) (change_bvars_alpha l u).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv d; inv_two_sw d.

  { constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    applydup in_combine in i1; repnd.
    inv_two_sw_bterm i0; simpl.

    pose proof (ind t t l0 i3) as ind'; autodimp ind' hyp; eauto 3 with slow.
    pose proof (ind' u l) as ind'; autodimp ind' hyp; eauto 3 with slow.
    erewrite two_swap_cs2_implies_same_all_vars; eauto 3 with slow. }

  { constructor; autorewrite with slow.
    eapply ind; try (left; reflexivity); simpl; eauto 3 with slow. }
Qed.
Hint Resolve implies_two_swap_cs2_change_bvars_alpha : slow.

Lemma implies_two_swap_cs2_lsubst {o} :
  forall sw (t u : @NTerm o) (s1 s2 : @Sub o),
    two_swap_cs2 sw t u
    -> two_swap_cs2_sub sw s1 s2
    -> two_swap_cs2 sw (lsubst t s1) (lsubst u s2).
Proof.
  introv dt ds.
  unfold lsubst.
  erewrite two_swap_cs2_implies_same_bound_vars; eauto.
  erewrite two_swap_cs2_sub_implies_same_free_vars; eauto.
  boolvar; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_lsubst : slow.

Lemma implies_two_swap_cs2_subst {o} :
  forall sw (t u : @NTerm o) v w z,
    two_swap_cs2 sw t u
    -> two_swap_cs2 sw w z
    -> two_swap_cs2 sw (subst t v w) (subst u v z).
Proof.
  introv dt ds.
  apply implies_two_swap_cs2_lsubst; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_subst : slow.

Lemma two_swap_cs2_preserves_closed {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> closed t
    -> closed u.
Proof.
  introv d isp; apply two_swap_cs2_implies_same_free_vars in d.
  unfold closed in *; try congruence.
Qed.
Hint Resolve two_swap_cs2_preserves_closed : slow.

Lemma two_swap_cs2_preserves_isprogram {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> isprogram t
    -> isprogram u.
Proof.
  introv d isp.
  unfold isprogram in *; repnd; dands; eauto 2 with slow.
Qed.
Hint Resolve two_swap_cs2_preserves_isprogram : slow.

Lemma two_swap_cs2_preserves_iscan {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> iscan t
    -> iscan u.
Proof.
  introv h q.
  inv_two_sw h.
Qed.
Hint Resolve two_swap_cs2_preserves_iscan : slow.

Lemma two_swap_cs2_preserves_isexc {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> isexc t
    -> isexc u.
Proof.
  introv h q.
  inv_two_sw h.
Qed.
Hint Resolve two_swap_cs2_preserves_isexc : slow.

Lemma two_swap_cs2_preserves_isvalue {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> isvalue t
    -> isvalue u.
Proof.
  introv d isv.
  inversion isv as [? isp isc]; subst.
  split; eauto 2 with slow.
Qed.
Hint Resolve two_swap_cs2_preserves_isvalue : slow.

Lemma two_swap_cs2_preserves_isvalue_like {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> isvalue_like t
    -> isvalue_like u.
Proof.
  introv h q; unfold isvalue_like in *; repndors; eauto 3 with slow.
Qed.
Hint Resolve two_swap_cs2_preserves_isvalue_like : slow.

Lemma length_mk_fresh_bterms {o} :
  forall l (bs : list (@BTerm o)),
    length (mk_fresh_bterms l bs) = length bs.
Proof.
  introv.
  unfold mk_fresh_bterms; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_mk_fresh_bterms : slow.

Lemma two_swap_cs2_implies_same_maybe_new_var {o} :
  forall sw (t u : @NTerm o) l k,
    two_swap_cs2 sw t u
    -> maybe_new_var l k t = maybe_new_var l k u.
Proof.
  introv d; unfold maybe_new_var, newvar.
  erewrite two_swap_cs2_implies_same_free_vars; eauto.
Qed.

Lemma maybe_new_var_nil {o} :
  forall v (t : @NTerm o),
    maybe_new_var v [] t = v.
Proof.
  tcsp.
Qed.
Hint Rewrite @maybe_new_var_nil : slow.

Lemma isvalue_like_implies_two_swap_cs2_pushdown_fresh {o} :
  forall sw (t u : @NTerm o) l,
    isvalue_like t
    -> two_swap_cs2 sw t u
    -> two_swap_cs2 sw (pushdown_fresh l t) (pushdown_fresh l u).
Proof.
  introv isv d.
  inv_two_sw d; simpl; autorewrite with slow; eauto 3 with slow.

  { constructor; autorewrite with slow; auto;[].
    introv i.
    unfold mk_fresh_bterms in i.
    rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    inv_two_sw_bterm i0.
    unfold mk_fresh_bterm; simpl; constructor.
    constructor; simpl; auto; introv i; repndors; ginv; tcsp.
    erewrite two_swap_cs2_implies_same_maybe_new_var; eauto. }

  { unfold isvalue_like in *; simpl in *; tcsp. }
Qed.
Hint Resolve isvalue_like_implies_two_swap_cs2_pushdown_fresh : slow.

Fixpoint mk_swap_cs2_2N {o} (n : nat) sw (t : @NTerm o) :=
  match n with
  | 0 => t
  | S m => mk_swap_cs2 sw (mk_swap_cs2 sw (mk_swap_cs2_2N m sw t))
  end.

Lemma isnoncan_like_decidable {o} :
  forall (t : @NTerm o),
    decidable (isnoncan_like t).
Proof.
  introv; destruct t as [v|op bs]; try (complete (right; intro xx; unfold isnoncan_like in *; simpl in *; tcsp)).
  destruct op; try (complete (right; intro xx; unfold isnoncan_like in *; simpl in *; tcsp));
    try (complete (left; unfold isnoncan_like; simpl; tcsp)).
Qed.

Lemma implies_two_swap_cs2_mk_eapply {o} :
  forall sw (t1 t2 u1 u2 : @NTerm o),
    two_swap_cs2 sw t1 u1
    -> two_swap_cs2 sw t2 u2
    -> two_swap_cs2 sw (mk_eapply t1 t2) (mk_eapply u1 u2).
Proof.
  introv da db.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_two_swap_cs2_mk_eapply : slow.

Lemma implies_two_swap_cs2_mk_apply {o} :
  forall sw (t1 t2 u1 u2 : @NTerm o),
    two_swap_cs2 sw t1 u1
    -> two_swap_cs2 sw t2 u2
    -> two_swap_cs2 sw (mk_apply t1 t2) (mk_apply u1 u2).
Proof.
  introv da db.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_two_swap_cs2_mk_apply : slow.

Lemma implies_two_swap_cs2_mk_atom_eq {o} :
  forall sw (t1 t2 t3 t4 u1 u2 u3 u4 : @NTerm o),
    two_swap_cs2 sw t1 u1
    -> two_swap_cs2 sw t2 u2
    -> two_swap_cs2 sw t3 u3
    -> two_swap_cs2 sw t4 u4
    -> two_swap_cs2 sw (mk_atom_eq t1 t2 t3 t4) (mk_atom_eq u1 u2 u3 u4).
Proof.
  introv da db dc dd.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_two_swap_cs2_mk_atom_eq : slow.

Lemma implies_two_swap_cs2_mk_fresh {o} :
  forall sw v (t1 t2 : @NTerm o),
    two_swap_cs2 sw t1 t2
    -> two_swap_cs2 sw (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv d.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_two_swap_cs2_mk_fresh : slow.

Lemma two_swap_cs2_preserves_isnoncan_like {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> isnoncan_like t
    -> isnoncan_like u
       [+] {n : nat
            & {w : NTerm
            & t = mk_swap_cs2_2N n sw w
            # !isnoncan_like w
            # two_swap_cs2 sw w u }}.
Proof.
  introv h; induction h; introv q; simpl in *; tcsp.
  destruct (isnoncan_like_decidable t) as [d|d].
  { autodimp IHh hyp; repndors; exrepnd; subst; tcsp.
    right; exists (S n) w; simpl; dands; tcsp. }
  clear IHh.
  right; exists 1 t; simpl; dands; tcsp.
Qed.

Lemma two_swap_cs2_implies_same_get_utokens {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> get_utokens t = get_utokens u.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv d; inv_two_sw; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); simpl; eauto 3 with slow));[].
  f_equal.
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_two_sw_bterm i0; simpl.
  apply in_combine in i; repnd.
  eapply ind; eauto 3 with slow.
Qed.
Hint Resolve two_swap_cs2_implies_same_get_utokens : slow.

Lemma two_swap_cs2_implies_same_get_fresh_atom {o} :
  forall sw lib (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> get_fresh_atom lib t = get_fresh_atom lib u.
Proof.
  introv d.
  apply two_swap_cs2_implies_same_get_utokens in d.
  unfold get_fresh_atom, get_utokens_lib.
  allrw; auto.
Qed.
Hint Resolve two_swap_cs2_implies_same_get_fresh_atom : slow.

Lemma implies_wf_term_oterm_fst {o} :
  forall op l (t : @NTerm o) bs,
    wf_term (oterm op (bterm l t :: bs))
    -> wf_term t.
Proof.
  introv wf.
  allrw @wf_oterm_iff; repnd.
  pose proof (wf (bterm l t)) as wf; simpl in wf; autodimp wf hyp.
Qed.
Hint Resolve implies_wf_term_oterm_fst : slow.

Lemma implies_wf_term_oterm_snd {o} :
  forall op l1 l2 (t1 t2 : @NTerm o) bs,
    wf_term (oterm op (bterm l1 t1 :: bterm l2 t2 :: bs))
    -> wf_term t2.
Proof.
  introv wf.
  allrw @wf_oterm_iff; repnd.
  pose proof (wf (bterm l2 t2)) as wf; simpl in wf; autodimp wf hyp.
Qed.
Hint Resolve implies_wf_term_oterm_snd : slow.

Hint Resolve subst_preserves_wf_term : slow.

Lemma two_swap_cs2_preserves_wf_term {o} :
  forall sw (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> wf_term t
    -> wf_term u.
Proof.
  introv h wf; allrw @wf_term_eq; eauto 3 with slow.
Qed.
Hint Resolve  two_swap_cs2_preserves_wf_term : slow.

Lemma implies_alpha_eq_oterm_fst {o} :
  forall op bs l (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (oterm op (bterm l a :: bs)) (oterm op (bterm l b :: bs)).
Proof.
  introv aeq.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i.
  repndors; ginv; eauto 3 with slow.
  apply in_combine_same in i; repnd; subst; eauto 3 with slow.
Qed.

Hint Resolve get_fresh_atom_prop_and_lib : slow.

Lemma two_swap_cs_bterms_preserves_eapply_wf_def {o} :
  forall sw op (bs1 bs2 : list (@BTerm o)),
    Datatypes.length bs1 = Datatypes.length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> eapply_wf_def (oterm op bs1)
    -> eapply_wf_def (oterm op bs2).
Proof.
  introv len imp wf.
  unfold eapply_wf_def in *; repndors; exrepnd; unfold mk_choice_seq, mk_lam in *;
    ginv; simpl in *; cpx; simpl in *; eauto.
  pose proof (imp (bterm [v] b) x) as imp; autodimp imp hyp.
  inv_two_sw_bterm imp; eauto.
Qed.

Lemma wf_term_swap_cs1_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NSwapCs1) bs)
    <=> {a, b, c : NTerm $ bs = [bterm [] a, bterm [] b, bterm [] c] # wf_term a # wf_term b # wf_term c}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp; cpx).
    destruct b as [l1 t1]; destruct b0 as [l2 t2]; destruct b1 as [l3 t3].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2, l3; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    pose proof (k (bterm [] t3)) as h3; autodimp h3 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2 t3; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma implies_swap_cs1_red_aux {o} :
  forall lib (t a v b : @NTerm o),
    iscan t
    -> reduces_to lib a v
    -> reduces_to lib (mk_swap_cs1 t a b) (mk_swap_cs1 t v b).
Proof.
  introv wf comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.
  revert dependent a.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup IHk in comp0.
    destruct a as [w|op bs].

    + csunf comp1; allsimpl; ginv.

    + dopid op as [can|ncan|nsw|exc|abs] Case;
        try (complete (eapply reduces_to_if_split2;[|exact comp2];
                       apply iscan_implies in wf; exrepnd; subst;
                       csunf; simpl; allrw; simpl; auto)).

      * Case "Can".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.

      * Case "Exc".
        csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; ginv; eauto 3 with slow.
Qed.

Lemma implies_two_swap_cs2_find_last_entry_default {o} :
  forall sw lib name (a b : @NTerm o),
    two_swap_cs2 sw a b
    -> two_swap_cs2 sw (find_last_entry_default lib name a) (find_last_entry_default lib name b).
Proof.
  introv tws; unfold find_last_entry_default.
  remember (find_cs lib name) as q; destruct q; auto.
  remember (last_cs_entry c) as h; destruct h; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_find_last_entry_default : slow.

Lemma implies_two_swap_cs2_subst_utokens_aux {o} :
  forall sw (a b : @NTerm o) s,
    two_swap_cs2 sw a b
    -> two_swap_cs2 sw (subst_utokens_aux a s) (subst_utokens_aux b s).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv h.
  { simpl in *; inv_two_sw. }
  rewrite subst_utokens_aux_oterm.
  remember (get_utok op) as g; symmetry in Heqg; destruct g.
  { inv_two_sw_term h; try (complete (simpl in *; ginv)).
    rewrite subst_utokens_aux_oterm; allrw.
    unfold subst_utok.
    remember (utok_sub_find s g) as u; symmetry in Hequ; destruct u; eauto 3 with slow.
    constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    apply in_combine in i1; repnd.
    inv_two_sw_bterm i0; simpl; eauto.
    constructor; eapply ind; eauto; eauto 3 with slow. }
  inv_two_sw_term h; try (complete (simpl in *; ginv)).
  { rewrite subst_utokens_aux_oterm; allrw.
    constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    apply in_combine in i1; repnd.
    inv_two_sw_bterm i0; simpl; eauto.
    constructor; eapply ind; eauto; eauto 3 with slow. }
  simpl in *; fold_terms; GC.
  apply two_sw_diff; eauto.
  eapply ind; try (left; reflexivity); simpl; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_subst_utokens_aux : slow.

Lemma implies_two_swap_cs2_subst_utokens {o} :
  forall sw (a b : @NTerm o) s,
    two_swap_cs2 sw a b
    -> two_swap_cs2 sw (subst_utokens a s) (subst_utokens b s).
Proof.
  introv h; unfold subst_utokens.
  applydup @two_swap_cs2_implies_same_bound_vars in h; rewrite h0; boolvar; eauto 3 with slow.
Qed.
Hint Resolve implies_two_swap_cs2_subst_utokens : slow.

Lemma co_wf_def_two_swap_cs2_implies_iswfpk {o} :
  forall sw comp c (bs1 bs2 : list (@BTerm o)),
    co_wf_def comp c bs1
    -> length bs1 = Datatypes.length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> iswfpk comp (oterm (Can c) bs2).
Proof.
  introv wf len imp.
  unfold co_wf_def in *; exrepnd; repndors; exrepnd; subst; simpl in *; cpx.
  { destruct c; simpl in *; ginv; simpl; eauto.
    { exists (@PKi o z); auto. }
    { exists (@PKc o c); auto. }
    { exists (@PKs o s); auto. }
    { exists (@PKa o g); auto. } }
  { destruct c; simpl in *; ginv; simpl; eauto.
    exists i; eauto. }
Qed.
Hint Resolve co_wf_def_two_swap_cs2_implies_iswfpk : slow.

Lemma ca_wf_def_two_swap_cs2_implies_iswfpk {o} :
  forall sw c (bs1 bs2 : list (@BTerm o)),
    ca_wf_def c bs1
    -> length bs1 = Datatypes.length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> isinteger (oterm (Can c) bs2).
Proof.
  introv wf len imp.
  unfold ca_wf_def in *; exrepnd; repndors; exrepnd; subst; simpl in *; cpx.
  exists i; eauto.
Qed.
Hint Resolve ca_wf_def_two_swap_cs2_implies_iswfpk : slow.

Lemma implies_alpha_eq_mk_arithop {o} :
  forall op (a1 a2 b1 b2 : @NTerm o),
    alpha_eq a1 b1
    -> alpha_eq a2 b2
    -> alpha_eq (mk_arithop op a1 a2) (mk_arithop op b1 b2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_alpha_eq_mk_compop {o} :
  forall op (a1 a2 a3 a4 b1 b2 b3 b4 : @NTerm o),
    alpha_eq a1 b1
    -> alpha_eq a2 b2
    -> alpha_eq a3 b3
    -> alpha_eq a4 b4
    -> alpha_eq (mk_compop op a1 a2 a3 a4) (mk_compop op b1 b2 b3 b4).
Proof.
  introv aeq1 aeq2 aeq3 aeq4.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_two_swap_cs2_push_swap_cs_can {o} :
  forall sw nsw c (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> two_swap_cs2 sw (push_swap_cs_can nsw c bs1) (push_swap_cs_can nsw c bs2).
Proof.
  introv len imp.
  unfold push_swap_cs_can.
  constructor; autorewrite with slow; simpl; auto.
  introv i.
  unfold push_swap_cs_bterms in i; rewrite <-map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply imp in i1.
  inv_two_sw_bterm i1; constructor.
  eapply two_sw_same; simpl; auto.
  introv i; repndors; ginv; tcsp.
  constructor.
  unfold push_swap_cs_sub_term; eauto with slow.
Qed.
Hint Resolve implies_two_swap_cs2_push_swap_cs_can : slow.

Lemma implies_two_swap_cs2_push_swap_cs_exc {o} :
  forall sw nsw (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> two_swap_cs2_bterm sw b1 b2)
    -> two_swap_cs2 sw (push_swap_cs_exc nsw bs1) (push_swap_cs_exc nsw bs2).
Proof.
  introv len imp.
  unfold push_swap_cs_exc.
  constructor; autorewrite with slow; simpl; auto.
  introv i.
  unfold push_swap_cs_bterms in i; rewrite <-map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply imp in i1.
  inv_two_sw_bterm i1; constructor.
  eapply two_sw_same; simpl; auto.
  introv i; repndors; ginv; tcsp.
  constructor.
  unfold push_swap_cs_sub_term; eauto with slow.
Qed.
Hint Resolve implies_two_swap_cs2_push_swap_cs_exc : slow.

Lemma compute_step_two_swap_cs2 {o} :
  forall sw lib (t u : @NTerm o) z,
    wf_term t
    -> two_swap_cs2 sw t u
    -> compute_step lib t = csuccess z
    -> {a : NTerm
        & {b : NTerm
        & {a' : NTerm
        & {b' : NTerm
        & reduces_to lib u b
        # reduces_to lib z a
        # two_swap_cs2 sw a' b'
        # alpha_eq b b'
        # alpha_eq a a'}}}}.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv wf tsw comp; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|nsw|exc|abs] SCase.

  { SCase "Can".
    csunf comp; simpl in *; ginv; eauto.
    inv_two_sw.
    eexists; eexists; eexists; eexists; dands; try (apply reduces_to_symm); try apply alpha_eq_refl; eauto. }

  { SCase "NCan".
    csunf comp; simpl in *.
    dterms w; try (complete (csunf; simpl; eauto));
      try (complete (apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
                     inv_two_sw; eapply ind in comp1; try (left; eauto); eauto 3 with slow; exrepnd;
                     eexists; eexists; eexists; eexists; dands;[eapply reduces_to_prinarg;eauto|eapply reduces_to_prinarg;eauto| | |];
                     try apply implies_alpha_eq_oterm_fst; eauto;
                     repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp))).

    { apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *.
      inv_two_sw.
      eexists; eexists; eexists; eexists; dands;[apply reduces_to_if_step; csunf; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl];eauto;
        try apply reduces_to_symm; simpl; eauto 3 with slow. }

    { dopid_noncan ncan SSCase; simpl in *;
      try apply_comp_success;
      try (complete (dcwf h));
      try (complete (ginv; csunf; simpl in *; eauto)).

      { SSCase "NFix".
        ginv.
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists;dands;[apply reduces_to_if_step; csunf; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl]; eauto;
          try apply reduces_to_symm; eauto.
        repeat (constructor; simpl; auto; introv xx; repndors; subst; ginv; tcsp; constructor; auto). }

      { SSCase "NSleep".
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;[apply reduces_to_if_step; csunf; simpl;unfold compute_step_sleep; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl]; eauto;
          try apply reduces_to_symm; eauto 3 with slow. }

      { SSCase "NTUni".
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;[apply reduces_to_if_step; csunf; simpl;unfold compute_step_tuni; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl];
          try apply reduces_to_symm; eauto 3 with slow.
        boolvar; try omega; autorewrite with slow; auto. }

      { SSCase "NMinus".
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;[apply reduces_to_if_step; csunf; simpl;unfold compute_step_minus; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl];
          try apply reduces_to_symm; eauto 3 with slow. }

      { SSCase "NParallel".
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;[apply reduces_to_if_step; csunf; simpl;unfold compute_step_parallel; simpl| | |apply alpha_eq_refl|apply alpha_eq_refl];
          try apply reduces_to_symm; eauto 3 with slow. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; ginv; subst; simpl in *.
      inv_two_sw.
      inv_two_sw.
      eexists; eexists; eexists; eexists; dands;
        [apply reduces_to_if_step;csunf; simpl; rewrite compute_step_catch_if_diff
        |apply reduces_to_if_step;csunf; simpl| | |]; try apply alpha_eq_refl; eauto. }

    { inv_two_sw.
      apply compute_step_fresh_success in comp; repeat (repndors; exrepnd; GC; ginv; subst; simpl in * ).
      { inv_two_sw.
        eexists; eexists; eexists; eexists; dands; try (apply reduces_to_if_step; csunf; simpl; boolvar; eauto); try apply alpha_eq_refl.
        repeat (constructor; simpl; auto; introv i; repndors; tcsp; ginv). }
      { eexists; eexists; eexists; eexists; dands; try (apply reduces_to_if_step; rewrite compute_step_fresh_if_isvalue_like2; eauto); try apply alpha_eq_refl; eauto 3 with slow. }
      { pose proof (ind w2 (subst w2 w0 (mk_utoken (get_fresh_atom lib w2))) [w0]) as ind.
        rewrite simple_osize_subst in ind; eauto 3 with slow.
        repeat (autodimp ind hyp); eauto 3 with slow.
        pose proof (ind (subst u w0 (mk_utoken (get_fresh_atom lib u))) x) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow.
        { erewrite two_swap_cs2_implies_same_get_fresh_atom; eauto 3 with slow. }
        exrepnd; fold_terms.
        apply reduces_to_fresh in ind0; auto; exrepnd; eauto 3 with slow.

        applydup @compute_step_preserves_wf in comp2; eauto 3 with slow;[].
        applydup @wf_fresh_iff in wf.
        assert (!LIn w0 (free_vars x)) as ni.
        { apply compute_step_preserves in comp2; eauto 3 with slow;[]; repnd.
          intro i; apply subvars_eq in comp3; apply comp3 in i.
          unfold subst in i; rewrite free_vars_cl_lsubst in i; eauto 3 with slow.
          simpl in i; apply in_remove_nvars in i; simpl in i; tcsp. }

        pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom lib w2) w0) as q.
        repeat (autodimp q hyp);[].
        apply (alpha_eq_ren_utokens _ _ [(get_fresh_atom lib w2, get_fresh_atom lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)]))]) in q.
        rewrite subst_ren_utokens in q.
        rewrite ren_utokens_trivial in q; simpl in *; fold_terms;
          [|apply disjoint_singleton_l;
            intro xx; apply get_utokens_subst_utokens_subset in xx; simpl in xx;
            unfold get_utokens_utok_ren in xx; simpl in xx; autorewrite with slow in xx;
            apply in_remove in xx; tcsp].
        unfold ren_atom in q; simpl in *; boolvar; tcsp; GC;[].
        dup ind2 as h.

        assert (!LIn (get_fresh_atom lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)]))
                 (remove (get_patom_deq o) (get_fresh_atom lib w2) (get_utokens_lib lib x))) as nif.
        { intro xx; apply in_remove in xx; repnd; tcsp.
          pose proof (get_fresh_atom_prop_and_lib lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)])) as w.
          remember (get_fresh_atom lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)])) as p; clear Heqp.
          allrw @in_app_iff; apply not_over_or in w; repnd; repndors; tcsp.
          destruct w1; apply get_utokens_subst_utokens_subset2; auto; simpl; apply in_remove; tcsp. }

        apply (reduces_to_ren_utokens _ _ _ [(get_fresh_atom lib w2, get_fresh_atom lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)]))]) in h; simpl; eauto 3 with slow;
          try (complete (apply disjoint_singleton_r; eauto 3 with slow));
          try (complete (apply disjoint_singleton_l; auto));[].

        apply alpha_eq_sym in q.
        eapply reduces_to_alpha in h; try exact q; eauto 3 with slow; exrepnd;[].
        apply reduces_to_fresh in h1; eauto 2 with slow; exrepnd;
          try (apply wf_subst_utokens; eauto 3 with slow);[].

        eapply alpha_eq_trans in h0;[|apply alpha_eq_ren_utokens; apply alpha_eq_sym; eauto].
        apply alpha_eq_sym in h2; eapply alpha_eq_trans in h2;
          [|apply alpha_eq_subst_utokens;[eauto|]; apply alphaeq_utok_sub_refl].

        pose proof (simple_ren_utokens_subst_utokens_eq1
                      a' []
                      (get_fresh_atom lib w2)
                      (get_fresh_atom lib (subst_utokens x [(get_fresh_atom lib w2, mk_var w0)]))
                      w0 (remove (get_patom_deq o) (get_fresh_atom lib w2) (get_utokens_lib lib x))) as w.
        simpl in w; autorewrite with slow in w.
        repeat (autodimp w hyp); eauto 3 with slow.
        { apply alphaeq_preserves_utokens in ind1; rewrite <- ind1.
          apply reduces_to_preserves_utokens in ind2; eauto 3 with slow;[].
          introv i; apply (get_utokens_subset_get_utokens_lib lib) in i; apply ind2 in i.
          simpl.
          destruct (get_patom_deq o (get_fresh_atom lib w2) x0); subst; tcsp.
          right; apply in_remove; tcsp. }
        { introv i j; tcsp; unfold ren_atom in j; simpl in j; subst; tcsp. }
        rewrite w in h2; clear w.
        rewrite ren_utokens_trivial in h2; simpl; auto;[].

        eexists; eexists; eexists; eexists; dands; try exact ind0; try exact h1;
          [|apply implies_alpha_eq_mk_fresh; eapply alpha_eq_trans;[eauto|];
            apply alpha_eq_subst_utokens;[eauto|]; apply alphaeq_utok_sub_refl
           |apply implies_alpha_eq_mk_fresh; eapply alpha_eq_trans;[eauto|]; apply alpha_eq_sym; eauto].

        apply implies_two_swap_cs2_mk_fresh.
        apply (two_swap_cs2_implies_same_get_fresh_atom _ lib) in diff; rewrite diff.
        apply implies_two_swap_cs2_subst_utokens; auto. } }

    { dopid_noncan ncan SSCase; simpl in *;
        try apply_comp_success;
        try (complete (dcwf h));
        try (complete (dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
                       unfold apply_bterm; autorewrite with slow; simpl; eauto));
        try (complete (try dterms w; repndors; repnd; subst; simpl in *;
                       repeat inv_two_sw; eexists;eexists;eexists;eexists;dands;[apply reduces_to_if_step;csunf;simpl|apply reduces_to_symm| | |];
                       try apply alpha_eq_refl; eauto;
                       unfold subst, apply_bterm; autorewrite with slow; simpl; tcsp; eauto 4 with slow)).

      { SSCase "NEApply".
        unfold nobnd in *; ginv; simpl in *.
        inv_two_sw.
        repndors; exrepnd; subst; simpl in *; tcsp.

        { inv_two_sw.
          apply compute_step_eapply2_success in comp1; repnd; repndors; exrepnd;
            unfold mk_lam, mk_choice_seq in *; subst; repeat (simpl in *; ginv; cpx).

          { pose proof (imp0 (bterm [v] b) x) as imp0; autodimp imp0 hyp.
            inv_two_sw_bterm imp0.
            applydup @two_swap_cs2_preserves_iscan in diff as isc; auto.
            apply iscan_implies in isc; exrepnd; subst.
            eexists; eexists; eexists; eexists; dands;
              [apply reduces_to_if_step;csunf;simpl;dcwf h; simpl; eauto| | | |];
              try apply alpha_eq_refl;
              try apply reduces_to_symm; eauto.
            unfold apply_bterm; simpl; eauto 3 with slow. }

          inv_two_sw; simpl in *; GC.
          eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step;csunf;simpl;dcwf h; simpl; boolvar; try omega; autorewrite with slow; allrw; eauto| | | |];
            try apply alpha_eq_refl; try (apply reduces_to_symm); eauto; eauto 3 with slow. }

        { apply isexc_implies2 in comp0; exrepnd; subst.
          repeat inv_two_sw.
          dup comp2 as wfd.
          eapply two_swap_cs_bterms_preserves_eapply_wf_def in wfd; eauto.
          eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step;csunf;simpl;dcwf h| | | |];
            try apply alpha_eq_refl; try apply reduces_to_symm; eauto. }

        eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
        exrepnd.
        inv_two_sw.
        dup comp2 as wfd.
        eapply two_swap_cs_bterms_preserves_eapply_wf_def in wfd; eauto.
        allrw @wf_term_eapply_iff; exrepnd; ginv; simpl in *; cpx.
        eexists; eexists; eexists; eexists; dands;
          try (apply implies_eapply_red_aux; eauto);
          try (apply implies_alpha_eq_mk_eapply;eauto).
        repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp). }

      { SSCase "NDecide".
        repeat inv_two_sw.
        repndors; exrepnd; subst; simpl in *.

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto| | | |];
            try apply alpha_eq_refl; try apply reduces_to_symm; eauto.
          unfold apply_bterm; simpl; allrw @fold_subst; eauto 3 with slow. }

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto| | | |];
            try apply alpha_eq_refl;try apply reduces_to_symm; eauto.
          unfold apply_bterm; simpl; allrw @fold_subst; eauto 3 with slow. } }

(*      { SSCase "NTryCatch".
        dterms w.
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;
          [apply reduces_to_if_step; csunf; simpl; eauto| | | |];
          try apply alpha_eq_refl; try apply reduces_to_symm; eauto.
        repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp).
        constructor; eauto 3 with slow. }*)

(*      { SSCase "NParallel".
        dterms w.
        repeat inv_two_sw.
        eexists; eexists; eexists; dands;
          [apply reduces_to_if_step; csunf; simpl; eauto| | |];
          try unfold compute_step_parallel;
          try apply reduces_to_symm; eauto; eauto 3 with slow. }*)

      { SSCase "NSwapCs1".
        dterms w; simpl in *.

        { apply compute_step_swap_cs1_aux_success_implies in comp; exrepnd; subst; simpl in *.
          repeat inv_two_sw.
          eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto| | | |];
            try apply alpha_eq_refl; try apply reduces_to_symm; eauto.
          repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp). }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          inv_two_sw.
          eapply ind in comp1; try (right;left;eauto); eauto 3 with slow.
          exrepnd.
          repeat inv_two_sw.
          allrw @wf_term_swap_cs1_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms.
          eexists; eexists; eexists; eexists; dands;
            try (apply implies_swap_cs1_red_aux; eauto 3 with slow);
            try apply implies_alpha_eq_mk_swap_cs1; eauto.
          repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp). }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          inv_two_sw.
          eapply ind in comp1; try (right;left;eauto); eauto 3 with slow.
          exrepnd.
          inv_two_sw diff0.
          allrw @wf_term_swap_cs1_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms.
          eexists; eexists; eexists; eexists; dands;
            try (apply implies_swap_cs1_red_aux; eauto 3 with slow);
            try apply implies_alpha_eq_mk_swap_cs1; eauto.
          repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp). }

        { repeat inv_two_sw.
          eexists; eexists; eexists; eexists; dands;
            try apply alpha_eq_refl; try (apply reduces_to_if_step; csunf; simpl; eauto); eauto. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          inv_two_sw.
          eapply ind in comp1; try (right;left;eauto); eauto 3 with slow.
          exrepnd.
          repeat inv_two_sw.
          allrw @wf_term_swap_cs1_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms.
          eexists; eexists; eexists; eexists; dands;
            try (apply implies_swap_cs1_red_aux; eauto 3 with slow);
            try apply implies_alpha_eq_mk_swap_cs1; eauto.
          repeat (constructor; simpl; auto; introv i; repndors; ginv; tcsp). } }

      { SSCase "NLastCs".
        unfold nobnd in *; ginv.
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;
          [apply reduces_to_if_step; csunf; simpl;eauto| | | |];
          try apply alpha_eq_refl; try apply reduces_to_symm; eauto; eauto 3 with slow. }

      { unfold nobnd in *; ginv.
        repeat inv_two_sw.
        repndors; exrepnd; subst.

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto| | | |];
            try apply alpha_eq_refl;try apply reduces_to_symm; eauto; eauto 3 with slow. }

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto; autorewrite with slow; boolvar; try omega; eauto| | | |];
            try apply alpha_eq_refl;try apply reduces_to_symm; eauto; eauto 3 with slow.
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp).
          constructor; eauto 3 with slow. } }

      { unfold nobnd in *; ginv.
        repeat inv_two_sw.
        repndors; exrepnd; subst.

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto;boolvar; try omega; eauto| | | |];
            try apply alpha_eq_refl; try apply reduces_to_symm; eauto; eauto 3 with slow. }

        { eexists; eexists; eexists; eexists; dands;
            [apply reduces_to_if_step; csunf; simpl; eauto; autorewrite with slow; boolvar; try omega; eauto| | | |];
            try apply alpha_eq_refl;try apply reduces_to_symm; eauto; eauto 3 with slow.
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp).
          constructor; eauto 3 with slow. } }

      { SSCase "NCompOp".
        dcwf h;[].
        repeat (dterm w; repeat inv_two_sw; ginv).

        { apply compute_step_compop_success_can_can in comp; exrepnd; subst; simpl in *;[].
          repndors; exrepnd; subst; cpx; simpl in *; repeat inv_two_sw_bterms; boolvar; subst; tcsp;
            try (complete (eexists; eexists; eexists; eexists; dands;
                           [apply reduces_to_if_step; csunf; simpl; dcwf h;
                            unfold compute_step_comp; simpl; allrw; eauto| | | |];
                           try apply alpha_eq_refl; try apply reduces_to_symm; eauto; boolvar; try omega; auto; tcsp)). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_ncompop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_comp_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_compop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_ncompop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_comp_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_compop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { eexists; eexists; eexists; eexists; dands;
            try (apply reduces_to_if_step; csunf; simpl; try dcwf h; eauto);
            try apply alpha_eq_refl; eauto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_ncompop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_comp_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_compop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_ncompop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_comp_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_compop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). } }

      { SSCase "NArithOp".
        dcwf h;[].
        repeat (dterm w; repeat inv_two_sw; ginv).

        { apply compute_step_arithop_success_can_can in comp; exrepnd; subst; simpl in *;[]; cpx.
          repndors; exrepnd; subst; cpx; simpl in *; repeat inv_two_sw_bterms; boolvar; subst; tcsp;
            try (complete (eexists; eexists; eexists; eexists; dands;
                           [apply reduces_to_if_step; csunf; simpl; dcwf h;
                            unfold compute_step_comp; simpl; allrw; eauto| | | |];
                           try apply alpha_eq_refl; try apply reduces_to_symm; eauto; boolvar; try omega; auto; tcsp;
                           repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp))). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_narithop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_arith_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_arithop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_narithop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_arith_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_arithop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { eexists; eexists; eexists; eexists; dands;
            try (apply reduces_to_if_step; csunf; simpl; try dcwf h; eauto);
            try apply alpha_eq_refl; eauto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_narithop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_arith_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_arithop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right;left;eauto);try (complete (constructor; eauto)); eauto 3 with slow; exrepnd.
          allrw @wf_term_narithop_iff; exrepnd; ginv; simpl in *; cpx; simpl in *.
          repeat inv_two_sw_bterms; fold_terms.
          eexists; eexists; eexists; eexists; dands;
            try (eapply reduce_to_prinargs_arith_can; eauto; try apply reduces_to_symm; eauto 3 with slow);
            try (apply implies_alpha_eq_mk_arithop; eauto).
          repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). } }

      { dterms w.
        repeat inv_two_sw.
        eexists; eexists; eexists; eexists; dands;
          try (complete (apply reduces_to_if_step; csunf; simpl; eauto));
          try apply reduces_to_symm; try apply alpha_eq_refl.
        destruct (canonical_form_test_for c w4); auto. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; subst; simpl in *; ginv; repeat inv_two_sw.
      { eexists; eexists; eexists; eexists; dands;
          try (complete (apply reduces_to_if_step; csunf;simpl; eauto));
          try apply reduces_to_symm; try apply alpha_eq_refl.
        apply implies_two_swap_cs2_mk_atom_eq; eauto 3 with slow.
        repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). }
      { eexists; eexists; eexists; eexists; dands;
          try (complete (apply reduces_to_if_step; csunf; simpl; rewrite compute_step_catch_non_trycatch; eauto));
          try apply reduces_to_symm; try apply alpha_eq_refl.
        repeat (constructor; simpl; auto; introv j; repndors; ginv; tcsp). } }

    { apply compute_step_fresh_success in comp; repeat (repndors; exrepnd; GC; ginv; subst; simpl in * ). } }

  { apply compute_step_NSwapCs2_success in comp; exrepnd; subst.
    apply compute_step_swap_cs2_success in comp0; repndors; exrepnd; subst; simpl in *.

    { repeat inv_two_sw; fold_terms.
      eexists; eexists; eexists; eexists; dands;
        try (complete (apply reduces_to_if_step; csunf; simpl; eauto)); try apply alpha_eq_refl; eauto 3 with slow. }

    { repeat inv_two_sw; fold_terms.
      eexists; eexists; eexists; eexists; dands;
        try (complete (apply reduces_to_if_step; csunf; simpl; eauto)); try apply alpha_eq_refl; eauto 3 with slow. }





  }

  { csunf comp; simpl in *; ginv.
    inv_two_sw.
    eexists; eexists; eexists; eexists; dands;
      try (complete (apply reduces_to_if_step; csunf; simpl; eauto)); try apply alpha_eq_refl; eauto 3 with slow. }

  { csunf comp; simpl in *; inv_two_sw.

    admit. }
Admitted.

Lemma reduces_to_or {o} :
  forall lib (k : nat) (t u v : @NTerm o),
    reduces_in_atmost_k_steps lib t u k
    -> reduces_to lib t v
    -> {k1 : nat & {k2 : nat
        & k = (k1 + k2)%nat
        # reduces_in_atmost_k_steps lib t v k1
        # reduces_in_atmost_k_steps lib v u k2 }}
       [+]
       reduces_to lib u v.
Proof.
  introv ra rb.
  unfold reduces_to, reduces_in_atmost_k_steps in *; exrepnd.
  destruct (le_dec k k0).
  { right; exists (k0 - k).
    eapply compute_split; eauto. }
  left.
  exists k0 (k - k0).
  rewrite le_plus_minus_r; try omega; dands; auto.
  eapply compute_split; eauto; try omega.
Qed.

Lemma reduces_in_atmost_k_steps_two_swap_cs2 {o} :
  forall sw lib k (t u : @NTerm o) z,
    two_swap_cs2 sw t u
    -> reduces_in_atmost_k_steps lib t z k
    -> {a : NTerm
        & {b : NTerm
        & reduces_to lib u b
        # reduces_to lib z a
        # two_swap_cs2 sw a b}}.
Proof.
  induction k as [? ind] using comp_ind_type; introv h r.
  destruct k.
  { allrw @reduces_in_atmost_k_steps_0; subst.
    exists z u; dands; eauto 3 with slow. }
  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  eapply compute_step_two_swap_cs2 in r1; eauto; exrepnd.
  eapply reduces_to_or in r0; eauto.
  repndors; exrepnd;[|exists a b; dands; auto];[].
  subst.
  eapply ind in r0; try exact r1; try omega.
  exrepnd.
  exists a0 b0; dands; eauto 3 with slow.
  eapply reduces_to_trans; eauto.
Qed.

Lemma reduces_to_two_swap_cs2 {o} :
  forall sw lib (t u : @NTerm o) z,
    two_swap_cs2 sw t u
    -> reduces_to lib t z
    -> {a : NTerm
        & {b : NTerm
        & reduces_to lib u b
        # reduces_to lib z a
        # two_swap_cs2 sw a b}}.
Proof.
  introv h r.
  unfold reduces_to in r; exrepnd.
  eapply reduces_in_atmost_k_steps_two_swap_cs2 in r0; eauto.
Qed.

Lemma computes_to_value_two_swap_cs2 {o} :
  forall sw lib (t u : @NTerm o) z,
    two_swap_cs2 sw t u
    -> computes_to_value lib t z
    -> {w : NTerm
        & computes_to_value lib u w
        # two_swap_cs2 sw z w}.
Proof.
  introv h r; unfold computes_to_value in *; repnd.
  eapply reduces_to_two_swap_cs2 in r0; eauto; exrepnd.
  apply reduces_to_if_value in r2; auto; subst.
  exists b; dands; eauto 3 with slow.
Qed.

Lemma approx_two_swap_cs2 {o} :
  forall sw lib (t u : @NTerm o),
    isprog t
    -> isprog u
    -> two_swap_cs2 sw t u
    -> approx lib t u.
Proof.
  cofix ind; introv ispt ispu tsw.
  constructor; unfold close_comput; dands; auto; eauto 2 with slow.

  { (* VAL case *)

    introv comp.
    applydup @computes_to_value_implies_isprogram in comp as wf.
    eapply computes_to_value_two_swap_cs2 in comp; eauto; exrepnd.
    apply two_swap_cs2_can in comp0; exrepnd; subst.
    eexists; dands; eauto.

    unfold lblift; autorewrite with slow; dands; auto.
    introv ln; autorewrite with slow.

    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (select2bts tl_subterms bs' n) as q; repeat (autodimp q hyp); exrepnd.
    applydup comp2 in q1.
    rewrite q0, q2.
    rewrite q0 in wf, wf0.
    destruct b1 as [l1 u1], b2 as [l2 u2].
    apply bt_wf_iff in wf0.
    inv_two_sw_bterm q3.

    exists l2 u1 u2; dands; eauto 3 with slow.
    unfold olift.
    dands; eauto 2 with slow.

    assert (subset (free_vars u1) l2) as ssa by eauto 2 with slow.
    introv wfs ispa ispb; left.
    eapply ind; eauto 3 with slow. }

  { (* EXC case *)

    introv comp.
    applydup @preserve_program_exc2 in comp; auto; repnd; eauto 3 with slow.
    eapply reduces_to_two_swap_cs2 in comp; eauto; exrepnd.
    apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow; subst.
    inv_two_sw.
    applydup @reduces_to_preserves_program in comp2; eauto 3 with slow.
    apply isprogram_exception_iff in comp3; repnd.
    exists u1 u0; dands; auto; left; eapply ind; eauto 3 with slow. }
Qed.

Lemma implies_two_swap_cs2_mk_swap_cs2 {o} :
  forall sw sw' (t u : @NTerm o),
    two_swap_cs2 sw t u
    -> two_swap_cs2 sw (mk_swap_cs2 sw' t) (mk_swap_cs2 sw' u).
Proof.
  introv d.
  repeat (constructor; simpl; tcsp; introv i; repndors; ginv; tcsp).
Qed.
Hint Resolve implies_two_swap_cs2_mk_swap_cs2 : slow.

Lemma implies_closed_mk_swap_cs2 {o} :
  forall sw (t : @NTerm o),
    closed t
    -> closed (mk_swap_cs2 sw t).
Proof.
  introv cl; unfold closed in *; simpl in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_closed_mk_swap_cs2 : slow.

Definition sw_sub_ts {o} sw l (k : list (@NTerm o)) : @Sub o :=
  combine l (map (mk_swap_cs2 sw) k).

Lemma areprograms_implies_prog_sw_sub_ts {o} :
  forall sw l (ts : list (@NTerm o)),
    areprograms ts
    -> prog_sub (sw_sub_ts sw l ts).
Proof.
  unfold sw_sub_ts; induction l; introv aps; simpl in *; eauto 3 with slow.
  destruct ts; simpl in *; eauto 3 with slow.
  allrw @areprograms_cons; repnd.
  allrw @prog_sub_cons; dands; eauto 3 with slow.
Qed.
Hint Resolve areprograms_implies_prog_sw_sub_ts : slow.

Lemma areprograms_implies_wf_sw_sub_ts {o} :
  forall sw l (ts : list (@NTerm o)),
    areprograms ts
    -> wf_sub (sw_sub_ts sw l ts).
Proof.
  introv aps; eauto 3 with slow.
Qed.
Hint Resolve areprograms_implies_wf_sw_sub_ts : slow.

Lemma wf_sw_sub2 {o} :
  forall sw l k,
    @wf_sub o (sw_sub2 sw l k).
Proof.
  introv i; unfold sw_sub2 in *.
  apply in_combine_right_eauto in i.
  apply in_map_iff in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve wf_sw_sub2 : slow.

Lemma dom_sub_sw_sub2 {o} :
  forall sw l k,
    length l = length k
    -> @dom_sub o (sw_sub2 sw l k) = l.
Proof.
  introv len.
  unfold sw_sub2.
  rewrite dom_sub_combine_le; autorewrite with slow; auto; try omega.
Qed.

Lemma dom_sub_sw_sub_ts {o} :
  forall sw l k,
    length l = length k
    -> @dom_sub o (sw_sub_ts sw l k) = l.
Proof.
  introv len.
  unfold sw_sub_ts.
  rewrite dom_sub_combine_le; autorewrite with slow; auto; try omega.
Qed.

Lemma flat_map_sing :
  forall {A} (l : list A),
    flat_map (fun x => [x]) l = l.
Proof.
  induction l; introv; simpl; auto; try congruence.
Qed.
Hint Rewrite @flat_map_sing : slow.

Lemma sub_free_vars_sw_sub2 {o} :
  forall sw l k,
    length l = length k
    -> @sub_free_vars o (sw_sub2 sw l k) = k.
Proof.
  introv len.
  unfold sw_sub2.
  rewrite sub_free_vars_combine; autorewrite with slow; auto.
  rewrite flat_map_map; unfold compose; simpl; autorewrite with slow; auto.
Qed.

Lemma isprogram_mk_swap_cs2_sw_sub2_sw_sub_ts {o} :
  forall sw (t : @NTerm o) l k ts,
    nt_wf t
    -> areprograms ts
    -> length l = length k
    -> length k = length ts
    -> subset (free_vars t) l
    -> isprogram (lsubst (mk_swap_cs2 sw (lsubst_aux t (sw_sub2 sw l k))) (sw_sub_ts sw k ts)).
Proof.
  introv wf aps lena lenb ss.
  apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
  simpl; autorewrite with slow.
  introv i; apply free_vars_lsubst_aux_subset in i.
  rewrite dom_sub_sw_sub2 in i; auto.
  rewrite dom_sub_sw_sub_ts; auto.
  apply in_app_iff in i; repndors.

  { apply in_remove_nvars in i; repnd.
    apply ss in i0; tcsp. }

  rewrite sub_free_vars_sw_sub2 in i; auto.
Qed.
Hint Resolve isprogram_mk_swap_cs2_sw_sub2_sw_sub_ts : slow.

Lemma areprograms_implies_cl_sub {o} :
  forall l (ts : list (@NTerm o)),
    areprograms ts
    -> cl_sub (combine l ts).
Proof.
  induction l; introv aps; simpl in *; eauto 3 with slow.
  destruct ts; simpl in *; eauto 3 with slow.
  allrw @areprograms_cons; repnd.
  allrw @cl_sub_cons; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve areprograms_implies_cl_sub : slow.

Lemma disjoint_bv_sub_sw_sub {o} :
  forall sw l (t : @NTerm o),
    disjoint (bound_vars t) l
    -> disjoint_bv_sub t (sw_sub sw l).
Proof.
  introv disj i.
  apply in_map_iff in i; exrepnd; ginv; simpl in *.
  apply disjoint_singleton_l; introv j.
  apply disj in j; tcsp.
Qed.
Hint Resolve disjoint_bv_sub_sw_sub : slow.

Lemma areprograms_implies_disjoint_bv_sub {o} :
  forall (t : @NTerm o) l ts,
    areprograms ts
    -> disjoint_bv_sub t (combine l ts).
Proof.
  introv aps i.
  apply (areprograms_implies_cl_sub l) in aps.
  rw @cl_sub_eq2 in aps; apply aps in i; clear aps.
  rw i; auto.
Qed.
Hint Resolve areprograms_implies_disjoint_bv_sub : slow.

Lemma sub_bound_vars_sw_sub {o} :
  forall sw l,
    @sub_bound_vars o (sw_sub sw l) = [].
Proof.
  induction l; simpl; auto.
Qed.
Hint Rewrite @sub_bound_vars_sw_sub : slow.

Definition eq_option {o} (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => t1 = t2
    | None, None => True
    | _,_ => False
  end.

Definition ext_eq_subs {o} vs (sub1 sub2 : @Sub o) :=
  forall v,
    LIn v vs
    -> eq_option (sub_find sub1 v) (sub_find sub2 v).

Lemma eq_lsubst_aux_if_ext_eq {o} :
  forall (t : @NTerm o) sub1 sub2,
    ext_eq_subs (free_vars t) sub1 sub2
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> disjoint (bound_vars t) (sub_free_vars sub2)
    -> lsubst_aux t sub1 = lsubst_aux t sub2.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv ext d1 d2; allsimpl; auto.

  - Case "vterm".
    pose proof (ext v) as h.
    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1;
    remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2;
    allsimpl; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t].
    allsimpl.
    f_equal.

    pose proof (ind t t l i) as h; clear ind.
    autodimp h hyp; eauto 3 with slow.
    apply h.

    + introv j.
      allrw @sub_find_sub_filter_eq.
      destruct (in_deq _ deq_nvar v l) as [d|d]; boolvar; tcsp; GC.
      apply ext.
      rw lin_flat_map.
      eexists; dands; eauto.
      simpl.
      rw in_remove_nvars; sp.

    + introv j k.
      pose proof (d1 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.

    + introv j k.
      pose proof (d2 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.
Qed.

Lemma eq_option_refl {o} :
  forall (x : option (@NTerm o)),
    eq_option x x.
Proof.
  introv; destruct x; simpl; auto.
Qed.
Hint Resolve eq_option_refl : slow.

Lemma lsubst_aux_cons_not_in_eq {o} :
  forall (t : @NTerm o) v u sub,
    disjoint (bound_vars t) (free_vars u)
    -> disjoint (bound_vars t) (sub_free_vars sub)
    -> !LIn v (free_vars t)
    -> lsubst_aux t ((v, u) :: sub) = lsubst_aux t sub.
Proof.
  introv disja disjb ni.
  apply eq_lsubst_aux_if_ext_eq; simpl; eauto 3 with slow; allrw disjoint_app_r;auto.
  introv i; simpl; boolvar; tcsp; eauto 3 with slow.
Qed.

Lemma lsubst_sub_cons_r_not_in {o} :
  forall (sub1 sub2 : @Sub o) v t,
    !LIn v (sub_free_vars sub1)
    -> disjoint (sub_bound_vars sub1) (free_vars t)
    -> disjoint (sub_bound_vars sub1) (sub_free_vars sub2)
    -> lsubst_sub sub1 ((v, t) :: sub2) = lsubst_sub sub1 sub2.
Proof.
  induction sub1; introv ni disja disjb; repnd; simpl in *; auto.
  allrw in_app_iff; apply not_over_or in ni; repnd.
  allrw disjoint_app_l; repnd.
  rewrite IHsub1; auto.
  f_equal; f_equal.
  repeat (rewrite lsubst_lsubst_aux; simpl; allrw disjoint_app_r;
          allrw <- @sub_free_vars_is_flat_map_free_vars_range; dands; auto;[]).
  rewrite lsubst_aux_cons_not_in_eq; auto.
Qed.

Lemma lsubst_mk_swap_cs2_eq {o} :
  forall sw (t : @NTerm o) sub,
    lsubst (mk_swap_cs2 sw t) sub = mk_swap_cs2 sw (lsubst t sub).
Proof.
  introv.
  unfold lsubst in *; simpl in *; autorewrite with slow in *.
  boolvar; auto.
Qed.

Lemma lsubst_sub_sw_sub_as_sw_sub_ts {o} :
  forall sw l (ts : list (@NTerm o)),
    no_repeats l
    -> length l = length ts
    -> lsubst_sub (sw_sub sw l) (combine l ts) = sw_sub_ts sw l ts.
Proof.
  unfold sw_sub_ts.
  induction l; introv norep len; simpl in *; auto.
  allrw no_repeats_cons; repnd.
  destruct ts; simpl in *; tcsp; cpx.
  rewrite lsubst_sub_cons_r_not_in; autorewrite with slow; tcsp.
  rewrite IHl; auto.
  rewrite lsubst_mk_swap_cs2_eq.
  rewrite lsubst_vterm_eq_aux; simpl; boolvar; tcsp.
Qed.

Hint Rewrite @sub_free_vars_app : slow.

Lemma areprograms_implies_sub_free_vars_sw_sub_ts_nil {o} :
  forall sw l (ts : list (@NTerm o)),
    areprograms ts
    -> sub_free_vars (sw_sub_ts sw l ts) = [].
Proof.
  unfold sw_sub_ts.
  induction l; introv aps; simpl; auto.
  destruct ts; simpl; autorewrite with slow; tcsp.
  allrw @areprograms_cons; repnd.
  rewrite IHl; autorewrite with slow; auto.
  apply closed_if_program in aps0; auto.
Qed.

Lemma areprograms_implies_sub_free_vars_combine_nil {o} :
  forall l (ts : list (@NTerm o)),
    areprograms ts
    -> sub_free_vars (combine l ts) = [].
Proof.
  induction l; introv aps; simpl; auto.
  destruct ts; simpl; autorewrite with slow; tcsp.
  allrw @areprograms_cons; repnd.
  rewrite IHl; autorewrite with slow; auto.
  apply closed_if_program in aps0; auto.
Qed.

Require Export computation_preserves_utok.

Lemma sub_find_app_left {o} :
  forall (s1 s2 : @Sub o) v,
    subset (dom_sub s2) (dom_sub s1)
    -> sub_find (s1 ++ s2) v = sub_find s1 v.
Proof.
  introv ss.
  rewrite sub_find_app.
  remember (sub_find s1 v) as sf; symmetry in Heqsf; destruct sf; auto.
  remember (sub_find s2 v) as x; symmetry in Heqx; destruct x; auto.
  apply sub_find_some_implies_in_dom_sub in Heqx; apply ss in Heqx.
  apply sub_find_none2 in Heqsf; tcsp.
Qed.

Lemma sub_find_sw_sub_ts_as {o} :
  forall sw l (ts : list (@NTerm o)) v,
    sub_find (sw_sub_ts sw l ts) v
    = match sub_find (combine l ts) v with
      | Some t => Some (mk_swap_cs2 sw t)
      | None => None
      end.
Proof.
  induction l; introv; simpl; auto.
  destruct ts; simpl; auto; boolvar; tcsp.
  unfold sw_sub_ts in *.
  rewrite IHl; auto.
Qed.

Lemma in_implies_sub_find_some {o} :
  forall v l (ts : list (@NTerm o)),
    LIn v l
    -> length l = length ts
    -> {t : NTerm & LIn t ts # sub_find (combine l ts) v = Some t}.
Proof.
  induction l; introv i len; simpl in *; cpx.
  repndors; subst; tcsp; cpxpp; boolvar; tcsp; eauto.
  apply IHl in len; exrepnd; eauto.
Qed.

Lemma sub_filter_pair_dom2 {p} :
  forall lvf R lvi lnta lntb,
    length lvi = length lnta
    -> length lvi = length lntb
    -> bin_rel_nterm R lnta lntb
    -> {lvi' : list NVar
        $ { lnta', lntb' : list (@NTerm p)
        $ sub_filter (combine lvi lnta) lvf = combine lvi' lnta'
        # sub_filter (combine lvi lntb) lvf = combine lvi' lntb'
        # length lvi' = length lnta'
        # length lvi' = length lntb'
        # bin_rel_nterm R lnta' lntb'
        # lvi' = remove_nvars lvf lvi
        # subset lnta' lnta
        # subset lntb' lntb }}.
Proof.
  induction lvi as [| v lvi Hind]; introns Hl.
  { repeat (eapply existT with (x:=nil)).
    simpl in *; cpx; dands; autorewrite with slow; tcsp. }

  simpl.
  destruct lnta as [|ha lnta];invertsn Hl;
    destruct lntb as [| hb  lntb];invertsn Hl0; allsimpl.
  repeat rw memvar_dmemvar.
  apply binrel_list_cons in Hl1; repnd; duplicate Hl0.
  cases_ifd Ha; eapply Hind with (lnta := lnta) in Hl0; eauto.

  { exrepnd.
    eexists; eexists; eexists; dands; eauto; subst; try (apply subset_cons1; auto);[].
    rewrite remove_nvars_cons_r; boolvar; tcsp. }

  { exrepnd; exists (v::lvi') (ha :: lnta') (hb :: lntb').
    rewrite remove_nvars_cons_r; boolvar; tcsp.
    allsimpl; dands; spc; try (f_equal;spc); try (apply subset_cons2; auto);[].
    apply binrel_list_cons; sp. }
Qed.

Hint Resolve implies_no_repeats : slow.

Lemma subset_preserves_disjoint_flat_map_free_vars {o} :
  forall (ts1 ts2 : list (@NTerm o)) l,
    subset ts1 ts2
    -> disjoint (flat_map free_vars ts2) l
    -> disjoint (flat_map free_vars ts1) l.
Proof.
  introv h disj i j; allrw lin_flat_map; exrepnd.
  apply disj in j; auto.
  allrw lin_flat_map.
  apply h in i1; eauto.
Qed.
Hint Resolve subset_preserves_disjoint_flat_map_free_vars : slow.

Lemma lsubst_aux_sw_sub_lsubst_aux_combine_eq {o} :
  forall sw (t : @NTerm o) l ts,
    length l = length ts
    -> no_repeats l
    -> disjoint (flat_map free_vars ts) (bound_vars t)
    -> lsubst_aux (lsubst_aux t (sw_sub sw l)) (combine l ts)
       = lsubst_aux t (sw_sub_ts sw l ts).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv len norep disj.

  { simpl.
    rewrite sub_find_sw_sub; boolvar; simpl; autorewrite with slow;
      rewrite sub_find_sw_sub_ts_as;
      remember (sub_find (combine l ts) v) as sf; symmetry in Heqsf; destruct sf; auto.
    { pose proof (in_implies_sub_find_some v l ts) as q; repeat (autodimp q hyp); exrepnd.
      rewrite Heqsf in *; ginv. }
    apply sub_find_some_implies_in_dom_sub in Heqsf.
    rewrite dom_sub_combine in Heqsf; auto; tcsp. }

  simpl in *; f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  autorewrite with slow.
  unfold sw_sub_ts.

  pose proof (@sub_filter_pair_dom2 o l0 (fun a b => b = mk_swap_cs2 sw a) l ts (map (mk_swap_cs2 sw) ts)) as q.
  autorewrite with slow in q.
  repeat (autodimp q hyp).
  { apply bin_rel_nterm_if_combine; autorewrite with slow; auto.
    introv j.
    rewrite combine_map_l in j; apply in_map_iff in j; exrepnd; ginv. }
  exrepnd.
  rewrite q1, q2.
  assert (lntb' = map (mk_swap_cs2 sw) lnta') as xx.
  { rewrite <- (map_id lntb').
    apply eq_maps3; try congruence.
    introv j.
    apply (in_combine_implies_nth default_nterm default_nterm) in j; try congruence; exrepnd.
    unfold bin_rel_nterm, binrel_list in q5; repnd.
    pose proof (q5 n0) as q5; repeat (autodimp q5 hyp); try congruence. }
  subst.
  eapply ind; eauto; eauto 3 with slow;[].

  rw @disjoint_flat_map_r in disj.
  apply disj in i; simpl in *.
  allrw disjoint_app_r; repnd; tcsp; eauto 3 with slow.
Qed.

Lemma approx_mk_swap_cs2_aux1 {o} :
  forall lib sw (t : @NTerm o) v u,
    isprog u
    -> isprog_vars [v] t
    -> approx
         lib
         (mk_swap_cs2 sw (subst (push_swap_cs_sub_term sw [v] (swap_cs_term sw t)) v (mk_swap_cs2 sw u)))
         (mk_swap_cs2 sw (subst (swap_cs_term sw t) v u)).
Proof.
  introv ispu ispt.

  apply (approx_two_swap_cs2 sw); auto; eauto 3 with slow;
    repeat (first [apply isprog_swap_cs2_implies
                  |apply subst_preserves_isprog]; eauto 3 with slow).
  apply implies_two_swap_cs2_mk_swap_cs2.
  unfold subst.
  unfold push_swap_cs_sub_term.
  repeat (unflsubst; eauto 4 with slow;[]).

  applydup @closed_if_isprog in ispu as cl.

  pose proof (lsubst_aux_sw_sub_lsubst_aux_combine_eq
                sw (swap_cs_term sw t) [v] [mk_swap_cs2 sw u]) as q.
  simpl in q; autorewrite with slow in q.
  rw cl in q; repeat (autodimp q hyp).
  unfold sw_sub; simpl; rewrite q.

  apply implies_two_swap_cs2_lsubst_aux; eauto 3 with slow.
  unfold sw_sub_ts; simpl.
  constructor; auto; apply two_sw_diff; eauto 3 with slow.
Qed.

Definition nodefs_b {o} (b : @BTerm o) := get_defs_b b = [].
Definition nodefs_bs {o} (bs : list (@BTerm o)) := flat_map get_defs_b bs = [].

Lemma find_cs_value_at_if_safe_library_implies_nodefs_bs {o} :
  forall lib name k (val : @ChoiceSeqVal o) op bs,
    safe_library lib
    -> find_cs_value_at lib name k = Some val
    -> computes_to_value lib (CSVal2term val) (oterm op bs)
    -> nodefs_bs bs.
Proof.
  introv safe fcs comp.
  apply find_cs_value_at_if_safe_library in fcs; auto; repndors; exrepnd; subst; simpl in *.
  { apply computes_to_value_isvalue_eq in comp; auto.
    destruct bs; simpl in *; ginv; tcsp. }
  { destruct b; simpl in *.
    { apply computes_to_value_isvalue_eq in comp; simpl; eauto 3 with slow.
      inversion comp; subst; simpl in *; tcsp. }
    { apply computes_to_value_isvalue_eq in comp; simpl; eauto 3 with slow.
      inversion comp; subst; simpl in *; tcsp. } }
Qed.

Definition nobnd_bs {o} (bs : list (@BTerm o)) :=
  flat_map get_vars bs = [].

Lemma find_cs_value_at_if_safe_library_implies_nobnd_bs {o} :
  forall lib name k (val : @ChoiceSeqVal o) op bs,
    safe_library lib
    -> find_cs_value_at lib name k = Some val
    -> computes_to_value lib (CSVal2term val) (oterm op bs)
    -> nobnd_bs bs.
Proof.
  introv safe fcs comp.
  apply find_cs_value_at_if_safe_library in fcs; auto; repndors; exrepnd; subst; simpl in *.
  { apply computes_to_value_isvalue_eq in comp; auto.
    destruct bs; simpl in *; ginv; tcsp. }
  { destruct b; simpl in *.
    { apply computes_to_value_isvalue_eq in comp; simpl; eauto 3 with slow.
      inversion comp; subst; simpl in *; tcsp. }
    { apply computes_to_value_isvalue_eq in comp; simpl; eauto 3 with slow.
      inversion comp; subst; simpl in *; tcsp. } }
Qed.

Hint Resolve selectbt_in : slow.

Lemma isprog_bt_nil_implies_isprog {o} :
  forall (t : @NTerm o),
    isprog_bt (bterm [] t)
    -> isprog t.
Proof.
  introv isp.
  unfold isprog_bt, isprog in *; simpl in *; autorewrite with slow in *.
  allrw @wf_bterm_iff; auto.
Qed.

Lemma swap_cs_can_if_no_defs {o} :
  forall sw (can : @CanonicalOp o),
    get_defs_c can = []
    -> swap_cs_can sw can = can.
Proof.
  introv nd; destruct can; simpl in *; auto; ginv.
Qed.

Lemma swap_cs_op_if_no_defs {o} :
  forall sw (op : @Opid o),
    get_defs_o op = []
    -> swap_cs_op sw op = op.
Proof.
  introv nd; destruct op; simpl in *; auto; ginv.
  { rewrite swap_cs_can_if_no_defs; auto. }
  { destruct c; simpl in *; ginv. }
Qed.

Lemma swap_cs_term_if_no_defs {o} :
  forall sw (t : @NTerm o),
    get_defs t = []
    -> swap_cs_term sw t = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; intro nd; simpl in *; auto.
  apply app_eq_nil in nd; repnd.
  rewrite swap_cs_op_if_no_defs; auto.
  f_equal.
  apply eq_map_l; introv i; destruct x as [l t]; simpl; f_equal.
  eapply ind; eauto.
  rw @flat_map_empty in nd; apply nd in i; simpl in *; auto.
Qed.

Lemma subset_nil_implies_eq_nil :
  forall {T} (l : list T),
    subset l [] -> l = [].
Proof.
  introv ss; destruct l; auto.
  apply subset_cons_nil in ss; tcsp.
Qed.

Lemma get_defs_pushdown_fresh {o} :
  forall v (t : @NTerm o),
    get_defs (pushdown_fresh v t) = get_defs t.
Proof.
  introv; unfold pushdown_fresh; destruct t; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_defs_pushdown_fresh : slow.


Definition get_defs_utok_sub {o} (s : @utok_sub o) :=
  flat_map get_defs (utok_sub_range s).

Lemma get_defs_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) s,
    subset (get_defs (subst_utokens_aux t s)) (get_defs t ++ get_defs_utok_sub s).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; try (complete (simpl in *; auto)).
  rewrite subst_utokens_aux_oterm; simpl.
  remember (get_utok op) as k; symmetry in Heqk; destruct k; simpl.

  { unfold subst_utok.
    remember (utok_sub_find s g) as f; symmetry in Heqf; destruct f; simpl.
    { apply subset_app_l.
      apply subsetSingleFlatMap.
      apply utok_sub_find_some in Heqf.
      eapply implies_utok_sub_range; eauto. }
    { apply subset_flat_map; introv i; apply in_map_iff in i; exrepnd; subst.
      destruct a; simpl in *.
      eapply subset_trans;[eapply ind;eauto|].
      rewrite <- app_assoc.
      apply subset_app_l; apply subset_app_lr; auto.
      eapply subset_trans;[|eapply subsetSingleFlatMap;eauto].
      simpl; auto. } }

  { rewrite <- app_assoc.
    apply subset_app_lr; auto.
    apply subset_flat_map; introv i; apply in_map_iff in i; exrepnd; subst.
    destruct a; simpl in *.
    eapply subset_trans;[eapply ind;eauto|].
    apply subset_app_lr; auto.
    eapply subset_trans;[|eapply subsetSingleFlatMap;eauto].
    simpl; auto. }
Qed.

Lemma get_defs_lsubst_aux_allvars {o} :
  forall (t : @NTerm o) s,
    allvars_sub s
    -> get_defs (lsubst_aux t s) = get_defs t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv av; simpl in *.

  { remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
    apply sub_find_allvars in Heqsf; auto; exrepnd; subst; simpl; auto. }

  f_equal.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto; eauto 3 with slow.
Qed.

Lemma get_defs_lsubst_aux_is_utok {o} :
  forall (t : @NTerm o) s,
    is_utok_sub s
    -> get_defs (lsubst_aux t s) = get_defs t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv av; simpl in *.

  { remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
    apply sub_find_some_is_utok_sub_implies in Heqsf; auto.
    apply is_utok_implies in Heqsf; exrepnd; subst; simpl; auto. }

  f_equal.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto; eauto 3 with slow.
Qed.

Lemma get_defs_lsubst_is_utok {o} :
  forall (t : @NTerm o) s,
    is_utok_sub s
    -> get_defs (lsubst t s) = get_defs t.
Proof.
  introv isu.
  unflsubst.
  apply get_defs_lsubst_aux_is_utok; auto.
Qed.

Lemma alpha_eq_preserves_get_defs {o} :
  forall (t u : @NTerm o),
    alpha_eq t u
    -> get_defs t = get_defs u.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv aeq.
  { inversion aeq; subst; simpl; auto. }
  apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst.
  unfold alpha_eq_bterms in *; repnd.
  simpl; f_equal.
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup aeq0 in i.
  apply in_combine in i; repnd.
  destruct t1 as [l1 t1], t2 as [l2 t2]; simpl in *.
  inversion i0 as [? ? ? ? ? disj lena lenb norep aeq']; clear i0; subst.
  eapply ind in aeq'; eauto; autorewrite with slow; eauto 3 with slow.

  unfold lsubst in aeq'.
  repeat (rewrite flat_map_free_var_vars_range in aeq'; auto; try omega).
  apply disjoint_sym in disj.
  allrw @disjoint_app_l; repnd.
  boolvar; tcsp;[].
  repeat (rewrite get_defs_lsubst_aux_allvars in aeq'; eauto 3 with slow).
Qed.

Lemma get_defs_change_bvars_alpha {o} :
  forall l (t : @NTerm o),
    get_defs (change_bvars_alpha l t) = get_defs t.
Proof.
  introv.
  pose proof (change_bvars_alpha_spec t l) as q; simpl in q; repnd.
  apply alpha_eq_preserves_get_defs; eauto 3 with slow.
Qed.
Hint Rewrite @get_defs_change_bvars_alpha : slow.

Lemma get_defs_subst_utokens_subset {o} :
  forall (t : @NTerm o) s,
    subset (get_defs (subst_utokens t s)) (get_defs t ++ get_defs_utok_sub s).
Proof.
  introv; unfold subst_utokens; boolvar.
  { apply get_defs_subst_utokens_aux_subset. }
  { eapply subset_trans;[apply get_defs_subst_utokens_aux_subset|].
    autorewrite with slow; auto. }
Qed.

Lemma implies_get_defs_subst_utokens_nil {o} :
  forall (t : @NTerm o) s,
    get_defs t = []
    -> get_defs_utok_sub s = []
    -> get_defs (subst_utokens t s) = [].
Proof.
  introv d1 d2.
  pose proof (get_defs_subst_utokens_subset t s) as q.
  rewrite d1, d2 in q; simpl in q.
  apply subset_nil_implies_eq_nil; auto.
Qed.

Definition get_defs_sub {o} (s : @Sub o) :=
  flat_map get_defs (range s).

Lemma subset_get_defs_sub_filter {o} :
  forall l (s : @Sub o),
    subset (get_defs_sub (sub_filter s l)) (get_defs_sub s).
Proof.
  introv i.
  unfold get_defs_sub in *.
  allrw @lin_flat_map; exrepnd.
  apply range_sub_filter_subset in i1; eauto.
Qed.
Hint Resolve subset_get_defs_sub_filter : slow.

Lemma get_defs_lsubst_aux_subset {o} :
  forall (t : @NTerm o) s,
    subset (get_defs (lsubst_aux t s)) (get_defs t ++ get_defs_sub s).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl in *; auto.

  { remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
    apply subsetSingleFlatMap.
    apply sub_find_some in Heqsf.
    apply in_sub_eta in Heqsf; tcsp. }

  rewrite <- app_assoc.
  apply subset_app_lr; auto.
  apply subset_flat_map; introv i; apply in_map_iff in i; exrepnd; subst.
  destruct a; simpl in *.
  eapply subset_trans;[eapply ind;eauto|].
  apply subset_app_lr; eauto 3 with slow.
  eapply subset_trans;[|eapply subsetSingleFlatMap;eauto].
  simpl; auto.
Qed.

Lemma get_defs_lsubst_subset {o} :
  forall (t : @NTerm o) s,
    subset (get_defs (lsubst t s)) (get_defs t ++ get_defs_sub s).
Proof.
  introv.
  unfold lsubst; boolvar.
  { apply get_defs_lsubst_aux_subset. }
  { eapply subset_trans;[apply get_defs_lsubst_aux_subset|]; autorewrite with slow; auto. }
Qed.

Lemma get_defs_subst_subset {o} :
  forall (t : @NTerm o) v u,
    subset (get_defs (subst t v u)) (get_defs t ++ get_defs u).
Proof.
  introv.
  unfold subst.
  eapply subset_trans;[apply get_defs_lsubst_subset|].
  unfold get_defs_sub; simpl; autorewrite with slow; auto.
Qed.

Lemma implies_get_defs_subst_nil {o} :
  forall (t : @NTerm o) v u,
    get_defs t = []
    -> get_defs u = []
    -> get_defs (subst t v u) = [].
Proof.
  introv ha hb.
  pose proof (get_defs_subst_subset t v u) as q.
  rewrite ha, hb in q; simpl in *.
  apply subset_nil_implies_eq_nil; auto.
Qed.
Hint Resolve implies_get_defs_subst_nil : slow.

Lemma implies_get_defs_lsubst_nil {o} :
  forall (t : @NTerm o) s,
    get_defs t = []
    -> get_defs_sub s = []
    -> get_defs (lsubst t s) = [].
Proof.
  introv ha hb.
  pose proof (get_defs_lsubst_subset t s) as q.
  rewrite ha, hb in q; simpl in *.
  apply subset_nil_implies_eq_nil; auto.
Qed.
Hint Resolve implies_get_defs_lsubst_nil : slow.

Lemma implies_get_defs_lsubst_aux_nil {o} :
  forall (t : @NTerm o) s,
    get_defs t = []
    -> get_defs_sub s = []
    -> get_defs (lsubst_aux t s) = [].
Proof.
  introv ha hb.
  pose proof (get_defs_lsubst_aux_subset t s) as q.
  rewrite ha, hb in q; simpl in *.
  apply subset_nil_implies_eq_nil; auto.
Qed.
Hint Resolve implies_get_defs_lsubst_aux_nil : slow.

Lemma implies_get_defs_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    get_defs t = []
    -> get_defs_sub sub = []
    -> get_defs_sub ((v,t) :: sub) = [].
Proof.
  introv h q.
  unfold get_defs_sub in *; simpl in *; allrw; auto.
Qed.
Hint Resolve implies_get_defs_sub_cons : slow.


Lemma compute_step_preserves_no_defs {o} :
  forall lib (t v : @NTerm o),
    compute_step lib t = csuccess v
    -> get_defs t = []
    -> get_defs v = [].
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv comp nd; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|nsw|exc|abs] SCase;
    try (complete (csunf comp; simpl in *; ginv; eauto));[|].

  { SCase "NCan".
    csunf comp; simpl in *.
    dterms w; try (complete (csunf; simpl; eauto));
      autorewrite with slow in *;
      try (complete (apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
                     eapply ind in comp1; try (left; eauto); eauto 3 with slow; exrepnd; allrw; auto)).

    { apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *; auto. }

    { dopid_noncan ncan SSCase; simpl in *;
        try apply_comp_success; tcsp;
          try (complete (ginv; simpl in *; autorewrite with slow in *; allrw; auto));
          try (complete (dcwf h));
          try (complete (ginv; csunf; simpl in *; eauto)). }

    { apply compute_step_catch_success in comp; repndors; exrepnd; ginv; subst; simpl in *; auto. }

    { apply compute_step_fresh_success in comp; repeat (repndors; exrepnd; GC; ginv; subst; simpl in * );
        autorewrite with slow in *; tcsp.
      eapply ind in comp2; try (left; reflexivity); try rewrite simple_osize_subst; simpl; eauto 3 with slow.
      apply implies_get_defs_subst_utokens_nil; simpl; auto. }

    { allrw @app_eq_nil_iff; repnd.
      dopid_noncan ncan SSCase; simpl in *;
        try apply_comp_success; tcsp; repndors; exrepnd; subst; unfold nobnd in *; ginv;
          simpl in *; autorewrite with slow in *; allrw app_eq_nil_iff; repnd; eauto 4 with slow;
          try (complete (ginv; simpl in *; autorewrite with slow in *; allrw; auto));
          try (complete (dcwf h));
          try (complete (ginv; csunf; simpl in *; eauto));
          try (complete (dterms w; unfold apply_bterm; simpl; try apply implies_get_defs_subst_nil;
                         simpl; allrw app_eq_nil_iff; dands; auto)).


      { SSCase "NEApply".
        repndors; exrepnd; unfold nobnd in *; ginv.
        apply compute_step_eapply2_success in comp1; exrepnd; repndors; exrepnd; subst; simpl in *; ginv;
          unfold mk_lam, mk_choice_seq, nobnd in *; ginv; simpl in *; autorewrite with slow in *.
        unfold apply_bterm; simpl; eauto 3 with slow. }

      { SSCase "NEApply".
        simpl; allrw app_eq_nil_iff; dands; auto.
        eapply ind; eauto 3 with slow. }

      { SSCase "NSwapCs1".
        dterms w; allrw app_eq_nil_iff; repnd; auto.

        { apply compute_step_swap_cs1_aux_success_implies in comp.
          exrepnd; subst; simpl in *; autorewrite with slow in *; GC; ginv. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow.
          allrw app_eq_nil_iff; dands; auto. } }

      { SSCase "NCompOp".
        dcwf h; dterms w; simpl in *; allrw app_eq_nil_iff; repnd; tcsp.

        { apply compute_step_compop_success_can_can in comp; exrepnd; repndors; exrepnd;
            subst; simpl in *; allrw app_eq_nil_iff; repnd; GC; boolvar; tcsp. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow.
          allrw app_eq_nil_iff; dands; auto. } }

      { SSCase "NArithOp".
        dcwf h; dterms w; simpl in *; allrw app_eq_nil_iff; repnd; tcsp.

        { apply compute_step_arithop_success_can_can in comp; exrepnd; repndors; exrepnd;
            subst; simpl in *; allrw app_eq_nil_iff; repnd; GC; boolvar; tcsp. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow. }

        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          allrw app_eq_nil_iff; dands; auto.
          eapply ind; eauto; simpl; eauto 3 with slow.
          allrw app_eq_nil_iff; dands; auto. } }

      { SSCase "NCanTest".
        dterms w; autorewrite with slow in *.
        destruct (canonical_form_test_for c w4); auto. } }

    { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
      allrw app_eq_nil_iff; repnd; dands; auto.
      eapply ind; eauto; simpl; eauto 3 with slow. }

    { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
      allrw app_eq_nil_iff; repnd; dands; auto.
      eapply ind; eauto; simpl; eauto 3 with slow.
      allrw app_eq_nil_iff; dands; auto. }

    { apply compute_step_catch_success in comp; repndors; exrepnd; subst; ginv; simpl in *;
        allrw app_eq_nil_iff; repnd; dands; GC; auto; eauto 3 with slow. }

    { apply compute_step_fresh_success in comp; repnd; repndors; exrepnd; subst; ginv. } }

  { apply compute_step_NSwapCs2_success in comp; exrepnd; subst; simpl in *.
    allrw app_eq_nil_iff; repnd; GC.
    destruct nsw; simpl in *; ginv. }
Qed.

Lemma reduces_in_atmost_k_steps_preserves_no_defs {o} :
  forall lib k (t v : @NTerm o),
    reduces_in_atmost_k_steps lib t v k
    -> get_defs t = []
    -> get_defs v = [].
Proof.
  induction k; introv comp h.
  { allrw @reduces_in_atmost_k_steps_0; subst; auto. }
  allrw @reduces_in_atmost_k_steps_S;exrepnd.
  apply compute_step_preserves_no_defs in comp1; eauto.
Qed.

Lemma reduces_to_preserves_no_defs {o} :
  forall lib (t v : @NTerm o),
    reduces_to lib t v
    -> get_defs t = []
    -> get_defs v = [].
Proof.
  introv comp h; unfold reduces_to in *; exrepnd.
  eapply reduces_in_atmost_k_steps_preserves_no_defs; eauto.
Qed.

Lemma computes_to_value_preserves_no_defs {o} :
  forall lib (t v : @NTerm o),
    computes_to_value lib t v
    -> get_defs t = []
    -> get_defs v = [].
Proof.
  introv comp h; unfold computes_to_value in *; repnd.
  eapply reduces_to_preserves_no_defs; eauto.
Qed.

Lemma approx_mk_swap_cs2_no_defs {o} :
  forall lib sw (t : @NTerm o),
    get_defs t = []
    -> isprog t
    -> approx lib t (mk_swap_cs2 sw t).
Proof.
  cofix ind; introv nd isp.
  constructor; unfold close_comput; dands; auto; eauto 3 with slow;[|]; introv comp.

  { (* VAL case *)

    applydup @computes_to_value_preserves_no_defs in comp; auto.

    assert ((swap_cs_term sw t) =v>(lib) (swap_cs_term sw (oterm (Can c) tl_subterms))) as comp'.
    { repeat (rewrite swap_cs_term_if_no_defs; auto). }

    applydup @computes_to_value_isvalue in comp' as isv.
    rewrite swap_cs_term_if_no_defs in isv; auto;[].
    simpl in *; apply app_eq_nil in comp0; repnd.
    apply (isvalue_implies_isvalue_push_swap_cs_can sw) in isv.
    unfold push_swap_cs_can in isv.
    rewrite swap_cs_can_if_no_defs in isv; auto;[].

    exists (push_swap_cs_bterms sw tl_subterms); dands.

    { unfold computes_to_value in *; repnd; dands; auto;[].
      eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2;eauto|].
      autorewrite with slow.
      eapply reduces_to_if_step; csunf; simpl.
      unfold push_swap_cs_can; autorewrite with slow.
      rewrite swap_cs_can_if_no_defs; auto. }

    unfold push_swap_cs_bterms.
    unfold push_swap_cs_bterm.
    unfold push_swap_cs_sub_term.

(* Problem: the substitution will bring in some definitions/css *)

Abort.

Definition mk_boolean {o} (b : bool) : @NTerm o := if b then mk_btrue else mk_bfalse.

Lemma CSVal2term_mkc_boolean_as {o} :
  forall b, @CSVal2term o (mkc_boolean b) = mk_boolean b.
Proof.
  introv; destruct b; simpl; auto.
Qed.
Hint Rewrite @CSVal2term_mkc_boolean_as : slow.

Lemma isvalue_mk_boolean {o} :
  forall b, @isvalue o (mk_boolean b).
Proof.
  introv; destruct b; repeat constructor; simpl; introv i; repndors;
    subst; tcsp; allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve isvalue_mk_boolean : slow.

Lemma can_eq_mk_boolean_implies {o} :
  forall b c (bs : list (@BTerm o)),
    mk_boolean b = oterm (Can c) bs
    -> (c = NInj NInl [+] c = NInj NInr) # bs = [nobnd mk_axiom].
Proof.
  introv h; destruct b; simpl in *; inversion h; subst; auto.
Qed.

Hint Resolve isv_can : slow.

Lemma iscan_lam {o} :
  forall v (t : @NTerm o), iscan (mk_lam v t).
Proof.
  introv; tcsp.
Qed.
Hint Resolve iscan_lam : slow.

Lemma if_computes_to_exception_apply2 {p} :
  forall lib en f a e,
    isprogram f
    -> isprogram a
    -> computes_to_exception lib en (mk_apply f a) e
    -> {v : NVar & {b : @NTerm p & computes_to_value lib f (mk_lam v b) # computes_to_exception lib en (subst b v a) e}}
       [+] {n : choice_sequence_name & computes_to_value lib f (mk_choice_seq n) # computes_to_exception lib en a e }
       [+] {n : choice_sequence_name & {k : nat & {val : ChoiceSeqVal & computes_to_value lib f (mk_choice_seq n) # find_cs_value_at lib n k = Some val # computes_to_exception lib en (CSVal2term val) e }}}
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

    dopid o as [can|ncan|nsw|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      csunf comp1; allsimpl.
      apply compute_step_apply_success in comp1;
        repndors; exrepnd; subst; fold_terms; cpx; GC.

      { left.
        exists v b; dands; eauto.
        split; eauto 3 with slow. }

      { applydup @reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue_like in comp0; eauto 3 with slow;[].
        repndors; exrepnd; eauto.
        { right; right; left.
          exists n n0 val; dands; eauto.
          split; eauto 3 with slow. }
        { right; left.
          exists n; dands; eauto.
          split; eauto 3 with slow. } }

    + Case "NCan".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd.

      * left.
        exists v b; dands; eauto.
        split; eauto 3 with slow.

      * right; left.
        exists n0; dands; eauto.
        split; eauto 3 with slow.

      * right; right; left.
        exists n0 k0 val; dands; eauto.
        split; eauto 3 with slow.

      * right; right; right.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.

    + Case "NSwapCs2".
      unfold mk_apply, nobnd in comp1.
      rw @compute_step_ncan_nswap in comp1.
      remember (compute_step lib (oterm (NSwapCs2 nsw) l)); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.
      repndors; exrepnd.

      * left.
        exists v b; dands; eauto.
        split; eauto 3 with slow.

      * right; left.
        exists n0; dands; eauto.
        split; eauto 3 with slow.

      * right; right; left.
        exists n0 k0 val; dands; eauto.
        split; eauto 3 with slow.

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
        exists v b; dands; eauto.
        split; eauto 3 with slow.

      * right; left.
        exists n0; dands; eauto.
        split; eauto 3 with slow.

      * right; right; left.
        exists n0 k0 val; dands; eauto.
        split; eauto 3 with slow.

      * right; right; right.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n; sp.
Qed.

Lemma swap_cs2_computes_to_exception_implies {o} :
  forall lib sw (t : @NTerm o) a e,
    isprog t
    -> (mk_swap_cs2 sw t) =e>(a,lib) e
    -> {a' : NTerm & {e' : NTerm
        & ((swap_cs_term sw t) =e>(a',lib) e')
        # a = mk_swap_cs2 sw (swap_cs_term sw a')
        # e = mk_swap_cs2 sw (swap_cs_term sw e') }}.
Proof.
  introv wf comp.
  unfold computes_to_exception, reduces_to in comp; exrepnd.

  pose proof (computes_to_val_like_in_max_k_steps_swap_cs2_implies lib k sw t (mk_exception a e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
  repndors; exrepnd; subst; simpl in *; ginv.

  { apply computes_to_val_like_in_max_k_steps_if_isvalue_like in q0; eauto 3 with slow.
    inversion q0. }

  exists en e0; dands; auto.
  unfold computes_to_exception, computes_to_exception_in_max_k_steps in *.
  exists k1; auto.
Qed.

Lemma approx_apply_swap_cs2 {o} :
  forall sw lib (f t : @NTerm o),
    safe_library lib
    -> isprog f
    -> isprog t
    -> approx
         lib
         (mk_apply (mk_swap_cs2 sw f) (mk_swap_cs2 sw t))
         (mk_swap_cs2 sw (mk_apply f t)).
Proof.
  introv safe ispf ispt.
  constructor; unfold close_comput; dands; auto;
    repeat first [apply isprogram_apply| apply implies_isprogram_mk_swap_cs2];
    eauto 2 with slow; introv comp;[|].

  { (* VAL case *)

    apply if_computes_to_value_apply in comp; eauto 4 with slow;[].
    repndors; exrepnd.

    { apply swap_cs2_computes_to_value_implies in comp0; eauto 3 with slow;[].
      exrepnd.
      destruct c0; simpl in *; ginv.
      repeat (destruct bs; simpl in *; ginv).
      destruct b0; simpl in *.
      repeat (destruct l; simpl in *; ginv).
      inversion comp0; subst; clear comp0; fold_terms.
      autorewrite with slow in *.
      unfold subst in comp1.
      applydup @closed_if_isprog in ispt as clt.
      rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in comp1; simpl; autorewrite with slow;
        try (complete (rewrite clt; auto)).
      allrw @fold_subst.

      applydup @computes_to_value_isvalue in comp2 as isv.
      inversion isv as [? ispl isc]; subst; clear isv isc.
      allrw @isprogram_eq.
      allrw <- @isprog_lam_iff.

      assert (approx
                lib
                (mk_swap_cs2 sw (subst (push_swap_cs_sub_term sw [n0] (swap_cs_term sw n)) n0 (mk_swap_cs2 sw t)))
                (mk_swap_cs2 sw (subst (swap_cs_term sw n) n0 t))) as apx.
      { apply approx_mk_swap_cs2_aux1; eauto 3 with slow. }

      applydup @computes_to_value_isvalue in comp2 as isv.
      inversion isv as [? isp isc]; clear isc isv; subst.
      apply isprog_eq in isp; apply isprog_lam_iff in isp.
      eapply approx_canonical_form in apx; eauto; exrepnd.
      apply swap_cs2_computes_to_value_implies in apx1; try apply subst_preserves_isprog; eauto 3 with slow;[].
      exrepnd.
      rewrite <- subst_swap_cs_term in apx2; autorewrite with slow in *.
      unfold push_swap_cs_can in apx1; ginv; autorewrite with slow in *.

      assert (computes_to_value
                lib
                (swap_cs_term sw (mk_apply f t))
                (oterm (Can c0) bs)) as comp'.
      { unfold computes_to_value in *; repnd; dands; auto; simpl; fold_terms.
        eapply reduces_to_trans;[eapply reduces_to_prinarg;eauto|]; fold_terms.
        eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl; reflexivity|].
        unfold apply_bterm; simpl; allrw @fold_subst; auto. }

      assert (computes_to_value
                lib
                (mk_swap_cs2 sw (mk_apply f t))
                (push_swap_cs_can sw (swap_cs_can sw c0) (map (swap_cs_bterm sw) bs))) as comp''.
      { unfold computes_to_value in *; repnd; dands; eauto 3 with slow.
        eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2; eauto|].
        simpl; eapply reduces_to_if_step; csunf; simpl; auto. }

      unfold push_swap_cs_can in comp''; autorewrite with slow in comp''.
      eexists; dands; try exact comp''; auto.
      apply clearbot_relbt2; auto. }

    { apply swap_cs2_computes_to_value_implies in comp1; eauto 3 with slow;[].
      exrepnd.
      inversion comp1; autorewrite with slow in *; subst; clear comp1.
      destruct bs; simpl in *; ginv; fold_terms.
      apply eapply_choice_seq_computes_to_value_implies in comp0; exrepnd.
      apply swap_cs2_computes_to_value_implies in comp1; auto; exrepnd.
      inversion comp1; clear comp1.
      destruct bs; simpl in *; ginv.
      destruct c0; simpl in *; ginv.
      fold_terms.

      dup comp0 as nd; eapply find_cs_value_at_if_safe_library_implies_nodefs_bs in nd; eauto;[].
      dup comp0 as nb; eapply find_cs_value_at_if_safe_library_implies_nobnd_bs in nb; eauto;[].

      assert (computes_to_value
                lib
                (swap_cs_term sw (mk_apply f t))
                (oterm (Can c) tl_subterms)) as comp'.
      { unfold computes_to_value in *; repnd; dands; auto; simpl; fold_terms.
        eapply reduces_to_trans;[eapply reduces_to_prinarg;eauto|]; fold_terms.
        eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl; reflexivity|]; auto.
        eapply reduces_to_trans;[apply implies_eapply_red;[|apply reduces_to_symm|eauto]; eauto 3 with slow|].
        eapply reduces_to_trans;
          [apply reduces_to_if_step; csunf; simpl;
           unfold compute_step_eapply; simpl; boolvar; try omega; autorewrite with slow;
           allrw; try reflexivity|]; auto. }

      exists (push_swap_cs_bterms sw (map (swap_cs_bterm sw) tl_subterms)); dands; eauto 3 with slow.
      { unfold computes_to_value in *; repnd.
        apply (isvalue_implies_isvalue_push_swap_cs_can_swap sw) in comp' as isv; simpl in *.
        unfold push_swap_cs_can in isv; simpl in *; autorewrite with slow in isv.
        dands; auto; eauto 3 with slow;[].
        eapply reduces_to_trans;
          [apply implies_reduces_to_mk_swap_cs2;eauto|].
        simpl.
        eapply reduces_to_if_step.
        csunf; simpl.
        unfold push_swap_cs_can; autorewrite with slow; auto. }

      apply clearbot_relbt2.
      unfold lblift; autorewrite with slow; dands; auto.
      introv len.
      unfold push_swap_cs_bterms; autorewrite with slow.
      repeat (rewrite selectbt_map; autorewrite with slow; auto;[]).
      unfold nodefs_bs in nd; rw @flat_map_empty in nd.
      unfold nobnd_bs in nb; rw @flat_map_empty in nb.
      pose proof (nd (selectbt tl_subterms n0)) as nd; autodimp nd hyp; eauto 3 with slow;[].
      pose proof (nb (selectbt tl_subterms n0)) as nb; autodimp nb hyp; eauto 3 with slow;[].
      applydup @computes_to_value_isvalue in comp0 as isv.
      inversion isv as [? isp isc]; subst; clear isv isc.
      allrw @isprogram_eq; allrw @isprog_ot_iff; repnd; clear isp0.
      pose proof (isp (selectbt tl_subterms n0)) as isp; autodimp isp hyp; eauto 3 with slow;[].
      remember (selectbt tl_subterms n0) as b; destruct b as [l u]; simpl in *; subst.
      apply isprog_bt_nil_implies_isprog in isp.
      applydup @closed_if_isprog in isp as cl.
      unfold blift.
      eexists; eexists; eexists; dands; try apply alphaeqbt_refl.
      autorewrite with slow.
      apply cl_olift_implies_olift; eauto 2 with slow;[].
      unfold cl_olift; dands; eauto 3 with slow;
        try (apply implies_nt_wf_mk_swap_cs2; apply implies_nt_wf_swap_cs_term; eauto 3 with slow).
      introv wfs ispa ispb.
      repeat (rewrite cl_lsubst_trivial; simpl; autorewrite with slow; try rewrite cl; eauto 3 with slow;[]).
      rewrite swap_cs_term_if_no_defs; auto.

      eapply find_cs_value_at_if_safe_library in comp3; auto;[].
      repndors; exrepnd; subst; autorewrite with slow in *; simpl in *.
      { apply computes_to_value_isvalue_eq in comp0; eauto 3 with slow; inversion comp0; subst; simpl in *; tcsp. }
      { apply computes_to_value_isvalue_eq in comp0; eauto 3 with slow.
        apply can_eq_mk_boolean_implies in comp0; repnd; subst; simpl in *.
        destruct n0; simpl in *; tcsp; cpx; unfold selectbt, nobnd in *; simpl in *; ginv.
        apply reduces_to_implies_approx1; eauto 3 with slow. } } }

  { (* EXC case *)

    applydup @if_computes_to_exception_apply2 in comp; eauto 3 with slow.
    repndors; exrepnd.

    { apply swap_cs2_computes_to_value_implies in comp1; auto; exrepnd.
      destruct c; simpl in *; ginv.
      repeat (destruct bs; simpl in *; ginv).
      destruct b0; simpl in *.
      repeat (destruct l; simpl in *; ginv).
      inversion comp1; subst; clear comp1; fold_terms.
      autorewrite with slow in *.
      unfold subst in comp0.
      applydup @closed_if_isprog in ispt as clt.
      rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in comp0; simpl; autorewrite with slow;
        try (complete (rewrite clt; auto)).
      allrw @fold_subst.

      applydup @computes_to_value_isvalue in comp2 as isv.
      inversion isv as [? ispl isc]; subst; clear isv isc.
      allrw @isprogram_eq.
      allrw <- @isprog_lam_iff.

      assert (approx
                lib
                (mk_swap_cs2 sw (subst (push_swap_cs_sub_term sw [n0] (swap_cs_term sw n)) n0 (mk_swap_cs2 sw t)))
                (mk_swap_cs2 sw (subst (swap_cs_term sw n) n0 t))) as apx.
      { apply approx_mk_swap_cs2_aux1; eauto 3 with slow. }

      applydup @computes_to_value_isvalue in comp2 as isv.
      inversion isv as [? isp isc]; clear isc isv; subst.
      apply isprog_eq in isp; apply isprog_lam_iff in isp.
      eapply exception_approx in apx; eauto; exrepnd.
      repndors; try (complete (inversion apx1)); try (complete (inversion apx2)).

      apply swap_cs2_computes_to_exception_implies in apx0; try apply subst_preserves_isprog; eauto 3 with slow;[].
      exrepnd; subst.
      rewrite <- subst_swap_cs_term in apx3; autorewrite with slow in *.

      assert (computes_to_exception
                lib
                a'0
                (swap_cs_term sw (mk_apply f t))
                e'0) as comp'.
      { unfold computes_to_exception, computes_to_value in *; repnd; simpl; fold_terms.
        eapply reduces_to_trans;[eapply reduces_to_prinarg;eauto|]; fold_terms.
        eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl; reflexivity|].
        unfold apply_bterm; simpl; allrw @fold_subst; auto. }

      assert (computes_to_exception
                lib
                (mk_swap_cs2 sw (swap_cs_term sw a'0))
                (mk_swap_cs2 sw (mk_apply f t))
                (mk_swap_cs2 sw (swap_cs_term sw e'0))) as comp''.
      { unfold computes_to_exception, computes_to_value in *; repnd.
        eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2; eauto|].
        simpl; eapply reduces_to_if_step; csunf; simpl; auto.
        unfold push_swap_cs_exc; simpl; fold_terms; autorewrite with slow; auto. }

      eexists; eexists; dands; try exact comp''; auto. }

    { apply swap_cs2_computes_to_value_implies in comp0; auto; exrepnd.
      destruct c; simpl in *; ginv.
      repeat (destruct bs; simpl in *; ginv).
      inversion comp0; subst; clear comp0; fold_terms.
      apply swap_cs2_computes_to_exception_implies in comp1; auto; exrepnd; subst.

      assert (computes_to_exception
                lib
                a'
                (swap_cs_term sw (mk_apply f t))
                e') as comp'.
      { unfold computes_to_exception, computes_to_value in *; repnd; simpl; fold_terms.
        eapply reduces_to_trans;[eapply reduces_to_prinarg;eauto|]; fold_terms.
        eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl; reflexivity|].
        eapply reduces_to_trans;[apply implies_eapply_red_aux;eauto 3 with slow|].
        apply reduces_to_if_step; csunf; simpl; tcsp. }

      assert (computes_to_exception
                lib
                (mk_swap_cs2 sw (swap_cs_term sw a'))
                (mk_swap_cs2 sw (mk_apply f t))
                (mk_swap_cs2 sw (swap_cs_term sw e'))) as comp''.
      { unfold computes_to_exception, computes_to_value in *; repnd.
        eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2; eauto|].
        simpl; eapply reduces_to_if_step; csunf; simpl; auto.
        unfold push_swap_cs_exc; simpl; fold_terms; autorewrite with slow; auto. }

      applydup @preserve_program_exc2 in comp0; eauto 3 with slow; repnd.
      eexists; eexists; dands; try exact comp''; auto;
        try (left; tcsp; apply approx_refl);
          apply implies_isprogram_mk_swap_cs2; eauto 3 with slow. }

    { apply find_cs_value_at_if_safe_library in comp2; auto; repndors; exrepnd;
        subst; simpl in *; autorewrite with slow in *;
          apply iscancan_doesnt_raise_an_exception in comp1; eauto 3 with slow; tcsp. }

    { apply swap_cs2_computes_to_exception_implies in comp0; auto; exrepnd; subst.

      assert (computes_to_exception
                lib
                a'
                (swap_cs_term sw (mk_apply f t))
                e') as comp'.
      { unfold computes_to_exception, computes_to_value in *; repnd; simpl; fold_terms.
        eapply reduces_to_trans;[eapply reduces_to_prinarg;eauto|]; fold_terms.
        apply reduces_to_if_step; csunf; simpl; tcsp. }

      assert (computes_to_exception
                lib
                (mk_swap_cs2 sw (swap_cs_term sw a'))
                (mk_swap_cs2 sw (mk_apply f t))
                (mk_swap_cs2 sw (swap_cs_term sw e'))) as comp''.
      { unfold computes_to_exception, computes_to_value in *; repnd.
        eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2; eauto|].
        simpl; eapply reduces_to_if_step; csunf; simpl; auto.
        unfold push_swap_cs_exc; simpl; fold_terms; autorewrite with slow; auto. }

      applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
      eexists; eexists; dands; try exact comp''; auto;
        try (left; tcsp; apply approx_refl);
          apply implies_isprogram_mk_swap_cs2; eauto 3 with slow. } }
Qed.


Lemma lsubst_approx_star_congr_aux {p} :
  forall b lib b' lvi lnta lnta',
  approx_star lib b b'
  -> length lvi = length lnta
  -> length lvi = length lnta'
  -> disjoint (bound_vars b ++ bound_vars b') (flat_map (@free_vars p) (lnta ++ lnta'))
  -> bin_rel_nterm (approx_star lib) lnta lnta'
  -> approx_star lib (lsubst_aux b (combine lvi lnta)) (lsubst_aux b' (combine lvi lnta')).
Proof.
  nterm_ind1s b as [x|o lbt Hind] Case; introv Hap H1len H2len Hdis Hbin;
  rw flat_map_app in Hdis; duplicate Hbin as Hbb;
  apply @approx_rel_wf_sub with (lvi:=lvi) in Hbb; repnd.

  - Case "vterm".
    invertsn Hap. allsimpl.
    dsub_find xa;
      apply approx_open_lsubst_congr with (sub:= combine lvi lnta') in Hap;spcf;
      lsubst_lsubst_aux_eq_hyp X99 Hap; simpl; simpl_vlist; clear X99;
      lsubst_lsubst_aux_eq_hyp X99 Hap; simpl; simpl_vlist; clear X99;
      allsimpl; revert Hap.

    + dsub_find xa'; [|provefalse; eauto with slow].
      introv Hap. symmetry in Heqxa. symmetry in Heqxa'.
      eapply sub_find_some2_first
        in Heqxa; eauto. exrepnd. repnud Hbin. repnud Hbin.
      dimp (Hbin n);[spc;fail|].
      rewrite nth_indep with (d':= default_nterm) in Heqxa0; spc.
      rewrite nth_indep with (d':= default_nterm) in Heqxa4; spc.
      rw Heqxa0 in hyp.
      rw Heqxa4 in hyp.
      eapply approx_star_open_trans; eauto.

    + dsub_find xa'; [provefalse; eauto with slow | ].
      introv. apply approx_open_implies_approx_star.

  - Case "oterm".
    allsimpl.
    pose proof (approx_ot_change
                  lib
                  (flat_map free_vars lnta ++ flat_map free_vars lnta')
                  _ _ _ Hap) as Hao.
    exrepnd.
    rename lbtcv into lbt'. (* t' in paper *)
    apply approx_open_lsubst_congr with (sub:= combine lvi lnta') in Hao0;spcf.
    lsubst_lsubst_aux_eq_hyp X99 Hao0; simpl; simpl_vlist; clear X99;[].
    lsubst_lsubst_aux_eq_hyp X99 Hao0; simpl; simpl_vlist; clear X99;[].
    apply approx_star_open_trans with (b:=lsubst_aux (oterm o lbt') (combine lvi lnta'));spc;[].
    allsimpl.
    apply approx_open_relates_only_wf in Hao0. repnd.
    apply approx_star_congruence2;spc;[].
    clear Hao0 Hao4.
    unfold approx_starbts, lblift_sub; allunfold @blift_sub;repeat(simpl_list).
    dands; spcf.
    exrepnd. GC.
    introv Hlt. rw @selectbt_map;spc;[].  rw @selectbt_map;spc;[].
    duplicate Hlt as Hlt99. apply Hao2 in Hlt.

    pose proof (dec_op_approx_star o) as e; repndors; exrepnd.

    + pose proof (approx_star_btermd_fr
                    _ _ _ _
                    (flat_map free_vars lnta ++ flat_map free_vars lnta')
                    e
                    Hlt) as Hfb.

      exrepnd.
      exists lvn
             (lsubst_aux nt1' (sub_filter (combine lvi lnta) lvn))
             (lsubst_aux nt2' (sub_filter (combine lvi lnta') lvn)).
      dimp (selectbt_in n lbt');spcf.
      dimp (selectbt_in n lbt);spcf.
      applydup @alpha_eq_bterm_preserves_osize2 in Hfb4.
      (* needed to apply induction hyp later *)
      apply (lsubst_alphabt_congr _ _ (combine lvi lnta'))
        in Hfb5; [|allsimpl; spcls; disjoint_reasoningv;
                   apply disjoint_sym; eapply disjoint_flat_map_r in Hao1; eauto; fail].
      apply (lsubst_alphabt_congr _ _ (combine lvi lnta))
        in Hfb4; [|allsimpl; spcls; disjoint_reasoningv;
                   apply disjoint_sym in Hdis2;
                   eapply disjoint_flat_map_r in Hdis2; eauto with slow; fail].

      dands; auto;[].
      right; left.

      pose proof (exists_nrut_sub
                    lvn
                    (get_utokens_lib lib nt1'
                                 ++ get_utokens_lib lib nt2'
                                 ++ flat_map (get_utokens_lib lib) lnta
                                 ++ flat_map (get_utokens_lib lib) lnta'))
        as exnrut; exrepnd.

      pose proof (approx_star_change_nrut_sub
                    lib nt1' nt2' sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                    sub0
                    (get_utokens_lib lib nt1'
                                 ++ get_utokens_lib lib nt2'
                                 ++ flat_map (get_utokens_lib lib) lnta
                                 ++ flat_map (get_utokens_lib lib) lnta'))
           as ch.
      repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

      destruct (selectbt lbt n) as [l1 t1].
      destruct (selectbt lbt' n) as [l2 t2].
      allsimpl.

      pose proof (Hind t1 (lsubst nt1' sub0) l1) as h; repeat (autodimp h hh).
      { allrw; auto; rw @simple_osize_lsubst; eauto 3 with slow. }
      pose proof (h lib (lsubst nt2' sub0) lvi lnta lnta') as q; clear h.
      repeat (autodimp q hh).

      { repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow).
        repeat (erewrite bound_vars_lsubst_aux_nrut_sub; eauto).
        rw flat_map_app; allrw disjoint_app_l; sp. }

      repeat (rw @cl_lsubst_lsubst_aux in q; eauto 2 with slow).

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt1' sub0 (combine lvi lnta)) as e1.
      rw @sub_free_vars_combine in e1; auto.
      rw <- exnrut0 in e1.
      erewrite sub_bound_vars_nrut_sub in e1; eauto.
      erewrite sub_free_vars_nrut_sub in e1; eauto.
      allrw disjoint_app_r; allrw disjoint_app_l; repnd.
      repeat (autodimp e1 hh).

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt2' sub0 (combine lvi lnta')) as e2.
      rw @sub_free_vars_combine in e2; auto.
      rw <- exnrut0 in e2.
      erewrite sub_bound_vars_nrut_sub in e2; eauto.
      erewrite sub_free_vars_nrut_sub in e2; eauto.
      allrw disjoint_app_r; allrw disjoint_app_l; repnd.
      repeat (autodimp e2 hh).

      rw @cl_lsubst_aux_sub_trivial in e1; eauto 2 with slow.
      rw @cl_lsubst_aux_sub_trivial in e2; eauto 2 with slow.
      rw <- e1 in q; rw <- e2 in q.

      exists sub0; dands; auto.

      { repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow). }

      { eapply nrut_sub_subset;[|exact exnrut1].
        rw subset_app; dands; introv i; repeat (rw in_app_iff);
          apply get_utokens_lib_lsubst_aux in i; rw in_app_iff in i; repndors; tcsp;
            try (complete (apply in_app_iff in i; tcsp));
            apply in_get_utokens_sub in i; exrepnd; apply in_sub_keep_first in i0; repnd;
              apply sub_find_some in i2; apply in_sub_filter in i2; repnd; apply in_combine in i3; repnd.
        - right; right; left; rw lin_flat_map; eexists; dands; eauto 2 with slow.
        - right; right; right; rw lin_flat_map; eexists; dands; eauto 2 with slow.
      }

    + subst o.
      pose proof (approx_star_btermd_sw
                    _ _ _ _
                    (flat_map free_vars lnta ++ flat_map free_vars lnta')
                    Hlt) as Hfb.
      exrepnd.
      exists lvn (lsubst_aux nt1' (sub_filter (combine lvi lnta) lvn))
             (lsubst_aux nt2' (sub_filter (combine lvi lnta') lvn)).
      dimp (selectbt_in n lbt');spcf.
      dimp (selectbt_in n lbt);spcf.
      applydup @alpha_eq_bterm_preserves_osize2 in Hfb2.
      (* needed to apply induction hyp later *)
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta'))
        in Hfb3; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym; eapply disjoint_flat_map_r in Hao1; eauto; fail].
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta))
        in Hfb2; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym in Hdis2;
                     eapply disjoint_flat_map_r in Hdis2; eauto with slow; fail].

      dands; auto;[].
      right; right; dands; auto.
      eexists; dands; eauto.
SearchAbout approx_star lsubst.
Check sub_filter_pair_dom.
      dimp (sub_filter_pair_dom lvn (approx_star lib) lvi lnta lnta' ); spcf.
      exrepnd.
      rename lnta'0 into lntf.
      rename lntb' into lntf'.
      rename lvi' into lvif.
      rw hyp1.
      rw hyp3.
      destruct (selectbt lbt n) as [lv nt].
      simpl in Hfb5.

      repeat rewrite <- lsubst_aux_swap_cs_term.
      repeat rewrite swap_cs_sub_combine.
      eapply Hind; try exact hyp0; autorewrite with slow; allrw; eauto 3 with slow; try omega.

2:{
SearchAbout swap_cs_sub combine.
SearchAbout swap_cs_term lsubst_aux.
Check approx_star_congruence2.
      eapply Hind.

      eapply Hind with (nt:=nt); eauto; spc;[allrw; eauto 3 with slow|];[].
      rw flat_map_app. disjoint_reasoningv; disjoint_sub_filter.

    + pose proof (approx_star_btermd
                    _ _ _ _
                    (flat_map free_vars lnta ++ flat_map free_vars lnta')
                    e
                    Hlt) as Hfb.
      exrepnd.
      exists lvn (lsubst_aux nt1' (sub_filter (combine lvi lnta) lvn))
             (lsubst_aux nt2' (sub_filter (combine lvi lnta') lvn)).
      dimp (selectbt_in n lbt');spcf.
      dimp (selectbt_in n lbt);spcf.
      applydup @alpha_eq_bterm_preserves_osize2 in Hfb2.
      (* needed to apply induction hyp later *)
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta'))
        in Hfb3; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym; eapply disjoint_flat_map_r in Hao1; eauto; fail].
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta))
        in Hfb2; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym in Hdis2;
                     eapply disjoint_flat_map_r in Hdis2; eauto with slow; fail].

      dands; auto;[].
      left; dands; auto.
      dimp (sub_filter_pair_dom lvn (approx_star lib) lvi lnta lnta' ); spcf.
      exrepnd.
      rename lnta'0 into lntf.
      rename lntb' into lntf'.
      rename lvi' into lvif.
      rw hyp1.
      rw hyp3.
      destruct (selectbt lbt n) as [lv nt].
      simpl in Hfb5.
      eapply Hind with (nt:=nt); eauto; spc;[allrw; eauto 3 with slow|];[].
      rw flat_map_app. disjoint_reasoningv; disjoint_sub_filter.
Qed.

Lemma get_utokens_sub_combine {o} :
  forall vs (ts : list (@NTerm o)),
    length vs = length ts
    -> get_utokens_sub (combine vs ts) = flat_map get_utokens ts.
Proof.
  induction vs; destruct ts; introv len; allsimpl; tcsp; cpx.
  allrw @get_utokens_sub_cons.
  rw IHvs; auto.
Qed.

Lemma change_dom_nrut_sub {o} :
  forall (sub : @Sub o) l vs,
    nrut_sub l sub
    -> length vs = length sub
    -> {sub' : Sub
        & nrut_sub l sub'
        # range sub = range sub'
        # dom_sub sub' = vs }.
Proof.
  introv nrut len.
  exists (combine vs (range sub)).
  rw @range_combine; allrw @length_range; auto.
  rw @dom_sub_combine; allrw @length_range; auto.
  dands; auto.
  allunfold @nrut_sub; repnd.
  rw @get_utokens_sub_combine; allrw @length_range; auto.
  dands; auto.
  introv i.
  allapply in_combine; repnd.
  apply in_range in i; exrepnd.
  pose proof (nrut0 v0 t) as h; autodimp h hyp.
Qed.

Lemma cl_lsubst_approx_star_congr {o} :
  forall lib (a b : @NTerm o) sub,
    prog_sub sub
    -> approx_star lib a b
    -> approx_star lib (lsubst a sub) (lsubst_aux b sub).
Proof.
  introv pr apr.
  pose proof (lsubst_approx_star_congr_aux lib a b (dom_sub sub) (range sub) (range sub)) as h.
  allrw @length_dom; allrw @length_range.
  repeat (autodimp h hyp).
  - rw flat_map_app.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range.
    rw @sub_free_vars_if_cl_sub; simpl; eauto with slow.
  - unfold bin_rel_nterm, binrel_list; dands; auto.
    introv i.
    apply approx_star_refl.
    remember (nth n (range sub) default_nterm) as t.
    assert (LIn t (range sub)) as k.
    { subst; apply nth_in; auto. }
    apply in_range in k; exrepnd.
    pose proof (pr v t) as h; autodimp h hyp.
    destruct h as [c w]; auto.
  - allrw <- @sub_eta; auto.
    rw @cl_lsubst_lsubst_aux; eauto 2 with slow.
Qed.

(* we need it at least for subs with range as axiom for howe_lemma2 *)
Lemma approx_star_bterm_lsubst_congr {p} :
  forall lib (bt1 bt2 : BTerm) sub op,
    @prog_sub p sub
    -> approx_star_bterm op lib bt1 bt2
    -> approx_star_bterm
         op lib
         (lsubst_bterm_aux bt1 sub)
         (lsubst_bterm_aux bt2 sub).
Proof.
  introv Hpr Hs.

  destruct (dec_op_eq_fresh op) as [d|d].

  {
    pose proof (approx_star_btermd_fr
                  _ _ _ _
                  (flat_map free_vars (range sub)) d Hs) as Hfb.
    exrepnd.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range.

    unfold approx_star_bterm, blift_sub.
    exists lvn (lsubst nt1' (sub_filter sub lvn)) (lsubst nt2' (sub_filter sub lvn)).
    dands; auto;
    [|apply (lsubst_alphabt_congr _ _ sub) in Hfb4;
       allsimpl; auto;
       try (rw <- @cl_lsubst_lsubst_aux in Hfb4; eauto 3 with slow);
       allrw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_if_cl_sub; eauto with slow
     |apply (lsubst_alphabt_congr _ _ sub) in Hfb5;
       allsimpl; auto;
       try (rw <- @cl_lsubst_lsubst_aux in Hfb5; eauto 3 with slow);
       allrw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_if_cl_sub; eauto with slow].

    right.

    pose proof (exists_nrut_sub
                  lvn
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_sub sub))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub0 (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                  sub1
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_sub sub))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

    destruct bt1 as [l1 t1].
    destruct bt2 as [l2 t2].
    allsimpl.

    pose proof (cl_lsubst_approx_star_congr
                  lib (lsubst nt1' sub1) (lsubst nt2' sub1) sub) as q.
    repeat (autodimp q hyp).

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt1' sub1 sub) as e1.
    repeat (rw @sub_free_vars_if_cl_sub in e1; eauto with slow).
    repeat (autodimp e1 hh).

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt2' sub1 sub) as e2.
    repeat (rw @sub_free_vars_if_cl_sub in e2; eauto with slow).
    repeat (autodimp e2 hh).

    rw @cl_lsubst_aux_sub_trivial in e1; eauto 2 with slow.
    rw @cl_lsubst_aux_sub_trivial in e2; eauto 2 with slow.
    repeat (rw <- @cl_lsubst_lsubst_aux in e1; eauto with slow).
    repeat (rw <- @cl_lsubst_lsubst_aux in e2; eauto with slow).
    repeat (rw <- @cl_lsubst_lsubst_aux in q; eauto with slow).
    rw <- e1 in q; rw <- e2 in q; clear e1 e2.
    rw <- exnrut0 in q.

    exists sub1; dands; auto.

    { eapply nrut_sub_subset;[|exact exnrut1].
      rw subset_app; dands; introv i; repeat (rw in_app_iff);
        apply get_utokens_lib_lsubst in i; rw in_app_iff in i; repndors; tcsp;
          try (complete (apply in_app_iff in i; tcsp));
          apply in_get_utokens_sub in i; exrepnd; apply in_sub_keep_first in i0; repnd;
            apply sub_find_some in i2; apply in_sub_filter in i2; repnd;
              apply in_sub_eta in i3; repnd;
                right; right; rw lin_flat_map; eexists; dands; eauto.
    }
  }

  pose proof (approx_star_btermd
                _ _ _ _
                (flat_map free_vars (range sub)) d Hs) as Hfb.
  exrepnd.
  apply @lsubst_alphabt_congr with (sub := sub) in Hfb2;
    [| change_to_lsubst_aux4; eauto; fail].
  apply @lsubst_alphabt_congr with (sub := sub) in Hfb3;
    [| change_to_lsubst_aux4; eauto; fail].
  allsimpl.
  exists lvn (lsubst_aux nt1' (sub_filter sub lvn))
    (lsubst_aux nt2' (sub_filter sub lvn)).
  dands; sp;[].
  pose proof (sub_eta (sub_filter sub lvn)) as Xsfeta.
  pose proof (sub_eta_length (sub_filter sub lvn)) as X1len.
  remember (dom_sub (sub_filter sub lvn)) as lsvi.
  remember (range (sub_filter sub lvn)) as lsnt.
  rw Xsfeta.
  left; dands; auto.
  apply lsubst_approx_star_congr_aux;spc.
  - rw flat_map_app.
    (* the disjoint_sub_filter tactic needs the substitutions in eta form*)
    pose proof (sub_eta sub ) as Xseta.
    pose proof (sub_eta_length sub) as Xslen.
    remember (dom_sub sub) as lvi.
      remember (range sub) as lnt.
    rw Xseta in Xsfeta.
     disjoint_reasoningv; try disjoint_sub_filter.
  - unfold bin_rel_nterm, binrel_list; dands; [sp | introv Hlt].
    apply approx_star_refl. pose proof (nth_in _  _ _ default_nterm Hlt) as XX.
    rw Heqlsnt in XX.
    apply in_range in XX. exrepnd.
    apply in_sub_filter in XX0. exrepnd.
    apply Hpr in XX1.
    rw Heqlsnt. inverts XX1. sp.
Qed.

(* end hide *)

(** %\noindent \\*% The following is a generalization of Howe's lemma 1 %\cite{Howe:1989}%.
    He proved proved (needed) it for substitutions of length one.
    We need it atleast for substitutions of length upto two because
    the computation for [NSpread] performs a simultaneous subsitution
    for two variables. We prove a more general version instead. 
    Apart from some uninteresting details about substitution, our
    mechanized proof
    is essentially the same as Howe's.


*)
Lemma lsubst_approx_star_congr {p} :
  forall lib (t1 t2 : @NTerm p) (lvi : list NVar) (lnt1 lnt2 : list NTerm),
  bin_rel_nterm (approx_star lib) lnt1 lnt2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 (combine lvi lnt1)) (lsubst t2 (combine lvi lnt2)).
Proof.
  introv Hsr H1l H2l Has.
  pose proof (change_bvars_alpha_wspec 
    ((flat_map free_vars lnt1)++(flat_map free_vars lnt2)) t1) as H1f.
  exrepnd. rename ntcv into ct1.
  pose proof (change_bvars_alpha_wspec 
    ((flat_map free_vars lnt1)++(flat_map free_vars lnt2)) t2) as H2f.
  exrepnd. rename ntcv into ct2.
  assert (approx_star lib ct1 ct2) by eauto with slow. clear Has.
  apply lsubst_alpha_congr2 with (sub:=(combine lvi lnt1)) in H1f0.
  apply lsubst_alpha_congr2 with (sub:=(combine lvi lnt2)) in H2f0.
  assert (approx_star lib (lsubst ct1 (combine lvi lnt1)) (lsubst ct2 (combine lvi lnt2))) 
      ;[|eauto with slow; fail].
  clear dependent t1. clear dependent t2.
  change_to_lsubst_aux4; repeat(simpl_sub); disjoint_reasoningv.
  apply lsubst_approx_star_congr_aux; spc;[].
  spcls. rw flat_map_app. disjoint_reasoningv.
Qed.

(* begin hide *)

Lemma lsubst_approx_star_congr2 {p} : forall lib t1 t2 sub1 sub2,
  sub_range_rel (@approx_star p lib) sub1 sub2
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv Hsr Has.
  apply sub_range_rel_as_list in Hsr. exrepnd.
  subst sub1. subst sub2.
  apply lsubst_approx_star_congr; spc.
Qed.

(* weaker version than previous*)
Lemma lsubst_approx_star_congr3 {p} : forall lib t1 t2 sub,
  @wf_sub p sub
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 sub) (lsubst t2 sub).
Proof.
 introv Hw Has.
 apply lsubst_approx_star_congr2; sp;[].
 induction sub;allsimpl;spc.
 - repnud Hw. repnud Hw.  apply approx_star_refl. eapply Hw; left; eauto.
 - apply IHsub. introv Hin. repnud Hw. repnud Hw. eapply Hw; right; eauto.
Qed.

Lemma approx_starbt_change {p} :
  forall lib op bt1 bt2 (lvn : list NVar),
    op <> NCan NFresh
    -> approx_star_bterm op lib bt1 bt2
    -> no_repeats lvn
    -> length lvn = num_bvars bt1
    -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
    -> {nt1',nt2' : @NTerm p
        $ approx_star lib nt1' nt2'
        # alpha_eq_bterm bt1 (bterm lvn nt1')
        # alpha_eq_bterm bt2 (bterm lvn nt2')
       (* # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lvn *)
       }.
Proof.
  introv d Hab Hnr Hlen Hdis.
  invertsna Hab Hab.
  exrepnd; repndors; exrepnd; tcsp; GC.
  applydup @alphaeqbt_numbvars in Hab2.
  allunfold @num_bvars. allsimpl.

  dimp (alpha_bterm_pair_change3 _ _ _ _ _ lvn Hab2 Hab1); spcf;[].
  exrepnd.
  assert (approx_star lib nt1n nt2n) as XX by eauto with slow.
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  split; spc;[].
  apply approx_star_lsubst_vars;spc.
Qed.

Lemma lsubst_aux_nest_same_str2 {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst_aux (lsubst_aux t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst_aux t (filt_combine lvi lnt lf).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv Hl1 Hl2 Hnr Hdisb Hdisf; tcsp.

  { Case "vterm".

  simpl. destructr (sub_find (@filt_var_ren p lvi lvio lf) v) as [s1st|n1n].
  - apply symmetry in HeqHdeq. rename HeqHdeq into s1s.
    apply sub_find_sub_filter_some in s1s. repnd.
    apply sub_find_first in s1s0. exrepnd.
    unfold var_ren in s1s1.
    rewrite dom_sub_combine in s1s1;
     [| rewrite map_length; congruence] .
    unfold var_ren in s1s0.
    rewrite length_combine_eq
    in s1s0;[| rewrite map_length]; auto. 
    apply nth_var_ren_implies in s1s2;auto. exrepnd. rename vsr into vio.
    simpl. rewrite s1s2. simpl.
    destructr (sub_find (filt_combine lvio lnt lf) vio) as [s2st|n2n].

    + apply symmetry in HeqHdeq. rename HeqHdeq into s2s.
      apply sub_find_sub_filter_some in s2s. repnd.
      apply sub_find_first in s2s0. exrepnd.
      unfold var_ren in s2s0. rewrite length_combine_eq
      in s2s0;spc.
      rw combine_nth in s2s2;spc. inverts s2s2 as s2s3 s2s4.
      simpl. rewrite <- Hl1 in s1s0.
     (** clear s2s1. it cannot rule out case when n>n0*) 
      pose proof (no_repeats_index_unique2
               _ _ _ _ _ _ Hnr s1s0 s2s0 s1s4 s2s3) as X99.
      destruct X99. GC.  clear s1s2. clear s1st.
      destructr (sub_find (filt_combine lvi lnt lf) v) as [s3st|n3n].
      * apply symmetry in HeqHdeq. rename HeqHdeq into s3s.
        apply sub_find_sub_filter_some in s3s. repnd.
        apply sub_find_first in s3s0. exrepnd.
        unfold var_ren in s3s0. rewrite length_combine_eq
        in s3s0;spc.
        rw combine_nth in s3s2;spc. inverts s3s2 as s3s3 s3s4.
        simpl.  rewrite  Hl1 in s1s0.
        allfold (@dom_sub p). 
        allunfold (@var_ren p). spcls. 
        assert (n0<n \/ n0=n \/ n<n0) as Htri by omega.
        (dorn Htri);[|(dorn Htri)];
          try (apply s1s1 in Htri); cpx;
          try (apply s3s1 in Htri); cpx.
        destruct Htri. GC. apply nth_select3 in s3s4;[| congruence].
        apply nth_select3 in s2s4; congruence.
      * rename HeqHdeq into n3n. symmetry in n3n. 
        apply sub_find_sub_filter_none in n3n. dorn n3n; [ |sp(**see s1s*)].
        apply sub_find_none2 in n3n.        
        clear s1s1. apply nth_in2 in s1s3;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp.
    + rename HeqHdeq into n2n. symmetry in n2n.
      apply sub_find_sub_filter_none in n2n. dorn n2n.
      * apply sub_find_none2 in n2n. 
        apply nth_in2 in s1s4;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp. 
      * apply nth_in2 in s1s4;[| congruence].
        assert (disjoint lvio lf) as X99 by disjoint_reasoningv.
        apply X99 in s1s4; sp.
  - allsimpl.
    rw <- disjoint_remove_nvars_l in Hdisf.
    apply disjoint_singleton_r in Hdisf.
    allrw in_remove_nvars.
    rw (not_over_and (LIn v lvio) (!LIn v lvi) (in_deq _ deq_nvar v lvio)) in Hdisf.
    rw (not_over_not (LIn v lvi) (in_deq _ deq_nvar v lvi)) in Hdisf.
    allfold @dom_sub.
    assert ((dom_sub (combine lvi lnt)) = lvi) as Xrw  by (spcls;sp).
    rename HeqHdeq into n1n. symmetry in n1n.

    unfold filt_var_ren in n1n.
    unfold filt_combine.
    allrw @sub_find_sub_filter_eq; boolvar; tcsp.
    apply sub_find_none2 in n1n.
    rw @dom_sub_var_ren in n1n; auto.
    repndors; tcsp.
    rw @sub_find_none_if;[|rw @dom_sub_combine; auto].
    rw @sub_find_none_if;[|rw @dom_sub_combine; auto];tcsp.
  }

  { Case "oterm". (**this part is easier!!*)
    allsimpl. f_equal. rewrite map_map. eapply eq_maps; eauto.
    intros bt Hinb. destruct bt as [lv nt].
    unfold compose.
    allsimpl. apply disjoint_app_r in Hdisb. repnd.
    rename Hdisb into Hdisl.
    rename Hdisb0 into Hdisb.
    eapply disjoint_lbt_bt2 in Hdisb; eauto. repnd.
    apply disjoint_app_l in Hdisb0. repnd.
    simpl. f_equal.
    unfold filt_var_ren. unfold filt_combine.
    repeat(rewrite <- sub_filter_app_r).
    eapply Hind; eauto 3 with slow;[disjoint_reasoningv|].
    allrw <- disjoint_remove_nvars_l.
    rw disjoint_flat_map_r in Hdisf. apply Hdisf in Hinb.
    simpl in Hinb. rw <- disjoint_remove_nvars_l in Hinb.
    apply remove_nvars_unchanged in Hdisb1.
    rw remove_nvars_comm in Hinb.
    rewrite Hdisb1 in Hinb. trivial.
  }
Qed.

Lemma lsubst_nest_same_str2 {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst (lsubst t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst t (filt_combine lvi lnt lf).
Proof.
  intros.
  change_to_lsubst_aux4;
    try(apply lsubst_aux_nest_same_str2;try(sp;fail));
    apply disjoint_sym;
    rw <- @disjoint_sub_as_flat_map;
  try(apply sub_filter_sat).
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw <- @lsubst_lsubst_aux; disjoint_reasoningv.
    rw @boundvars_lsubst_vars2; spcls; disjoint_reasoningv.
    + rw @disjoint_sub_as_flat_map. spcls. sp.
    + apply allvars_sub_filter.
    + apply sub_filter_sat. rw @disjoint_sub_as_flat_map.
      spcls. disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
Qed.

Lemma lsubst_nest_same2 {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst (lsubst t (var_ren lvi lvio)) (combine lvio lnt)
     = lsubst t (combine lvi lnt).
Proof.
  intros.
  pose proof (sub_filter_nil_r (@var_ren p lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply lsubst_nest_same_str2; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma lsubst_nest_same_alpha2 {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> alpha_eq (lsubst (lsubst t (@var_ren p lvi lvio)) (combine lvio lnt))
      (lsubst t (combine lvi lnt)).
Proof.
  intros.
  pose proof (change_bvars_alpha_wspec (lvio++(flat_map free_vars lnt)) t) as Hf.
  exrepnd.
  alpharws Hf0.
  rw @lsubst_nest_same2;spc.
  alpharws (alpha_eq_sym _ _ Hf0). sp.
Qed.

Lemma approx_starbt_change_fr {p} :
  forall lib op bt1 bt2 (lvn : list NVar),
    op = NCan NFresh
    -> approx_star_bterm op lib bt1 bt2
    -> no_repeats lvn
    -> length lvn = num_bvars bt1
    -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
    -> {sub : Sub
        $ {nt1',nt2' : @NTerm p
        $ approx_star lib (lsubst nt1' sub) (lsubst nt2' sub)
        # nrut_sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2') sub
        # lvn = dom_sub sub
        # alpha_eq_bterm bt1 (bterm lvn nt1')
        # alpha_eq_bterm bt2 (bterm lvn nt2')
       (* # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lvn *)
       }}.
Proof.
  introv d Hab Hnr Hlen Hdis.
  invertsna Hab Hab.
  exrepnd; repndors; exrepnd; tcsp; GC.
  applydup @alphaeqbt_numbvars in Hab2.
  allunfold @num_bvars; allsimpl.

  assert (length x = length sub) as len.
  { subst; allrw @length_dom; auto. }

  dimp (alpha_bterm_pair_change3 _ _ _ _ _ lvn Hab2 Hab1); spcf;[].
  exrepnd.
  assert (approx_star lib (lsubst nt1n sub) (lsubst nt2n sub)) as XX by eauto with slow.
  exists (combine lvn (range sub)).
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  rw @dom_sub_combine; allrw @length_range; auto; try omega.
  subst; dands; tcsp.

  - pose proof (lsubst_nest_same_alpha2 nt1n (dom_sub sub) lvn (range sub)) as nest1.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest1 hyp); try omega.
    { apply alpha_eq_bterm_preserves_free_vars in Hab2; allsimpl.
      rw disjoint_app_r in Hdis; repnd.
      rw Hab2 in Hdis0.
      apply alphaeq_preserves_free_vars in hyp0; rw <- hyp0; auto. }
    rw <- @sub_eta in nest1.

    pose proof (lsubst_nest_same_alpha2 nt2n (dom_sub sub) lvn (range sub)) as nest2.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest2 hyp); try omega.
    { apply alpha_eq_bterm_preserves_free_vars in Hab1; allsimpl.
      rw disjoint_app_r in Hdis; repnd.
      rw Hab1 in Hdis.
      apply alphaeq_preserves_free_vars in hyp2; rw <- hyp2; auto. }
    rw <- @sub_eta in nest2.

    pose proof (lsubst_alpha_congr2 nt1 nt1n sub hyp0) as as1.
    pose proof (lsubst_alpha_congr2 nt2 nt2n sub hyp2) as as2.

    eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact nest1].
    eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact nest2].
    eauto 3 with slow.

  - apply (alphaeq_preserves_get_utokens_lib lib) in hyp0.
    apply (alphaeq_preserves_get_utokens_lib lib) in hyp2.
    repeat (rw @get_utokens_lib_lsubst_allvars; eauto with slow).
    rw <- hyp0; rw <- hyp2.
    eapply nrut_sub_change_sub_same_range;[|exact Hab5].
    rw @range_combine; auto; allrw @length_range; allrw @length_dom; auto; try omega.
Qed.

Lemma approx_star_open_bt_trans {pp} :
  forall lib op (a b c : @BTerm pp),
  approx_star_bterm op lib a b
  -> approx_open_bterm lib b c
  -> approx_star_bterm op lib a c.
Proof.
  introv Has Hao.
  applydup @blift_sub_numbvars in Has.
  pose proof (fresh_vars
                (num_bvars a)
                (free_vars_bterm a ++ free_vars_bterm b ++ free_vars_bterm c))
    as Hfr.
  exrepnd.
  destruct (dec_op_eq_fresh op) as [d|d].

  - apply @approx_starbt_change_fr with (lvn:=lvn) in Has;exrepnd; spc;[| disjoint_reasoningv].
    apply @approxbtd_change with (lvn:=lvn) in Hao;spc;[| disjoint_reasoningv].
    assert (alpha_eq_bterm (bterm lvn nt1'0) (bterm lvn nt2')) as XX by eauto with slow.
    apply alpha_eq_bterm_triv in XX.
    unfold approx_open in p0.
    rwhg XX p0.
    fold (approx_open lib nt2' nt2'0) in p0.
    dup p0 as ao.

    pose proof (exists_nrut_sub
                  lvn
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_lib lib nt1'0
                               ++ get_utokens_lib lib nt2'0))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                  sub0
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_lib lib nt1'0
                               ++ get_utokens_lib lib nt2'0))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

    apply (approx_open_lsubst_congr _ _ _ sub0) in p0; eauto 2 with slow.
    eapply approx_star_open_trans in ch; eauto.
    exists lvn nt1' nt2'0.
    dands; tcsp.
    right.

    exists sub0; dands; tcsp.
    eapply nrut_sub_subset;[|exact exnrut1]; eauto with slow.

  - apply @approx_starbt_change with (lvn:=lvn) in Has;exrepnd; spc;[| disjoint_reasoningv].
    apply @approxbtd_change with (lvn:=lvn) in Hao;spc;[| disjoint_reasoningv].
    assert (alpha_eq_bterm (bterm lvn nt1'0) (bterm lvn nt2')) as XX by eauto with slow.
    apply alpha_eq_bterm_triv in XX.
    unfold approx_open in p0.
    rwhg XX p0.
    eapply approx_star_open_trans in Has1; eauto.
    exists lvn nt1' nt2'0.
    dands; tcsp.
Qed.

(* unlike lforall, this unfolds immediately to conjunctions
    if the list is concrete. But, it might confuse tactics like eauto *)
Fixpoint lforall2 {T} (P : T -> [univ]) (l: list T) : [univ] :=
  match l with
  [] => True
  | h::t => ((P h) # (lforall2 P t))
  end.

Notation programs :=  (lforall2 isprogram).

(* end hide *)

(** %\noindent \\*% Howe implicitly uses the following lemma at least twice
    in his proofs. It is essentially a more useful way
    to eliminate (use/destruct) a hypothesis of the form
    [approx_star (oterm o lbt) b].
    The advantage here is that we additionally obtain the hypothesis
    [isprogram (oterm o lbt')]. The [lbt'] that we obtain
    by naive inductive destruction of [approx_star (oterm o lbt) b]
    need not satisify this property. This additional property
    simplifies many proofs. For example, in his proof of
    Lemma 2 (shown below), when Howe says "by Lemma 1
    and the definition of $\le$ on open terms, we may assume that
    $\theta(\overline{t''})$ is closed", he is essentially using this lemma.

    The proof of this lemma involves reasoning like that
    used in the the proof
    of [approx_open_trans].
    Essentially, we substitute arbitrary closed terms for
    free variables in [lbt'] obtained
    by the inductive destruction so that it becomes closed and show that
    this substitution has no effect when it gets applied to other terms
    in the proof. %\\*%

 *)
Lemma approx_star_otd {p} : forall lib o lbt b, 
  approx_star lib (oterm o lbt) b
  -> isprogram b
  -> isprogram (oterm o lbt) (* required near the end *)
  -> {lbt' : (list (@BTerm p))  $  isprogram (oterm o lbt') 
        # approx_open lib (oterm o lbt') b
        # length lbt = length lbt'
        # approx_starbts o lib lbt lbt'}.
Proof.
  introv Has Hisp Hispo.
  invertsna Has Hapb.
  rename lbt1' into lbt''. (* t'' in paper *)  
  unfold approx_open in Hapb1.
  repnud Hapb1.
  remember (oterm o lbt'') as tb.
  pose proof (close_with_axiom tb Hapb2) as Hpr.
  allsimpl. exrepnd.
  dimp (Hapb1 (subst_axiom (free_vars tb))); spc;
      eauto 2 with slow;[ |rw @lsubst_trivial2; auto].
  remember (subst_axiom (free_vars tb)) as subc.
  remember (lsubst tb subc) as tbc.
  rw @lsubst_trivial2 in hyp; sp.
  remember((fun t : BTerm =>
                lsubst_bterm_aux t subc)) as fc.
  exists (map fc lbt'').
  lsubst_lsubst_aux_eq_hyp Heq Heqtbc.
  rw Heqtbc in Hpr. subst tb.
  simpl in Hpr.
  rw <- Heqfc in Hpr.
  dands; try( simpl_list); spc.
  - apply approx_implies_approx_open. subst; spc.
  - unfold approx_starbts; allunfold @lblift_sub; simpl_list; exrepnd.
    dands; spcf. introv Hlt.
    applydup Hapb0 in Hlt.
    rw @selectbt_map; [| omega].
    subst fc.
    apply approx_star_bterm_lsubst_congr with (sub:=subc) in Hlt0; auto;[].
    apply isprogram_ot_iff in Hispo. repnd.
    apply selectbt_in in Hlt.
    rw @lsubst_bterm_trivial in Hlt0; eauto with slow.
Qed.

Ltac prove_isprogram :=
  match goal with
    | [ |- isprogram _ ] =>
      complete (repeat decomp_progh; show_hyps; eauto with extens;
                repeat decomp_progc; eauto with extens)
    | _ => idtac
  end.

Lemma reduces_to_implies_approx_eauto {p} :
  forall lib (t x : @NTerm p),
    isprogram t -> reduces_to lib t x -> approx lib x t.
Proof.
 introv Hp Hr.
  apply reduces_to_implies_approx in Hr; sp.
Qed.

(** %\noindent \\* % We now prove Howe's lemma 2 %\cite{Howe:1989}%. Using the lemma
    [approx_star_otd] above, this proof goes
    pretty much exactly like Howe describes.

*)

Lemma howe_lemma2 {p} :
  forall lib (c : CanonicalOp) (lbt : list BTerm) (b : @NTerm p),
    let t:= oterm (Can c) lbt in
    isprogram t
    -> isprogram b
    -> approx_star lib t b
    -> {lbt' : (list BTerm)
        & approx_starbts (Can c) lib lbt lbt'
        # computes_to_value lib b (oterm (Can c) lbt')}.
Proof.
  introv Hprt Hprb Hap.
  apply approx_star_otd in Hap;spcf;[]. exrepnd.
  rename lbt' into lbt''. (* t'' in paper *)

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose. repnud Hclose.
  dimp (Hclose2 c lbt'');
    eauto;[apply computes_to_value_isvalue_refl; constructor; eauto; fail|].
  exrepnd.
  apply clearbot_relbt in hyp0.

  rename tr_subterms into lbt'. (*( t' in the paper proof *)
  exists lbt'.
  GC. (*clear Hclose*)
  split; auto;[].
  allunfold @lblift.

  repeat (simpl_list). repnd. split; spcf;[].
  introv Hlt.
  applydup_clear Hap0 in Hlt.
  dimp (hyp0 n); try omega;[].
  clear hyp0.
  eapply approx_star_open_bt_trans; eauto.
Qed.

Lemma howe_lemma2_implies_iscan {p} :
  forall lib (t b : @NTerm p),
    isprogram t
    -> iscan t
    -> isprogram b
    -> approx_star lib t b
    -> {v : NTerm & iscan v # (b =v>(lib) v) # approx_star lib t v}.
Proof.
  introv ispt isct ispb apr.
  apply iscan_implies in isct; repndors; exrepnd; subst.
  - apply howe_lemma2 in apr; auto.
    exrepnd.
    eexists; dands; eauto.
    allunfold @approx_starbts.
    apply (apso _ _ _ _ lbt'); auto.
    { allunfold @lblift_sub; repnd; auto. }
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram; eauto 3 with slow.
Qed.

Lemma howe_lemma2_exc {p} :
  forall lib a (e b : @NTerm p),
    isprogram (mk_exception a e)
    -> isprogram b
    -> approx_star lib (mk_exception a e) b
    -> { a' , e' : NTerm
        $ approx_star lib a a'
        # approx_star lib e e'
        # computes_to_exception lib a' b e'}.
Proof.
  introv Hprt Hprb Hap.
  apply approx_star_otd in Hap;spcf;[]. exrepnd.
  rename lbt' into lbt''. (* t'' in paper *)

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose. repnud Hclose.
  allsimpl; cpx.
  applydup @isprogram_exception_implies in Hap1; exrepnd; cpx.
  dimp (Hclose3 a0 t); try (complete (apply computes_to_exception_refl; sp)); exrepnd.
  apply remove_bot_approx in hyp2.
  apply remove_bot_approx in hyp1.

  exists a' e'; sp.

  - inversion Hap0 as [? f]; allsimpl; GC.
    generalize (f 0); clear f; intro k; autodimp k hyp.
    unfold selectbt in k; simpl in k.
    destruct k as [vs k]; exrepnd; repndors; exrepnd; ginv.
    inversion k1; subst; allsimpl; cpx.
    inversion k2; subst; allsimpl; cpx.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil; GC.

    apply @approx_star_alpha_fun_l with (nt1 := nt1); auto;
    try (complete (apply alpha_eq_sym; auto)).
    apply @approx_star_open_trans with (b := nt2); auto.
    eapply approx_open_alpha_rw_l_aux; eauto.
    apply approx_implies_approx_open; auto.

  - inversion Hap0 as [? f]; allsimpl; GC.
    generalize (f 1); clear f; intro k; autodimp k hyp.
    unfold selectbt in k; simpl in k.
    destruct k as [vs k]; exrepnd; repndors; exrepnd; ginv.
    inversion k1; subst; allsimpl; cpx.
    inversion k2; subst; allsimpl; cpx.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil; GC.

    apply @approx_star_alpha_fun_l with (nt1 := nt1); auto;
    try (complete (apply alpha_eq_sym; auto)).
    apply @approx_star_open_trans with (b := nt2); auto.
    eapply approx_open_alpha_rw_l_aux; eauto.
    apply approx_implies_approx_open; auto.
Qed.

(*
Lemma howe_lemma2_mrk {p} :
  forall lib m (b : @NTerm p),
    isprogram b
    -> approx_star lib (mk_marker m) b
    -> computes_to_marker lib b m.
Proof.
  introv Hprb Hap.
  apply approx_star_otd in Hap;spcf;[|repeat constructor; simpl; complete sp]; exrepnd.
  allsimpl; cpx; fold_terms.

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose.
  repnud Hclose.
  dimp (Hclose m).
  apply compute_to_marker_mrk.
Qed.
*)

(** Informally, [howe_lemma2] looks a lot like the definition of [close_comput].
    The only difference is that [close_comput] was
    preserved when computation happens on the LHS argument.

    Recall the [approx] can be considered as a greatest fixed point
    of [close_comput]. If we could prove that [approx_star] is preserved
    when computation happens on the LHS argument, a simple coinductive
    argument will prove that [approx_star] implies
    [approx] on closed terms.
    Formally, we only need to prove the following lemma
    %\footnote{Howe did not explicitly call it Lemma 3. But he proves it
        while proving his theorem 1}% :
[[
Lemma howe_lemma3 : forall (a a' b : NTerm),
  isprogram a
  -> isprogram a'
  -> isprogram b
  -> computes_to_value a a'
  -> approx_star a b
  -> approx_star a' b.
]]

  This proof will proceed by the induction on the number of steps that
  [a] took to compute to the value [a']. Since variables don't compute to
  anything, [a] must be of the form [oterm o lbt]. The proof then proceeds
  by case analysis on [o]. Unlike the previous proofs about [approx],
  which were uniform w.r.t the [Opid]s in the language and
  only assumed that the computation system was lazy, this proof
  requires reasoning about each [Opid] in the language.

  Howe abstracts the remainder of the proof of this lemma into the
  following condition (called extensionality) that has to be proved
  for each [Opid] in the language. The last hypothesis ([Hind], the big one)
  in this definition  is essentially the induction hypothesis
  in the proof of [howe_lemma3].
*)

Definition extensional_op_ind {p} k :=
  forall lib (u u' v : @NTerm p),
    isprogram u
    -> isprogram u'
    -> isprogram v
    -> computes_to_val_like_in_max_k_steps lib u u' k
    -> approx_star lib u v
    -> approx_star lib u' v.

Definition extensional_op {p} (o : @Opid p) :=
  forall
    (lib : plibrary)
    (lbt lbt' : list BTerm)
    (a : NTerm)
    (k : nat)
    (Hpa : isprogram a)
    (Hpt : isprogram (oterm o lbt))
    (Hpt' : isprogram (oterm o lbt'))
    (Hcv : computes_to_val_like_in_max_k_steps lib (oterm o lbt) a (S k))
    (Has : lblift_sub o approx_star lib lbt lbt')
    (Hind : @extensional_op_ind p k),
    approx_star lib a (oterm o lbt').

(** %\noindent \\*% It is immediately clear that all the canonical [Opid]s of
    a lazy computation
    system are extensional.  In this case, we have [(oterm o lbt)= a] and
    the conclusion is an immediate consequence of congruence of [approx_star].


 *)
Lemma nuprl_extensional_can {p} :
  forall cop, extensional_op (@Can p cop).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  apply computes_to_val_like_in_max_k_steps_can in Hcv; subst.
  apply approx_star_congruence2;sp; eauto with slow.
Qed.

Lemma nuprl_extensional_exc {p} :
  extensional_op (@Exc p).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  apply computes_to_val_like_in_max_k_steps_exc in Hcv; subst.
  apply approx_star_congruence2;sp; eauto with slow.
Qed.

(** %\noindent% The next definition
  is just compact and equivalent
  restatement of [extensional_op_val] for
  the paper.
  Please ignore if you are reading
  the technical report. Sorry! *)

Definition extensional_opc {p} (o : @Opid p) :=
  forall lib
         (lbt lbt' : list BTerm)
         (a : NTerm)
         (k:nat),
    programs [a,(oterm o lbt),(oterm o lbt')]
    -> computes_to_value_in_max_k_steps lib (S k) (oterm o lbt) a
    -> lblift_sub o approx_star lib lbt lbt'
    -> (forall (u u' v : @NTerm p),
          programs [u,u',v]
          -> computes_to_value_in_max_k_steps lib k u u'
          -> approx_star lib u v
          -> approx_star lib u' v)
    -> approx_star lib a (oterm o lbt').

(* begin hide *)

Lemma approx_star_bterm_nobnd2 {p} :
  forall lib op a b,
    approx_star_bterm op lib (bterm [] a) (@bterm p [] b)
    -> approx_star lib a b.
Proof.
  introv Has.
  apply approx_star_bterm_nobnd in Has; exrepnd; subst; cpx.
  inversion Has1; subst; sp.
Qed.

Lemma notTrue_btchange {p} : (forall lv nt lvn,
  length lv = length lvn ->
  alpha_eq_bterm (bterm lv nt) (bterm lvn (lsubst nt (@var_ren p lv lvn))))
  -> False.
Proof.
  introv Hc.
  pose proof (Hc [nvarx,nvary] (oterm (NCan (NArithOp ArithOpAdd)) [(bterm [] (vterm nvarx)),(bterm [] (vterm nvary))])
               [nvarz,nvarz] eq_refl) as XX.
  clear Hc.
  unfold mk_apply,lsubst, nobnd in XX.
  simpl in XX.
Abort. (* apply both sides to [1,2] and compute 1 step to get sth which is not alpha equal*)
(* see btchange_alpha for the correct version*)

(*
Lemma approx_star_btermd_samevar {p} :
  forall lib op a lv bt,
    approx_star_bterm lib op (bterm lv a) bt
    -> {b : @NTerm p
        $ alpha_eq_bterm bt (bterm lv b)
        # approx_star lib a b }.
Proof.
  introv Has.
  destruct bt as [lvb b']; allsimpl.
  apply (approx_star_btermd _ _ _ (lv++lvb)) in Has.
  exrepnd.
  pose proof (change_bvars_alpha_wspec (lv++lvb) a) as Hfa.
  exrepnd. rename ntcv into a'. duplicate Hfa0. 
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfa0.
  assert (alpha_eq_bterm (bterm lv a') (bterm lvn nt1')) 
      as Xa by eauto with slow.

  pose proof (change_bvars_alpha_wspec (lvb++lv) b') as Hfb.
  exrepnd. rename ntcv into b.
  apply @alpha_eq_bterm_congr with (lv:=lvb) in Hfb0.
  assert (alpha_eq_bterm (bterm lvb b) (bterm lvn nt2')) 
      as Xb by eauto with slow.
  invertsna Xa Hb.
  invertsna Xb Ha.
  apply lsubst_alpha_congr2 with (sub:=var_ren lv3 lv) in Ha3.
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  apply lsubst_alpha_congr2 with (sub:=var_ren lv0 lv) in Hb3.
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  assert (alpha_eq a' (lsubst nt1' (var_ren lvn lv))) as Xa by eauto with slow.
  clear Hb3.
  apply approx_star_lsubst_vars with (lvi:=lvn) (lvo:=lv) in Has1;spc;[].
  exists (lsubst nt2' (var_ren lvn lv)).
  dands.
  Focus 2. eauto with slow; fail.
Abort. (* probably not true ... see above*)
*)

Lemma approx_star_btermd_1var {p} :
  forall lib op v a bt,
    approx_star_bterm lib op (bterm [v] a) bt
    -> {vr : NVar
        $ {b : @NTerm p
        $ bt = bterm [vr] b
        # approx_star_bterm lib op (bterm [v] a) (bterm [vr] b) }}.
Proof.
  introv Hab.
  destruct bt as [lvb b].
  applydup @blift_sub_numbvars in Hab.
  allunfold @num_bvars; allsimpl.
  alphahypsd.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.

Lemma approx_star_btermd_2var {p} :
  forall lib op v1 v2 a bt,
    approx_star_bterm lib op (bterm [v1, v2] a) bt
    -> {v1r,v2r : NVar
        $ {b : @NTerm p $ bt=(bterm [v1r,v2r] b)
        # approx_star_bterm lib op (bterm [v1,v2] a) (bterm [v1r,v2r] b)}}.
Proof.
  introv Hab.
  destruct bt as [lvb b].
  applydup @blift_sub_numbvars in Hab.
  allunfold @num_bvars.
  allsimpl.
  alphahypsd.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.

(*

Lemma compute_apply_decompose : forall k lbt a,
  computes_to_value_in_max_k_steps (S k) (oterm (NCan NApply) lbt) a
  -> {v : NVar $ {la b arg : NTerm $ lbt = [(bterm [] la), (bterm [] arg)
        # computes_to_value_in_max_k_steps  k la (mk_lambda v b)
        # computes_to_value_in_max_k_steps  k la (mk_lambda v b)

      ] }} *)

Hint Resolve computek_preserves_program : slow.
Ltac lsubst_nest_tac :=
  let X99 := fresh "X438590348" in
  repeat match goal with
           | [ H : (approx_star ?lib (lsubst (lsubst ?t1 (var_ren ?lv1 ?lvn)) (combine ?lvn ?lnt1)) ?rhs) |- _ ]
             => dimp (lsubst_nest_same_alpha t1 lv1 lvn lnt1);
               spc;
               disjoint_reasoningv;
               rename H into X99;
               assert (approx_star lib (lsubst t1 (combine lv1 lnt1)) rhs)
                 as H by eauto with slow; clear X99
           | [ H : (approx_star ?lib ?lhs (lsubst (lsubst ?t1 (var_ren ?lv1 ?lvn)) (combine ?lvn ?lnt1))) |- _ ]
             => dimp (lsubst_nest_same_alpha t1 lv1 lvn lnt1);
               spc;
               disjoint_reasoningv;
               rename H into X99;
               assert (approx_star lib lhs (lsubst t1 (combine lv1 lnt1)))
                 as H by eauto with slow; clear X99
         end.


(* end hide *)

(** We now begin to prove that the non-canonical [Opid]s of Nuprl are extensional.
    The following corollary of Howe's lemma 1 ([lsubst_approx_star_congr]) will
    be very useful in  of the proofs for the
   [Opid]s [NApply, NCbv, NDecide, NSpread].

 *)

Lemma apply_bterm_approx_star_congr {p} :
  forall lib op bt1 bt2 lnt1 lnt2,
    op <> NCan NFresh
    -> approx_star_bterm op lib bt1 bt2
    -> bin_rel_nterm (@approx_star p lib) lnt1 lnt2 (*enforces that the lengths are equal*)
    -> length lnt1 = num_bvars bt1 (*only required for simplicity*)
    -> length lnt1 = length lnt2 (*only required for simplicity*)
    -> approx_star lib (apply_bterm bt1 lnt1) (apply_bterm bt2 lnt2).
Proof.
  introv d Ha0 Hbr H1len H2len.
  applydup @blift_sub_numbvars in Ha0. allunfold @num_bvars.

  apply (approx_star_btermd _ _ _ _ ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2))) in Ha0; auto.
  allunfold @apply_bterm. allsimpl. exrepnd.
  destruct bt1 as [lv1 t1].
  destruct bt2 as [lv2 t2]. rename nt1' into nt1. rename nt2' into nt2.
  rename lvn into lv.
  pose proof (fresh_vars (length lv1) (all_vars nt1 ++ all_vars nt2
               ++ all_vars t1 ++ all_vars t2)).
  exrepnd. simpl in Ha1.
  apply @alphabt_change_var with (lv:=lvn) in Ha4; spc; [| disjoint_reasoningv; fail].
  apply @alphabt_change_var with (lv:=lvn) in Ha3; spc;[| disjoint_reasoningv];[].
  apply approx_star_lsubst_vars with (lvi:=lv) (lvo:=lvn) in Ha0;spc;[].
  apply alpha_eq_sym in Ha6.
  apply alpha_eq_sym in Ha7.
  assert (approx_star lib
    (lsubst t1 (var_ren lv1 lvn)) (lsubst t2 (var_ren lv2 lvn)))
       as XX by eauto with slow. (* alpha replacement *)
  allsimpl. clear Ha0.
  apply @lsubst_approx_star_congr with
      (lvi:=lvn) (lnt1:=lnt1) (lnt2:=lnt2) in XX;spc;[].

   lsubst_nest_tac.
   sp.
Qed.

(* Howe proved the extensionality of the [NApply] [Opid].
    Crary%\cite{Crary98}% proved it for many others. Our [NDecide] and
    [NCbv] are exactly same as his case and let-binding constructs.
    Our proofs of extensionality of these [Opid]s are quite close to
    their descriptions. We will only describe the proofs for

    We will now describe the proof for [NSpread]
    %\footnote{Crary's language has $\pi _1$ and $\pi _2$ constructs}%.
*)


(* begin hide *)



Lemma blift_nobnd_congr {p} : forall R t1 t2,
  R t1 t2
  -> @blift p R (bterm [] t1) (bterm [] t2).
Proof.
  introv Ht.
  exists (@nil NVar) t1 t2.
  dands; eauto with slow.
Qed.

Lemma blift_sub_nobnd_congr {o} :
  forall lib R op (t1 t2 : @NTerm o),
  R lib t1 t2
  -> blift_sub op R lib (bterm [] t1) (bterm [] t2).
Proof.
  introv Ht.
  exists (@nil NVar) t1 t2; dands; eauto with slow.
  destruct (dec_op_eq_fresh op) as [d|d]; tcsp.
  right; exists ([] : @Sub o); simpl; allrw @lsubst_nil; dands; eauto with slow.
Qed.

Hint Unfold lblift lblift_sub : slow.
Hint Resolve approx_star_congruence2 blift_nobnd_congr blift_sub_nobnd_congr : slow.

Theorem approx_star_congruence3 {p} : forall lib o lbt1 lbt2,
  approx_starbts o lib lbt1 lbt2
  -> @isprogram p (oterm o lbt2)
  -> approx_star lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps Hnt.
   apply approx_star_congruence2; sp.
   eauto with slow.
Qed.


Ltac prove_approx_star := unfold mk_apply;
match goal with
| [ |- approx_star _ ?t ?t] => apply approx_star_refl
| [  |- approx_star _ (oterm ?o _) (oterm ?o _)] =>
       apply approx_star_congruence3
| [ |- isprogram _] => repeat(decomp_progc); eauto with slow
| [  |- approx_starbts _ _ _ _ ] =>
  (unfold approx_starbts, lblift_sub; simpl; dands;[spc|];
   let Hlt := fresh "XXHlt" in
   let n := fresh "XXn" in
   intros n Hlt;
   ( let rnum := (get_lt_rhs  Hlt) in
     fail_if_not_number rnum; (*fail if not a normal form*)
     repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
  ))
| [  |- approx_star_bterm _ _ (bterm [] ?t1) (bterm [] ?t2)] =>
  apply blift_sub_nobnd_congr
| [  |- blift_sub _ approx_star _ (bterm [] ?t1) (bterm [] ?t2)] =>
  apply blift_sub_nobnd_congr
end.


Ltac duplicateas H newname :=
  let name := fresh newname
  in remember H as name;
  clears_last.





Ltac approxrelbtd :=
  match goal with
  | [H: 0 = length _ |- _ ] => symmetry in H; apply length0 in H; subst
  | [H: 1 = length _ |- _ ] => symmetry in H; apply length1 in H; exrepnd; subst
  | [H: 2 = length _ |- _ ] => symmetry in H; apply length2 in H; exrepnd; subst
  | [H: 3 = length _ |- _ ] => symmetry in H; apply length3 in H; exrepnd; subst
  | [H: 4 = length _ |- _ ] => symmetry in H; apply length4 in H; exrepnd; subst
  | [H: _ = S (length _) |- _ ] =>  inverts H as H
  | [H: (forall _:nat, (_< ?m) -> blift_sub _ _ _ _ _)  |- _ ] =>
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX); clear H
  | [H: approx_star_bterm _ _ (bterm [] _) (bterm [] _) |- _] => hide_hyp H
  | [H: blift_sub _ approx_star _ (bterm [] _) (bterm [] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: blift_sub _ approx_star _ (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: blift_sub _ approx_star _ (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [] ?nt) _ |- _] =>
    apply approx_star_bterm_nobnd in H;
      let ntr := fresh nt "r" in
      (destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ approx_star _ (bterm [] ?nt) _ |- _] =>
    apply approx_star_bterm_nobnd in H;
      let ntr := fresh nt "r" in
      (destruct H as [ntr H]);
        repnd; subst
  | [H: approx_star_bterm _ _ (bterm [?v] ?nt) _ |- _] =>
    apply approx_star_btermd_1var in H;
      let vr := fresh v "r" in
      let ntr := fresh nt "r" in
      (destruct H as [vr H]; destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ approx_star _ (bterm [?v] ?nt) _ |- _] =>
    apply approx_star_btermd_1var in H;
      let vr := fresh v "r" in
      let ntr := fresh nt "r" in
      (destruct H as [vr H]; destruct H as [ntr H]);
        repnd; subst
  | [H: approx_star_bterm _ _ (bterm [?v1, ?v2] ?nt) _ |- _] =>
    apply approx_star_btermd_2var in H;
      let v1r := fresh v1 "r" in
      let v2r := fresh v2 "r" in
      let ntr := fresh nt "r" in
      (destruct H as [v1r H]; destruct H as [v2r H]; destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ approx_star _ (bterm [?v1, ?v2] ?nt) _ |- _] =>
    apply approx_star_btermd_2var in H;
      let v1r := fresh v1 "r" in
      let v2r := fresh v2 "r" in
      let ntr := fresh nt "r" in
      (destruct H as [v1r H]; destruct H as [v2r H]; destruct H as [ntr H]);
        repnd; subst
  | [H : approx_star_bterm _ _ (bterm ?lv ?a) (bterm ?lv ?b) |- _ ] =>
    apply approx_star_samevar in H; subst
  | [H : blift (approx_star _) (bterm ?lv ?a) (bterm ?lv ?b) |- _ ] =>
    apply approx_star_samevar in H; subst
  | [H : blift _ _ _ |- _ ] => unfold blift in H; exrepnd
  end.



Hint Resolve compute_max_steps_eauto compute_max_steps_eauto2: extens.


Lemma reduces_to_implies_approx_open {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx_open lib x t # approx_open lib t x.
Proof.
  introv Hp Hr. apply reduces_to_implies_approx in Hr; auto. repnd.
  split; apply approx_implies_approx_open; auto.
Qed.

(*
    We begin by proving extensionality of the [NApply] [Opid].
    Our proof essentially follows Howe's proof. We will, however
    describe the proof to describe some details specific to our
    formalization, and also sketch the general recipe for such proofs.
%\footnote {In hind-sight, it seems possible to write an
    automated tactic that can finish these proofs}.%

    Also, the shape of [bargs] has to be
    the one that
    [(map (fun x => 0) pargs ++ map num_bvars npargs) = OpBindings (NCan op)].

      Morevover, the head [Opid] of this canonical form
      ([v]) should be compatiable with [op].
      For example, if [op = NApply],
      [c] must be [NLambda]. Similarly, if [op = NDecide], [c] must either
      be [NInl] or [NInr]. For [NCbv], [c] can be canonical [Opid].
      One can look at the definition of the [compute_step]
      function to find out such relations.
      Often, [op] is called the elim form of the intro form [c].
*)

Definition get_bterms {p} (nt:@NTerm p) : list BTerm :=
  match nt with
    | vterm v => []
    | oterm o lbt => lbt
  end.

(* use this to typecheck all the composite terms in the long comment below*)
(*
  Definition v := nvarx.
  Definition v1 := nvarx.
  Definition v2 := nvarx.
  Definition b := (vterm nvarx).
  Definition bl := (vterm nvarx).
  Definition br := (vterm nvarx).
  Definition pi1 := (vterm nvarx).
  Definition arg := (vterm nvarx).
  Definition pi2 := (vterm nvarx).
  Definition lbt := @nil BTerm.
  Definition lbtc := @nil BTerm.
  Definition lbt' := @nil BTerm.
  Definition bargs := @nil BTerm.
  Definition bargs' := @nil BTerm.
  Definition pnt := @nil NTerm.
  Definition pnt' := @nil NTerm.
  Definition pntc := @nil NTerm.
  Definition pntc' := @nil NTerm.
  Definition op := NFix.
  Definition cc := NLambda.
  Definition f := fun  l: list BTerm => (vterm nvarx).
*)

(* end hide *)

(** Howe and Crary prove extensionality of many non-canonical [Opid]s.
    Our computation system has some new ones and the operational
    semantics of some earlier ones like [NFix] is different.
    We have formally proved that all [Opid]s in our system are extensional.
    Instead of describing these proofs separately, we will describe the
    general recipe. A reader who
    wishes to delve into very concrete details can walk through
     the coq proof
    scripts for the extensionality lemmas.

    In general, whenever a computation in which an arbitrary non-cononical term
    [(oterm (NCan op) lbt)] computes to a value [a], [lbt] can be expressed as
    [(map (bterm []) pnt)++bargs], where [pnt] are the principal arguments of [op].
    The length of [pargs] depends on [op].
    For [NCompOp] and [NCanTest], it is 2 and it is 1 for the rest.
    The [S k] steps of computation from [(oterm (NCan op) (map (bterm []) pnt ++ bargs))]
    to the value [a] (see hypothesis [Hcv] in [extensional_op])
    can be split into the following three parts
    that happen one after the other.

    - Each element of [pnt] converges to some canonical [NTerm].
      At the end of this stage, the overall term is of the form
      [(oterm (NCan op) ((map (bterm []) pntc)++bargs))] such that
      elements of [pnt] converge respectively to canonical elements of [pntc].

    - One interesting step of computation happens by the interaction of
      the canonical [Opid]s in [pntc] and the corresponding non-canonical [Opid]
      [op]. Let the overall term after this step
      be [t]. Let [llbt] be [(bargs ++ (flat_map get_bterms pntc))].
      For the proof of [extensional_op (NCan op)], the key property
      here is that [t] can always be written as some [f llbt] such that
      [forall lbt1 lbt2, approx_starbts lbt1 lbt2 -> approx_star (f lbt1) (f lbt2)].
      The details of this depend on the specific [op].
      We consider all cases
      one by one. The reader might want to revisit the definition of [compute_step]
      to understand the claims below.  [op=]
      -- [NApply] : In this case, [pntc] is of the form
          [[oterm (Can NLambda) [(bterm [v] b)]]] and [bargs] is of the form
          [[bterm [] arg]] and  [t= apply_bterm (bterm [v] b) [arg]]. For this
          and the next 4 cases, the required property of [f] is a direct consequence
          of the lemma [apply_bterm_approx_star_congr] above.
      -- [NCbv] : [pntc] is of the form [[oterm (Can cc) lbtc]] and
          [bargs] is of the form [bterm [v] b].
          [t= apply_bterm (bterm [v] b) [(oterm (Can cc) lbtc)]].
      -- [NSpread] : [pntc] is of the form
          [[oterm (Can NPair) [bterm [] pi1,bterm [] pi2]]]
          and [bargs] is of the form [bterm [v1,v2] b].
          [t= apply_bterm (bterm [v1,v2] b) [pi1,pi2]]
      -- [NDecide] : [pntc] is of the form
          [[oterm (Can NInl) [bterm [] arg]]] or [[oterm (Can NInr) [bterm [] arg]]]
          and [bargs] is of the form [[bterm [v] bl,bterm [v] br]]
          and  [t= apply_bterm (bterm [v] bl) [arg]] or
          [t= apply_bterm (bterm [v] br) [arg]] depending on [pntc].
      -- [NArithOp] : [pntc] is of the form
          [[oterm (Can (Nint n1)) [], oterm (Can (Nint n2)) []]]
          and [bargs] is []. [t = oterm (Can (Nint (n1+n2))) []]
          The [f] in this case does not depend on any [BTerm]s
          (there aren't any in this case)
          and is hence a constant function.
          The same reason applies for the three cases below.
      -- [NCompOp] : and [bargs] is of the form [arg3, arg4].
          [t] is either [arg3] or [arg4] depending only on the
          head canonical [Opid]s of the [NTerm]s in [pntc]
      -- [NCanTest] : exactly same as above.
    - t converges to a.

    One key observation here is that the second part of this
    3-way split consumes exactly one step. Hence the the first and last
    parts consume at most [k] steps and hence [Hind] (in the definition
    of [extensional_op]) can be applied to
    both these parts.

    To prove [extensional_op op], we use the hypothesis [Has] to infer
    that [lbt'] can also be expressed as [(map (bterm []) pnt')++bargs']
     (see the lemma [blift_numbvars]) such that we have
     [Hasp : bin_rel_nterm approx_star pnt pnt']
     Applying [Hind] along with [Hasp] to the first stage of computation where
     [pnt] converges pointwise to [pntc],
     and  we get
    [Haspc : bin_rel_nterm approx_star pntc pnt'].
    Next, we apply
    [howe_lemma2] pointwise to [Haspc](* make a corollary? *), we get [pntc']
    such that elements of [pnt'] converges to [pntc'] respectively
    such that we have [Haspcc : bin_rel_nterm approx_star pntc pntc']

    Next, the second stage of computation happens and we get that
    [oterm (NCan op) ((map (bterm []) pntc')++bargs')] computes to some
    [t'] in exactly one step. By the property of this
    one step function [f] that we described casewise above,
    we get [Hapt : approx_star t t'].

    Finally, we apply [Hind] to the third stage again to get
    [Hapa : approx_star a t'].
    Since [oterm (NCan op) ((map (bterm []) pnt')++bargs')] reduced to
    [t'], we use the lemma [reduces_to_implies_approx_open] above to get
    [Hao : approx_open t' (oterm (NCan op) ((map (bterm []) pnt')++bargs'))]
    Now, we can use [approx_star_open_trans] on [Hapa] and [Hao] to get
    the desired conclusion of [extensional_op op].

    The concrete Coq proofs of the extensionality lemmas below follow this overall recipe.


*)

Ltac splr :=
  first [ complete sp
        | complete (left; sp; splr)
        | complete (right; sp; splr)
        ].

Ltac make_red_val_or_exc H h :=
  let hyp := fresh h in
  let T := type of H in
  match T with
    | reduces_in_atmost_k_steps ?lib ?t1 ?t2 ?k =>
      assert (computes_to_val_or_exc_in_max_k_steps lib t1 t2 k)
        as hyp
          by (split; [ complete eauto
                     | splr
                     ]
             )
  end.

Ltac make_red_val_like H h :=
  let hyp := fresh h in
  let T := type of H in
  match T with
    | reduces_in_atmost_k_steps ?lib ?t1 ?t2 ?k =>
      assert (computes_to_val_like_in_max_k_steps lib t1 t2 k)
        as hyp
          by (split; [ complete eauto
                     | splr
                     ]
             )
  end.

Lemma approx_star_exception {p} :
  forall lib (a1 a2 e1 e2 : @NTerm p),
    approx_star lib a1 a2
    -> approx_star lib e1 e2
    -> approx_star lib (mk_exception a1 e1) (mk_exception a2 e2).
Proof.
  introv ap1 ap2.
  apply approx_star_congruence; simpl; sp.
  unfold approx_starbts, lblift_sub; simpl; dands; auto; introv j.
  repeat (destruct n; cpx);
    unfold selectbt; simpl; unfold blift_sub.
  - exists ([] : list NVar) a1 a2; dands; auto; left; dands; tcsp; intro i; ginv.
  - exists ([] : list NVar) e1 e2; dands; auto; left; dands; tcsp; intro i; ginv.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma reduces_to_primarg_marker {o} :
  forall lib nc m (l bs : list (@BTerm o)) v,
    reduces_to lib (oterm (NCan nc) (nobnd (oterm (Mrk m) l) :: bs)) v
    -> v = oterm (NCan nc) (nobnd (oterm (Mrk m) l) :: bs).
Proof.
  introv comp.
  unfold reduces_to in comp; exrepnd.
  allapply @reduces_in_atmost_k_steps_primarg_marker; subst; auto.
Qed.

(* !! MOVE to approx *)
Lemma approx_ncan_primarg_marker {o} :
  forall lib ncan m l bs (t : @NTerm o),
    isprogram (oterm (NCan ncan) (nobnd (oterm (Mrk m) l) :: bs))
    -> isprogram t
    -> approx lib (oterm (NCan ncan) (nobnd (oterm (Mrk m) l) :: bs)) t.
Proof.
  introv isp1 isp2.
  unfold approx.
  constructor.
  unfold close_comput; repnd; dands; auto.

  - unfold close_compute_val; introv comp.
    unfold computes_to_value in comp; repnd.
    apply reduces_to_primarg_marker in comp0; ginv.

  - unfold close_compute_exc; introv comp.
    unfold computes_to_exception in comp; repnd.
    apply reduces_to_primarg_marker in comp; ginv.

  - unfold close_compute_mrk; introv comp.
    unfold computes_to_marker in comp; repnd.
    apply reduces_to_primarg_marker in comp; ginv.
Qed.
*)

Lemma approx_star_nat {p} :
  forall lib (t : @NTerm p) n,
    isprogram t
    -> approx_star lib (mk_nat n) t
    -> computes_to_value lib t (mk_nat n).
Proof.
  introv isp apr.
  apply howe_lemma2 in apr; fold_terms; eauto 3 with slow.
  exrepnd.
  unfold approx_starbts, lblift_sub in apr1; allsimpl; repnd; cpx.
Qed.

Lemma approx_star_choice_seq {o} :
  forall lib (t : @NTerm o) n,
    isprogram t
    -> approx_star lib (mk_choice_seq n) t
    -> computes_to_value lib t (mk_choice_seq n).
Proof.
  introv isp apr.
  apply howe_lemma2 in apr; fold_terms; fold (@mk_choice_seq o n) in *; eauto 3 with slow.
  exrepnd.
  unfold approx_starbts, lblift_sub in apr1; allsimpl; repnd; cpx.
Qed.

Lemma bin_rel_nterm_singleton {o} :
  forall (a b : @NTerm o) R,
    R a b -> bin_rel_nterm R [a] [b].
Proof.
  introv h.
  unfold bin_rel_nterm, binrel_list; dands; simpl; auto.
  introv i; destruct n; try omega; auto.
Qed.
Hint Resolve bin_rel_nterm_singleton : slow.

(* !! Move to terms2 *)
Lemma isprogram_cbv_iff2 {p} :
  forall (a : @NTerm p) v b,
    isprogram (mk_cbv a v b)
    <=> isprogram a # isprogram_bt (bterm [v] b).
Proof.
  introv.
  rw @isprogram_cbv_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  rw <- null_iff_nil.
  rw null_remove_nvars.
  rw subvars_prop.
  split; intro k; repnd; dands; auto.
  inversion k; sp.
Qed.

Lemma compute_step_cbv_iscan {o} :
  forall lib (t : @NTerm o) v u,
    iscan t
    -> compute_step lib (mk_cbv t v u) = csuccess (subst u v t).
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst; csunf; simpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma reduces_to_implies_approx_open1 {o} :
  forall lib (t x : @NTerm o),
    isprogram t
    -> reduces_to lib t x
    -> approx_open lib x t.
Proof.
  introv isp r.
  apply reduces_to_implies_approx_open in r; sp.
Qed.

Lemma compute_step_try_iscan {o} :
  forall lib (t : @NTerm o) n v u,
    iscan t
    -> compute_step lib (mk_try t n v u)
       = csuccess (mk_atom_eq n n t mk_bot).
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst; csunf; simpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma approx_star_mk_atom_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx_star lib a1 a2
    -> approx_star lib b1 b2
    -> approx_star lib c1 c2
    -> approx_star lib d1 d2
    -> approx_star lib (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv apra aprb aprc aprd.
  apply approx_star_congruence; simpl; unfold num_bvars; simpl; auto.
  unfold approx_starbts, lblift_sub; simpl; dands; auto.
  introv i.
  unfold selectbt.
  repeat (destruct n; simpl; try omega;
          try (complete (apply blift_sub_nobnd_congr; auto))).
Qed.

Lemma no_change_after_val_like3 {o} :
  forall lib (t : @NTerm o) k1 v1 k2,
    reduces_in_atmost_k_steps lib t v1 k1
    -> isprogram v1
    -> isvalue_like v1
    -> k1 <= k2
    -> reduces_in_atmost_k_steps lib t v1 k2.
Proof.
  introv r isp isv leq.
  eapply no_change_after_val_like; eauto.
Qed.

Ltac extensional_ind H k hyp :=
    match type of H with
      | reduces_in_atmost_k_steps ?lib ?t ?v ?n =>
        apply (no_change_after_val_like3 lib t n v k) in H;
          auto;
          make_red_val_like H hyp
    end.

Lemma approx_star_bterm_numvars {o} :
  forall lib op (b1 b2 : @BTerm o),
    approx_star_bterm lib op b1 b2
    -> num_bvars b1 = num_bvars b2.
Proof.
  destruct b1, b2; introv ap.
  unfold approx_star_bterm, blift_sub in ap; exrepnd.
  inversion ap2; subst.
  inversion ap0; subst.
  unfold num_bvars; simpl; omega.
Qed.

Lemma approx_starbts_numvars {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)),
    approx_starbts lib op bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; intro ap; allsimpl; auto;
  unfold approx_starbts, lblift_sub in ap; repnd; allsimpl; cpx.
  pose proof (ap 0) as h; autodimp h hyp; [omega|].
  unfold selectbt in h; allsimpl.
  apply eq_cons; [ complete (eapply approx_star_bterm_numvars; eauto)|].
  apply IHbs1.
  unfold approx_starbts, lblift_sub; dands; auto; introv k.
  pose proof (ap (S n)) as x; autodimp x hyp; omega.
Qed.


(*
Lemma extensional_apseq {p} : forall s : nseq, extensional_op (@NCan p (NApseq s)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  assert (m <= S k) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_cbv_implies; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    try (complete (csunf XX1; allsimpl; ginv));[].

    csunf XX1; allsimpl.
    apply compute_step_apseq_success in XX1; exrepnd; subst.
    allrw <- @isprogram_apseq_iff.
    apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto; [].

    unfold lblift_sub in Has; repnd; allsimpl; cpx.
    repeat(approxrelbtd); show_hyps.
    allrw <- @isprogram_apseq_iff.
    fold_terms.

    make_red_val_like Hcv3 h.
    pose proof (Hi la (mk_nat n) lar) as q.
    repeat (autodimp q hyp).
    apply howe_lemma2 in q; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in q1; repnd; allsimpl; cpx.
    clear q1.
    fold_terms.

    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    unfold computes_to_value in q0; repnd.
    eapply reduces_to_trans;[apply reduces_to_prinarg;exact q1|].
    apply reduces_to_if_step; csunf; simpl.
    rw @Znat.Nat2Z.id.
    boolvar; try omega; auto.

  - allapply @isprogram_apseq_implies; exrepnd; ginv.
    apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    apply approx_star_bterm_nobnd2 in Has0bt.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := a2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @fold_cbv.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_apseq s (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
*)


(*
(* !! MOVE to computation4 *)
Lemma computes_to_val_like_in_max_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs v,
    computes_to_val_like_in_max_k_steps
      lib
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
      v k
    -> False.
Proof.
  introv h.
  unfold computes_to_val_like_in_max_k_steps in h; repnd.
  apply reduces_in_atmost_k_steps_primarg_marker in h0; subst.
  dorn h; sp.
Qed.
*)

(*
Lemma lblift_approx_star_implies_sub_range_rel {o} :
  forall lib (bs1 bs2 : list (@BTerm o)) vars,
    lblift (approx_star lib) bs1 bs2
    -> sub_range_rel
         (approx_star lib)
         (mk_abs_subst vars bs1)
         (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; introv ap; allsimpl; auto.
  - rw @mk_abs_subst_nil_r; simpl; auto.
  - unfold lblift in ap; cpx.
  - unfold lblift in ap; cpx.
  - destruct vars; simpl; auto.
    destruct a as [l1 t1]; destruct b as [l2 t2].
    unfold lblift in ap; simpl in ap; repnd; cpx.
    pose proof (ap 0) as h; autodimp h hyp; [omega|].
    unfold selectbt in h; simpl in h.
    unfold blift in h; exrepnd.
    inversion h2; inversion h0; subst; allsimpl; cpx; GC.
    destruct l1; destruct l2; allsimpl; cpx; GC.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil.
    dands; eauto with slow.
    apply IHbs1.
    unfold lblift; dands; auto; introv k.
    pose proof (ap (S n0)) as x; autodimp x hyp; omega.
Qed.
*)

(*
Inductive so_approx_star {o} :
  @library o -> @SOTerm o -> @SOTerm o -> [univ] :=
| soapsv:
    forall lib v t2,
      so_approx_open lib (sovar v ts1) t2
      -> so_approx_star lib (sovar v ts2) t2
| soapso:
    forall lib
           (op : Opid) (t2: NTerm)
           (lbt1 lbt1' : list BTerm),
      length lbt1 = length lbt1'
      -> lblift (approx_star lib) lbt1 lbt1'
      -> approx_open lib (oterm op lbt1') t2
      -> approx_star lib (oterm op lbt1) t2.
*)

(*
Lemma computes_to_val_or_exc_in_max_k_steps_marker {o} :
  forall lib (k : nat) mrk (l : list (@BTerm o)) (v : NTerm),
    computes_to_val_or_exc_in_max_k_steps lib (oterm (Mrk mrk) l) v k
    -> False.
Proof.
  introv comp.
  unfold computes_to_val_or_exc_in_max_k_steps in comp; repnd.
  apply reduces_in_atmost_k_steps_marker in comp0; subst.
  dorn comp; sp.
Qed.
*)

(*
Lemma computes_to_val_like_in_max_k_steps_marker {o} :
  forall lib (k : nat) mrk (l : list (@BTerm o)) (v : NTerm),
    computes_to_val_like_in_max_k_steps lib (oterm (Mrk mrk) l) v k
    -> v = oterm (Mrk mrk) l.
Proof.
  induction k; introv comp.
  - rw @computes_to_val_like_in_max_k_steps_0 in comp; repnd; auto.
  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    simpl in comp1; ginv.
    apply IHk in comp0; auto.
Qed.

Lemma nuprl_extensional_mrk {p} :
  forall m : marker, @extensional_op p (Mrk m).
Proof.
  introv.
  unfold extensional_op.
  introv isp1 isp2 isp3 comp ap ext.
  apply computes_to_val_like_in_max_k_steps_marker in comp; subst.
  apply ismrk_implies in isp2; tcsp; exrepnd.
  inversion isp0; subst.
  apply ismrk_implies in isp3; tcsp; exrepnd.
  inversion isp2; subst; fold_terms.
  apply (apso _ _ _ [] []); simpl; auto; fold_terms.
  apply approx_implies_approx_open.
  unfold approx; constructor.
  unfold close_comput; dands; auto.
  - unfold close_compute_val; introv comp.
    unfold computes_to_value in comp; repnd.
    apply reduces_to_marker in comp0; tcsp.
    inversion comp0.

  - unfold close_compute_exc; introv comp.
    unfold computes_to_exception in comp; repnd.
    apply reduces_to_marker in comp; tcsp.
    inversion comp.

  - unfold close_compute_mrk; introv comp.
    unfold computes_to_marker in comp; repnd.
    apply reduces_to_marker in comp; tcsp.
    inversion comp; subst.
    apply compute_to_marker_mrk.
Qed.
*)

Lemma computes_to_val_like_in_max_k_steps_parallel_implies2 {o} :
  forall lib k (bs : list (@BTerm o)) v,
    computes_to_val_like_in_max_k_steps lib (oterm (NCan NParallel) bs) v k
    -> {x : NTerm
        & {u : NTerm
        & {bs' : list BTerm
        & {m : nat
        & k = S m
        # bs = nobnd u :: bs'
        # computes_to_val_like_in_max_k_steps lib u x m
        # {c : CanonicalOp & {bs : list BTerm & x = oterm (Can c) bs # v = mk_axiom}}
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
    dopid op as [can|ncan|nsw|exc|abs] Case; ginv.

    + Case "Can".
      apply compute_step_parallel_success in comp1; subst.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (oterm (Can can) bts) (oterm (Can can) bts) bs k; dands; auto.
      { apply computes_to_val_like_in_max_k_steps_can_iff; sp. }
      left; eexists; eexists; dands; eauto.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst; allunfold @nobnd; ginv.
      exists x (oterm (NCan ncan) bts) bs' (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists u; auto.

    + Case "NSwapCs2".
      remember (compute_step lib (oterm (NSwapCs2 nsw) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst; allunfold @nobnd; ginv.
      exists x (oterm (NSwapCs2 nsw) bts) bs' (S m); dands; auto.
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

Lemma isprogram_comp_seq1_implies_ex {o} :
  forall a (l : list (@BTerm o)),
    isprogram (oterm (NCan (NCompSeq1 a)) l)
    -> {t1 : NTerm & {t2 : NTerm
        & l = [nobnd t1, nobnd t2]
        # isprogram t1
        # isprogram t2}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  destruct l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Lemma isprogram_comp_seq2_implies_ex {o} :
  forall nfo (l : list (@BTerm o)),
    isprogram (oterm (NCan (NCompSeq2 nfo)) l)
    -> {t1 : NTerm & {t2 : NTerm
        & l = [nobnd t1, nobnd t2]
        # isprogram t1
        # isprogram t2}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  destruct l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Lemma isprogram_comp_seq1_implies {o} :
  forall a (b c : @NTerm o),
    isprogram (mk_comp_seq1 a b c)
    -> (isprogram b # isprogram c).
Proof.
  introv isp.
  apply isprogram_comp_seq1_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma isprogram_comp_seq2_implies {o} :
  forall z l k (a b : @NTerm o),
    isprogram (mk_comp_seq2 z l k a b)
    -> (isprogram a # isprogram b).
Proof.
  introv isp.
  apply isprogram_comp_seq2_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_isvalue_implies {o} :
  forall lib k (a b : @NTerm o),
    reduces_in_atmost_k_steps lib a b k
    -> isvalue a
    -> b = a.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    rewrite compute_step_value in comp1; auto; ginv.
    apply IHk in comp0; auto.
Qed.

Lemma isvalue_mk_fresh_choice_nat_seq {o} :
  forall n (lib : @plibrary o) l,
    isvalue (mk_fresh_choice_nat_seq n lib l).
Proof.
  introv.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isvalue_mk_fresh_choice_nat_seq : slow.

Lemma implies_isprogram_mk_comp_seq2 {o} :
  forall n l i (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_comp_seq2 n l i a b).
Proof.
  introv ispa ispb.
  unfold isprogram, closed in *; repnd; simpl in *.
  allrw; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_comp_seq2 : slow.

Lemma approx_star_bterm_nobnd_iff {o} :
  forall lib (op : Opid) (a b : @NTerm o),
    approx_star_bterm op lib (bterm [] a) (bterm [] b) <=> approx_star lib a b.
Proof.
  introv; split; intro h.
  - eapply approx_star_bterm_nobnd2; eauto.
  - unfold approx_star_bterm, blift_sub; simpl.
    exists ([] : list NVar) a b; dands; auto.
    destruct (dec_op_eq_fresh op); subst; tcsp.
    right.
    exists ([] : @Sub o); dands; autorewrite with slow; tcsp; eauto 3 with slow.
Qed.

Lemma approx_starbts_nil {o} :
  forall (lib : @plibrary o) nc, approx_starbts nc lib [] [].
Proof.
  introv; unfold approx_starbts, lblift_sub; simpl; dands; tcsp.
Qed.
Hint Resolve approx_starbts_nil : slow.

Lemma implies_approx_star_mk_comp_seq2 {o} :
  forall lib n l i (a b c d : @NTerm o),
    approx_star lib a c
    -> approx_star lib b d
    -> approx_star lib (mk_comp_seq2 n l i a b) (mk_comp_seq2 n l i c d).
Proof.
  introv apra aprb.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_comp_seq2 : slow.

Lemma implies_approx_star_mk_apply {o} :
  forall lib (a b c d : @NTerm o),
    approx_star lib a c
    -> approx_star lib b d
    -> approx_star lib (mk_apply a b) (mk_apply c d).
Proof.
  introv apra aprb.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_apply : slow.

Lemma implies_approx_star_mk_zero {o} :
  forall (lib : @plibrary o),
    approx_star lib mk_zero mk_zero.
Proof.
  introv.
  apply approx_star_congruence; simpl; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_zero : slow.

Hint Resolve isprogram_mk_nat : slow.

Lemma implies_approx_star_mk_nat {o} :
  forall (lib : @plibrary o) k,
    approx_star lib (mk_nat k) (mk_nat k).
Proof.
  introv.
  apply approx_star_congruence; simpl; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_nat : slow.

Lemma isprogram_ldepth_implies {o} :
  forall (bs : list (@BTerm o)),
    isprogram (oterm (NCan NLDepth) bs) -> bs = [].
Proof.
  introv h.
  inversion h as [cl wf]; subst; simpl in *.
  inversion wf; subst; simpl in *; destruct bs; simpl in *; ginv.
Qed.
