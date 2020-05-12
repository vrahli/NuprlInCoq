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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms5.
Require Export terms_tacs.
Require Export terms_choice.
Require Export computation.


Hint Rewrite remove_nvars_nil_l : slow.
Hint Rewrite app_nil_r : slow.


Lemma isprogram_swap_cs2_implies {p} :
  forall nfo (bterms : list (@BTerm p)),
    isprogram (oterm (NSwapCs2 nfo) bterms)
    -> {a : NTerm $ bterms = [bterm [] a] # isprogram a }.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; simpl in *; ginv.
  destruct l; simpl in *; ginv.
  eexists; dands; eauto; dLin_hyp; allapply @isprogram_bt_nobnd; auto.
Qed.

Lemma isprogram_swap_cs1_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NSwapCs1) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c]
           # isprogram a
           # isprogram b
           # isprogram c }}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b, b0, b1; simpl in *; ginv.
  destruct l, l0, l1; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto;
    dLin_hyp; allapply @isprogram_bt_nobnd; auto.
Qed.

Lemma isprogram_swap_cs1_iff {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NSwapCs1) bterms)
    <=> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
        $ bterms = [bterm [] a, bterm [] b, bterm [] c]
        # isprogram a
        # isprogram b
        # isprogram c }}}.
Proof.
  introv; split; intro k.
  apply isprogram_swap_cs1_implies in k; auto.
  exrepnd; subst.
  apply isprogram_ot_iff; unfold num_bvars; simpl; sp; subst;
    apply implies_isprogram_bt0; auto.
Qed.

Lemma wf_swap_cs2 {o} :
  forall sw (a : @NTerm o),
    wf_term (mk_swap_cs2 sw a) <=> wf_term a.
Proof.
  introv; rw @wf_oterm_iff; simpl.
  split; intro h; repnd; dands; tcsp.
  { dLin_hyp; allrw @wf_bterm_iff; auto. }
  { introv i; repndors; subst; tcsp. }
Qed.

Lemma isprog_swap_cs2 {o} :
  forall sw (a : @NTerm o),
    isprog (mk_swap_cs2 sw a) <=> isprog a.
Proof.
  introv.
  unfold isprog; simpl; autorewrite with slow.
  rw @wf_swap_cs2; tcsp.
Qed.

Lemma isprog_swap_cs2_implies {o} :
  forall sw (a : @NTerm o),
    isprog a
    -> isprog (mk_swap_cs2 sw a).
Proof.
  introv ispa; apply isprog_swap_cs2; sp.
Qed.

Lemma implies_isprog_vars_mk_swap_cs1 {o} :
  forall l n1 n2 (t : @NTerm o),
    isprog_vars l n1
    -> isprog_vars l n2
    -> isprog_vars l t
    -> isprog_vars l (mk_swap_cs1 n1 n2 t).
Proof.
  introv ispa ipsb ispc.
  unfold mk_swap_cs1; apply isprog_vars_ot_iff; simpl; dands; tcsp.
  introv i; repndors; subst; tcsp; unfold nobnd in *; ginv; autorewrite with slow; auto.
Qed.
Hint Resolve implies_isprog_vars_mk_swap_cs1 : slow.

Lemma implies_isprog_vars_mk_swap_cs2 {o} :
  forall l sw (t : @NTerm o),
    isprog_vars l t
    -> isprog_vars l (mk_swap_cs2 sw t).
Proof.
  introv ispa.
  unfold mk_swap_cs2; apply isprog_vars_ot_iff; simpl; dands; tcsp.
  introv i; repndors; subst; tcsp; unfold nobnd in *; ginv; autorewrite with slow; auto.
Qed.
Hint Resolve implies_isprog_vars_mk_swap_cs2 : slow.

Lemma implies_isprogram_mk_swap_cs1 {o} :
  forall n1 n2 (t : @NTerm o),
    isprogram n1
    -> isprogram n2
    -> isprogram t
    -> isprogram (mk_swap_cs1 n1 n2 t).
Proof.
  introv ispa ipsb ispc.
  allrw @isprogram_eq; allrw @isprog_vars_nil_iff_isprog; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_swap_cs1 : slow.

Lemma implies_isprogram_mk_swap_cs2 {o} :
  forall sw (t : @NTerm o),
    isprogram t
    -> isprogram (mk_swap_cs2 sw t).
Proof.
  introv ispa.
  allrw @isprogram_eq; allrw @isprog_vars_nil_iff_isprog; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_swap_cs2 : slow.

Lemma isprog_vars_mk_choice_seq {o} :
  forall l n, @isprog_vars o l (mk_choice_seq n).
Proof.
  introv; apply isprog_vars_ot_iff; simpl; dands; tcsp.
Qed.
Hint Resolve isprog_vars_mk_choice_seq : slow.

Lemma nt_wf_mk_swap_cs1_implies {o} :
  forall (a b c : @NTerm o),
    nt_wf (mk_swap_cs1 a b c)
    -> nt_wf a # nt_wf b # nt_wf c.
Proof.
  introv wf.
  unfold mk_swap_cs1 in *.
  allrw @nt_wf_oterm_iff; autorewrite with slow in *; repnd; dands; auto;
    simpl in *; dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_mk_swap_cs2_implies {o} :
  forall sw (c : @NTerm o),
    nt_wf (mk_swap_cs2 sw c)
    -> nt_wf c.
Proof.
  introv wf.
  unfold mk_swap_cs1 in *.
  allrw @nt_wf_oterm_iff; autorewrite with slow in *; repnd; dands; auto;
    simpl in *; dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_push_swap_cs_sub_term_implies {o} :
  forall sw l (t : @NTerm o),
    nt_wf (push_swap_cs_sub_term sw l t)
    -> nt_wf t.
Proof.
  introv wf.
  unfold push_swap_cs_sub_term in *;
    try apply lsubst_aux_nt_wf in wf; auto.
Qed.

Lemma map_num_bvars_push_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    map num_bvars (push_swap_cs_bterms sw bs)
    = map num_bvars bs.
Proof.
  introv; unfold push_swap_cs_bterms; rewrite map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl; tcsp.
Qed.
Hint Rewrite @map_num_bvars_push_swap_cs_bterms : slow.

(*Lemma OpBindingsCan_delayed_swap_cs_can {o} :
  forall sw (can : @CanonicalOp o),
    OpBindingsCan (delayed_swap_cs_can sw can)
    = OpBindingsCan can.
Proof.
  introv; destruct can; simpl; auto.
Qed.
Hint Rewrite @OpBindingsCan_delayed_swap_cs_can : slow.*)

Lemma nt_wf_push_swap_cs_can_implies {o} :
  forall sw can (bs : list (@BTerm o)),
    nt_wf (push_swap_cs_can sw can bs)
    -> nt_wf (oterm (Can can) bs).
Proof.
  introv wf.
  unfold push_swap_cs_can in *.
  allrw @nt_wf_oterm_iff; simpl in *; autorewrite with slow in *; repnd; dands; auto.
  introv i.
  pose proof (wf (push_swap_cs_bterm sw b)) as wf.
  autodimp wf hyp.
  { apply in_map_iff; eexists; dands; eauto. }
  destruct b; simpl in *.
  allrw @bt_wf_iff.
  apply nt_wf_mk_swap_cs2_implies in wf; tcsp.
  apply nt_wf_push_swap_cs_sub_term_implies in wf; auto.
Qed.

Lemma implies_nt_wf_mk_swap_cs1 {o} :
  forall (a b c : @NTerm o),
    nt_wf a
    -> nt_wf b
    -> nt_wf c
    -> nt_wf (mk_swap_cs1 a b c).
Proof.
  introv wfa wfb wfc.
  constructor; simpl; tcsp.
  introv i; repndors; subst; tcsp; constructor; auto.
Qed.
Hint Resolve implies_nt_wf_mk_swap_cs1 : slow.

Lemma implies_nt_wf_mk_swap_cs2 {o} :
  forall sw (c : @NTerm o),
    nt_wf c
    -> nt_wf (mk_swap_cs2 sw c).
Proof.
  introv wfc.
  constructor; simpl; tcsp.
  introv i; repndors; subst; tcsp; constructor; auto.
Qed.
Hint Resolve implies_nt_wf_mk_swap_cs2 : slow.

Lemma wf_sub_sw_sub {o} :
  forall sw l, @wf_sub o (sw_sub sw l).
Proof.
  introv i.
  apply in_map_iff in i; exrepnd; ginv; eauto 3 with slow.
Qed.
Hint Resolve wf_sub_sw_sub : slow.

Lemma implies_nt_wf_push_swap_cs_sub_term {o} :
  forall sw l (t : @NTerm o),
    nt_wf t
    -> nt_wf (push_swap_cs_sub_term sw l t).
Proof.
  introv wf.
  unfold push_swap_cs_sub_term.
  apply lsubst_aux_preserves_wf; auto.
  introv i; apply in_map_iff in i; exrepnd; ginv; eauto 3 with slow.
Qed.
Hint Resolve implies_nt_wf_push_swap_cs_sub_term : slow.

Lemma implies_nt_wf_push_swap_cs_oterm {o} :
  forall sw can (bs : list (@BTerm o)),
    nt_wf (oterm (Can can) bs)
    -> nt_wf (push_swap_cs_can sw can bs).
Proof.
  introv wf; unfold push_swap_cs_can.
  allrw @nt_wf_oterm_iff; repnd; simpl in *; autorewrite with slow; dands; auto.
  introv i; unfold push_swap_cs_bterms in i; apply in_map_iff in i; exrepnd; subst.
  apply wf in i1; destruct a; simpl in *.
  allrw @bt_wf_iff; eauto 4 with slow.
Qed.
Hint Resolve implies_nt_wf_push_swap_cs_oterm : slow.

(*Lemma nt_wf_swap_cs0_iff {o} :
  forall (l : list (@BTerm o)),
    nt_wf (oterm (NCan NSwapCs0) l)
    <=> {a : NTerm & {b : NTerm & {c : NTerm
         & l = [nobnd a, nobnd b, nobnd c]
         # nt_wf a
         # nt_wf b
         # nt_wf c}}}.
Proof.
  introv; split; intro h.
  { inversion h as [|? ? imp eqm]; subst; clear h; simpl in *.
    repeat (destruct l; simpl in *; ginv).
    destruct b, b0, b1; unfold num_bvars in *; simpl in *.
    destruct l, l0, l1; simpl in *; ginv.
    dLin_hyp; allrw @bt_wf_iff.
    exists n n0 n1; dands; tcsp. }
  { exrepnd; subst.
    repeat constructor; simpl; introv i; repndors; subst; tcsp; constructor; auto. }
Qed.*)

Lemma nt_wf_swap_cs1_iff {o} :
  forall (l : list (@BTerm o)),
    nt_wf (oterm (NCan NSwapCs1) l)
    <=> {a : NTerm & {b : NTerm & {c : NTerm
         & l = [nobnd a, nobnd b, nobnd c]
         # nt_wf a
         # nt_wf b
         # nt_wf c}}}.
Proof.
  introv; split; intro h.
  { inversion h as [|? ? imp eqm]; subst; clear h; simpl in *.
    repeat (destruct l; simpl in *; ginv).
    destruct b, b0, b1; unfold num_bvars in *; simpl in *.
    destruct l, l0, l1; simpl in *; ginv.
    dLin_hyp; allrw @bt_wf_iff.
    exists n n0 n1; dands; tcsp. }
  { exrepnd; subst.
    repeat constructor; simpl; introv i; repndors; subst; tcsp; constructor; auto. }
Qed.

Lemma nt_wf_swap_cs2_iff {o} :
  forall nfo (l : list (@BTerm o)),
    nt_wf (oterm (NSwapCs2 nfo) l)
    <=> {a : NTerm
         & l = [nobnd a]
         # nt_wf a}.
Proof.
  introv; split; intro h.
  { inversion h as [|? ? imp eqm]; subst; clear h; simpl in *.
    repeat (destruct l; simpl in *; ginv); dLin_hyp.
    destruct b; unfold num_bvars in *; simpl in *.
    destruct l; simpl in *; ginv.
    allrw @bt_wf_iff.
    exists n; dands; tcsp. }
  { exrepnd; subst.
    repeat constructor; simpl; introv i; repndors; subst; tcsp; constructor; auto. }
Qed.

(*Lemma nt_wf_swap_cs_iff {o} :
  forall (l : list (@BTerm o)),
    nt_wf (oterm (NCan NSwapCs) l)
    <=> {a : NTerm & {b : NTerm & {c : NTerm
         & l = [nobnd a, nobnd b, nobnd c]
         # nt_wf a
         # nt_wf b
         # nt_wf c}}}.
Proof.
  introv; split; intro h.
  { inversion h as [|? ? imp eqm]; subst; clear h; simpl in *.
    repeat (destruct l; simpl in *; ginv).
    destruct b, b0, b1; unfold num_bvars in *; simpl in *.
    destruct l, l0, l1; simpl in *; ginv.
    dLin_hyp; allrw @bt_wf_iff.
    exists n n0 n1; dands; tcsp. }
  { exrepnd; subst.
    repeat constructor; simpl; introv i; repndors; subst; tcsp; constructor; auto. }
Qed.*)

Lemma sub_find_sw_sub {o} :
  forall sw l v,
    @sub_find o (sw_sub sw l) v
    = if in_deq _ deq_nvar v l then Some (mk_swap_cs2 sw (mk_var v))
      else None.
Proof.
  induction l; introv; simpl; auto.
  boolvar; simpl in *; repndors; subst; tcsp.
  { destruct n; tcsp. }
  { rewrite IHl; boolvar; tcsp. }
  { apply not_over_or in n0; repnd.
    rewrite IHl; boolvar; tcsp. }
Qed.

Hint Rewrite remove_nvars_nil_r : slow.

Lemma sub_filter_sw_sub {o} :
  forall sw l k,
    @sub_filter o (sw_sub sw l) k
    = sw_sub sw (remove_nvars k l).
Proof.
  induction l; introv; simpl; autorewrite with slow; simpl; auto.
  boolvar; simpl; tcsp; rewrite remove_nvars_cons_r; boolvar; tcsp.
  simpl; try congruence.
Qed.

Lemma free_vars_lsubst_aux_sw_sub {o} :
  forall sw (t : @NTerm o) l,
    free_vars (lsubst_aux t (sw_sub sw l)) = free_vars t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv.
  { rewrite sub_find_sw_sub; boolvar; simpl; auto. }
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  rewrite sub_filter_sw_sub.
  erewrite ind; eauto.
Qed.
Hint Rewrite @free_vars_lsubst_aux_sw_sub : slow.

Lemma flat_map_free_vars_range_sw_sub {o} :
  forall sw l,
    flat_map free_vars (range (@sw_sub o sw l)) = l.
Proof.
  induction l; introv; simpl; auto; try congruence.
Qed.
Hint Rewrite @flat_map_free_vars_range_sw_sub : slow.

Hint Rewrite @free_vars_change_bvars_alpha : slow.

Lemma free_vars_push_swap_cs_sub_term {o} :
  forall sw l (t : @NTerm o),
    free_vars (push_swap_cs_sub_term sw l t)
    = free_vars t.
Proof.
  introv.
  unfold push_swap_cs_sub_term.
  unfold lsubst; autorewrite with slow.
  boolvar; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_push_swap_cs_sub_term : slow.

Definition free_vars_bterms {o} (bs : list (@BTerm o)) :=
  flat_map free_vars_bterm bs.

Lemma bterm_in_implies_subvars_free_vars {o} :
  forall l (t : @NTerm o) bs,
    LIn (bterm l t) bs
    -> subvars (free_vars t) (l ++ free_vars_bterms bs).
Proof.
  introv i.
  rw subvars_prop; introv j.
  rw in_app_iff.
  destruct (in_deq _ deq_nvar x l); tcsp.
  right.
  rw lin_flat_map.
  eexists; dands; eauto; simpl.
  rw in_remove_nvars; sp.
Qed.

Lemma free_vars_push_swap_cs_oterm {o} :
  forall sw can (bs : list (@BTerm o)),
    free_vars (push_swap_cs_can sw can bs) = free_vars_bterms bs.
Proof.
  introv; simpl; tcsp.
  unfold push_swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_push_swap_cs_oterm : slow.

Lemma flat_map_free_vars_bterm_push_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    flat_map free_vars_bterm (push_swap_cs_bterms sw bs)
    = free_vars_bterms bs.
Proof.
  introv; unfold free_vars_bterms, push_swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_bterm_push_swap_cs_bterms : slow.

Lemma implies_isprog_vars_push_swap_cs_sub_term {o} :
  forall l sw vs (t : @NTerm o),
    isprog_vars l t
    -> isprog_vars l (push_swap_cs_sub_term sw vs t).
Proof.
  introv ispa.
  allrw @isprog_vars_eq; repnd; dands; autorewrite with slow; auto.
  apply implies_nt_wf_push_swap_cs_sub_term; auto.
Qed.
Hint Resolve implies_isprog_vars_push_swap_cs_sub_term : slow.

Lemma implies_isprogram_push_swap_cs_can {o} :
  forall sw can (bs : list (@BTerm o)),
    isprogram (oterm (Can can) bs)
    -> isprogram (push_swap_cs_can sw can bs).
Proof.
  introv isp.
  unfold push_swap_cs_can.
  allrw @isprogram_ot_iff; simpl; autorewrite with slow in *; repnd; dands; auto.
  introv i.
  unfold push_swap_cs_bterms in i; apply in_map_iff in i; exrepnd; subst.
  destruct a; simpl.
  apply isp in i1.
  allrw @isprogram_bt_iff_isprog_vars; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_push_swap_cs_can : slow.

Lemma isprog_vars_swap_cs2_implies {o} :
  forall vs sw (a : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs (mk_swap_cs2 sw a).
Proof.
  introv ispa.
  apply implies_isprog_vars_mk_swap_cs2; auto.
Qed.

Definition mkc_swap_cs2 {o} sw (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (mk_swap_cs2 sw a) (isprog_swap_cs2_implies sw a x).

Definition mkcv_swap_cs2 {o} vs sw (t : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_swap_cs2 sw a) (isprog_vars_swap_cs2_implies vs sw a x).

Definition mkc_swap_cs {o} (sw : cs_swap) (t : @CTerm o) :=
  mkc_swap_cs2 sw t.

Definition mkcv_swap_cs {o} vs (sw : cs_swap) (t : @CVTerm o vs) :=
  mkcv_swap_cs2 _ sw t.
