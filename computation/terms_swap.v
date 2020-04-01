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
Require Export computation_preserve1.


Hint Rewrite remove_nvars_nil_l : slow.
Hint Rewrite app_nil_r : slow.


Lemma isprogram_swap_cs2_implies {p} :
  forall nfo (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NSwapCs2 nfo)) bterms)
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
  forall n1 n2 (a : @NTerm o),
    wf_term (mk_swap_cs2 n1 n2 a) <=> wf_term a.
Proof.
  introv; rw @wf_oterm_iff; simpl.
  split; intro h; repnd; dands; tcsp.
  { dLin_hyp; allrw @wf_bterm_iff; auto. }
  { introv i; repndors; subst; tcsp. }
Qed.

Lemma isprog_swap_cs2 {o} :
  forall n1 n2 (a : @NTerm o),
    isprog (mk_swap_cs2 n1 n2 a) <=> isprog a.
Proof.
  introv.
  unfold isprog; simpl; autorewrite with slow.
  rw @wf_swap_cs2; tcsp.
Qed.

Lemma isprog_swap_cs2_implies {o} :
  forall n1 n2 (a : @NTerm o),
    isprog a
    -> isprog (mk_swap_cs2 n1 n2 a).
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
  forall l n1 n2 (t : @NTerm o),
    isprog_vars l t
    -> isprog_vars l (mk_swap_cs2 n1 n2 t).
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
  forall n1 n2 (t : @NTerm o),
    isprogram t
    -> isprogram (mk_swap_cs2 n1 n2 t).
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
  forall a b (c : @NTerm o),
    nt_wf (mk_swap_cs2 a b c)
    -> nt_wf c.
Proof.
  introv wf.
  unfold mk_swap_cs1 in *.
  allrw @nt_wf_oterm_iff; autorewrite with slow in *; repnd; dands; auto;
    simpl in *; dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_push_swap_cs_can_implies {o} :
  forall c1 c2 can (bs : list (@BTerm o)),
    nt_wf (push_swap_cs_can c1 c2 can bs)
    -> nt_wf (oterm (Can can) bs).
Proof.
  introv wf.
  unfold push_swap_cs_can in *.
  allrw @nt_wf_oterm_iff; simpl in *; autorewrite with slow in *; repnd; dands; auto.
  introv i.
  pose proof (wf (push_swap_cs_bterm c1 c2 b)) as wf.
  autodimp wf hyp.
  { apply in_map_iff; eexists; dands; eauto. }
  destruct b; simpl in *.
  allrw @bt_wf_iff.
  apply nt_wf_mk_swap_cs2_implies in wf; tcsp.
Qed.

Lemma implies_isprogram_push_swap_cs_can {o} :
  forall c1 c2 can (bs : list (@BTerm o)),
    isprogram (oterm (Can can) bs)
    -> isprogram (push_swap_cs_can c1 c2 can bs).
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
  forall vs n1 n2 (a : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs (mk_swap_cs2 n1 n2 a).
Proof.
  introv ispa.
  apply implies_isprog_vars_mk_swap_cs2; auto.
Qed.

Definition mkc_swap_cs2 {o} n1 n2 (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (mk_swap_cs2 n1 n2 a) (isprog_swap_cs2_implies n1 n2 a x).

Definition mkcv_swap_cs2 {o} vs n1 n2 (t : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_swap_cs2 n1 n2 a) (isprog_vars_swap_cs2_implies vs n1 n2 a x).

Definition mkc_swap_cs {o} (sw : cs_swap) (t : @CTerm o) :=
  mkc_swap_cs2 (fst sw) (snd sw) t.

Definition mkcv_swap_cs {o} vs (sw : cs_swap) (t : @CVTerm o vs) :=
  mkcv_swap_cs2 _ (fst sw) (snd sw) t.
