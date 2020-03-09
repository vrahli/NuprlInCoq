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


Require Export computation2.
Require Export csubst_ref.


Hint Rewrite app_nil_r : slow.
Hint Rewrite @sub_filter_nil_r : slow.
Hint Rewrite remove_nvars_nil_l : slow.
Hint Rewrite @oappl_nil : slow.
Hint Rewrite remove_nvars_eq : slow.
Hint Rewrite memvar_singleton : slow.
Hint Rewrite @lsubst_nil : slow.
Hint Rewrite @sub_keep_first_nil_r : slow.

Hint Resolve subset_get_utokens_get_utokens_step_seq : slow.
Hint Resolve oeqset_implies_osubset : slow.
Hint Resolve subset_disjoint_r : slow.


Lemma isprog_nout_implies_isprog {o} :
  forall (t : @NTerm o), isprog_nout t -> isprog t.
Proof.
  introv isp.
  apply isprog_nout_iff in isp; repnd.
  apply isprog_eq.
  constructor; auto.
Qed.
Hint Resolve isprog_nout_implies_isprog : slow.

Lemma compute_step_seq_can_test_success {o} :
  forall (t : @NTerm o) bs u,
    compute_step_seq_can_test t bs = csuccess u
    -> {a : NTerm & {b : NTerm & bs = [nobnd a, nobnd b] # u = b}}.
Proof.
  introv comp.
  unfold compute_step_seq_can_test in comp.
  destruct bs; allsimpl; ginv.
  destruct b as [l a].
  destruct l; allsimpl; ginv.
  destruct bs; allsimpl; ginv.
  destruct b as [l b].
  destruct l; allsimpl; ginv.
  destruct bs; allsimpl; ginv.
  unfold nobnd.
  eexists; eexists; dands; eauto.
Qed.

Lemma nt_wf_NCanTest {o} :
  forall c (bs : list (@BTerm o)),
    nt_wf (oterm (NCan (NCanTest c)) bs)
    <=> {t1 : NTerm
         & {t2 : NTerm
         & {t3 : NTerm
         & bs = [nobnd t1, nobnd t2, nobnd t3]
         # nt_wf t1
         # nt_wf t2
         # nt_wf t3 }}}.
Proof.
  introv; split; introv h.
  - inversion h as [|? ? imp e]; subst; allsimpl; clear h.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1]; allsimpl.
    destruct b0 as [l2 t2]; allsimpl.
    destruct b1 as [l3 t3]; allsimpl.
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    destruct l3; allsimpl; ginv.
    allunfold @num_bvars; allsimpl; GC.
    pose proof (imp (bterm [] t1)) as h1.
    pose proof (imp (bterm [] t2)) as h2.
    pose proof (imp (bterm [] t3)) as h3.
    clear imp.
    autodimp h1 hyp.
    autodimp h2 hyp.
    autodimp h3 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; eexists; dands; eauto.
  - exrepnd; subst.
    constructor; unfold num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Lemma compute_step_last_cs_success {o} :
  forall lib can (t : @NTerm o) bts bs u,
    compute_step_last_cs lib can t bts bs = csuccess u
    -> {name : choice_sequence_name
        & {d : NTerm
        & can = Ncseq name
        # bts = []
        # bs = [nobnd d]
        # u = find_last_entry_default lib name d }}.
Proof.
  introv e; allsimpl; destruct can; allsimpl; ginv; boolvar; ginv.

  destruct bts; allsimpl; ginv.
  destruct bs; allsimpl; ginv.
  destruct b, l, bs; ginv.
  eexists; eexists; dands; unfold nobnd; eauto.
Qed.

Lemma compute_step_comp_seq1_success {o} :
  forall lib nfo can (t : @NTerm o) bts bs u,
    compute_step_comp_seq1 lib nfo can t bts bs = csuccess u
    -> {a : cs_name
        & {i : nat
        & {f : NTerm
        & nfo = MkCompSeqNfo1 a
        # can = Nint (Z.of_nat i)
        # bts = []
        # bs = [nobnd f]
        #
        (
          (i = 0 # u = mk_fresh_choice_nat_seq a lib [])
          [+]
          (i > 0 # u = mk_comp_seq2 a [] i (mk_apply f mk_zero) f)
        )
       }}}.
Proof.
  introv e; allsimpl; destruct can, nfo as [a]; allsimpl; ginv; boolvar; ginv.

  { destruct bts; allsimpl; ginv.
    destruct bs; allsimpl; ginv.
    destruct b.
    destruct l0; ginv.
    destruct bs; allsimpl; ginv.
    exists a (Z.to_nat z) n.
    rewrite Z2Nat.id; dands; tcsp. }

  { destruct bts; allsimpl; ginv.
    destruct bs; allsimpl; ginv.
    destruct b.
    destruct l0; ginv.
    destruct bs; allsimpl; ginv.
    exists a (Z.to_nat z) n0.
    rewrite Z2Nat.id; dands; tcsp.
    right; dands; auto; try omega. }
Qed.

Lemma compute_step_comp_seq2_success {o} :
  forall lib nfo can (t : @NTerm o) bts bs u,
    compute_step_comp_seq2 lib nfo can t bts bs = csuccess u
    -> {a : cs_name
        & {l : list nat
        & {i : nat
        & {k : nat
        & {f : NTerm
        & nfo = MkCompSeqNfo2 a l i
        # can = Nint (Z.of_nat k)
        # bts = []
        # bs = [nobnd f]
        #
        (
          (i = S (length l) # u = mk_fresh_choice_nat_seq a lib (snoc l k))
          [+]
          (i > S (length l) # u = mk_comp_seq2 a (snoc l k) i (mk_apply f (mk_nat (S (length l)))) f)
        )
       }}}}}.
Proof.
  introv e; allsimpl.
  unfold compute_step_comp_seq2 in e.
  destruct nfo as [a l i]; allsimpl.
  exists a l i.
  destruct can; allsimpl; ginv; boolvar; ginv; subst;[|].


  { destruct bts; allsimpl; ginv.
    destruct bs; allsimpl; ginv.
    destruct b.
    destruct l1; ginv.
    destruct bs; allsimpl; ginv.
    exists (Z.to_nat z) n.
    rewrite Z2Nat.id; auto.
    dands; auto; try omega. }

  { destruct bts; allsimpl; ginv.
    destruct bs; allsimpl; ginv.
    destruct b.
    destruct l1; ginv.
    destruct bs; allsimpl; ginv.
    exists (Z.to_nat z) n0.
    rewrite Z2Nat.id; auto.
    dands; auto; try omega.
    right; dands; try omega; auto. }
Qed.

Lemma implies_nt_wf_mk_comp_seq2 {o} :
  forall n l i (a b : @NTerm o),
    nt_wf a
    -> nt_wf b
    -> nt_wf (mk_comp_seq2 n l i a b).
Proof.
  introv wfa wfb.
  repeat constructor; introv k; simpl in *; repndors; subst; tcsp;
    apply bt_wf_iff; auto.
Qed.
Hint Resolve implies_nt_wf_mk_comp_seq2 : slow.

Lemma nt_wf_mk_comp_seq1_iff {o} :
  forall n (a b : @NTerm o),
    nt_wf (mk_comp_seq1 n a b) <=> (nt_wf a # nt_wf b).
Proof.
  introv; split; intro h.

  {
    inversion h as [|? ? imp eqm]; subst; simpl in *.
    unfold nobnd, num_bvars in *; simpl in *; GC.
    pose proof (imp (bterm [] a)) as q1; autodimp q1 hyp.
    pose proof (imp (bterm [] b)) as q2; autodimp q2 hyp.
    allrw @bt_wf_iff; tcsp.
  }

  {
    repnd.
    repeat constructor; introv k; simpl in *; repndors; subst; tcsp;
      apply bt_wf_iff; auto.
  }
Qed.

Lemma nt_wf_mk_comp_seq2_iff {o} :
  forall n l i (a b : @NTerm o),
    nt_wf (mk_comp_seq2 n l i a b) <=> (nt_wf a # nt_wf b).
Proof.
  introv; split; intro h.

  {
    inversion h as [|? ? imp eqm]; subst; simpl in *.
    unfold nobnd, num_bvars in *; simpl in *; GC.
    pose proof (imp (bterm [] a)) as q1; autodimp q1 hyp.
    pose proof (imp (bterm [] b)) as q2; autodimp q2 hyp.
    allrw @bt_wf_iff; tcsp.
  }

  {
    repnd.
    repeat constructor; introv k; simpl in *; repndors; subst; tcsp;
      apply bt_wf_iff; auto.
  }
Qed.

Lemma implies_nt_wf_apply {o} :
  forall (a b : @NTerm o),
    nt_wf a
    -> nt_wf b
    -> nt_wf (mk_apply a b).
Proof.
  introv wfa wfb.
  allrw <- @wf_term_eq.
  apply wf_apply; auto.
Qed.
Hint Resolve implies_nt_wf_apply : slow.

Lemma nt_wf_mk_fresh_choice_nat_seq {o} :
  forall n (lib : @plibrary o) l, nt_wf (mk_fresh_choice_nat_seq n lib l).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve nt_wf_mk_fresh_choice_nat_seq : slow.

Lemma free_vars_find_last_entry_default_subvars {o} :
  forall lib name (d : @NTerm o),
    subvars (free_vars (find_last_entry_default lib name d)) (free_vars d).
Proof.
  introv; allrw subvars_eq; introv i.
  unfold find_last_entry_default in i.
  remember (find_cs lib name) as fcs; destruct fcs; simpl in *; auto.
  remember (last_cs_entry c) as lcs; destruct lcs; simpl in *; auto.
  autorewrite with slow in *; simpl in *; tcsp.
Qed.
Hint Resolve free_vars_find_last_entry_default_subvars : slow.

Lemma nt_wf_find_last_entry_default {o} :
  forall lib name (d : @NTerm o),
    nt_wf d
    -> nt_wf (find_last_entry_default lib name d).
Proof.
  introv wf; allrw subvars_eq.
  unfold find_last_entry_default.
  remember (find_cs lib name) as fcs; destruct fcs; simpl in *; auto.
  remember (last_cs_entry c) as lcs; destruct lcs; simpl in *; auto.
  eauto 3 with slow.
Qed.
Hint Resolve nt_wf_find_last_entry_default : slow.

Lemma compute_step_swap_cs1_success {o} :
  forall btsr (t : @NTerm o) arg1c arg1bts cstep arg1 ncr b,
    compute_step_swap_cs1 btsr t arg1c arg1bts cstep arg1 ncr = csuccess b
    -> {n1 : choice_sequence_name
       & {n2 : choice_sequence_name
       & {u : NTerm
       & arg1c = Ncseq n1
       # btsr = [bterm [] (oterm (Can (Ncseq n2)) []), bterm [] u]
       # arg1bts = []
       # b = mk_swap_cs2 n1 n2 u }}}
       [+]
       {l : list BTerm
       & {k : list BTerm
       & btsr = bterm [] (oterm Exc l) :: k
       # b = oterm Exc l }}
       [+]
       {op : Opid
       & {bs : list BTerm
       & {l : list BTerm
       & {u : NTerm
       & btsr = bterm [] (oterm op bs) :: l
       # cstep = csuccess u
       # isnoncan_like (oterm op bs)
       # b = oterm (NCan ncr) (bterm [] arg1 :: bterm [] u :: l) }}}}.
Proof.
  introv comp.
  destruct btsr; simpl in *; ginv.
  destruct b0; simpl in *; tcsp.
  destruct l; simpl in *; tcsp; ginv.
  destruct n; simpl in *; tcsp; ginv.
  destruct o0; simpl in *; tcsp.
  { unfold compute_step_swap_cs2 in *.
    destruct arg1c; simpl in *; tcsp; ginv.
    destruct c; simpl in *; tcsp; ginv.
    destruct arg1bts; simpl in *; tcsp; ginv.
    destruct l; simpl in *; tcsp; ginv.
    destruct btsr; simpl in *; tcsp; ginv.
    destruct b0; simpl in *; tcsp; ginv.
    destruct l; simpl in *; tcsp; ginv.
    destruct btsr; simpl in *; tcsp; ginv.
    left.
    exists c0 c n; dands; auto. }
  { destruct cstep; simpl in *; ginv.
    right; right.
    exists (@NCan o n) l btsr n0; dands; tcsp. }
  { ginv.
    right; left.
    exists l btsr; dands; auto. }
  { destruct cstep; simpl in *; ginv.
    right; right.
    exists (@Abs o o0) l btsr n; dands; tcsp. }
Qed.

Lemma compute_step_swap_cs2_success {o} :
  forall nfo arg1c arg1bts btsr (t : @NTerm o) b,
    compute_step_swap_cs2 nfo arg1c arg1bts btsr t = csuccess b
    -> btsr = [] # b = push_swap_cs_can (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) arg1c arg1bts.
Proof.
  introv comp.
  destruct btsr; simpl in *; ginv; auto.
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
  forall a b (c : @NTerm o),
    nt_wf c
    -> nt_wf (mk_swap_cs2 a b c).
Proof.
  introv wfc.
  constructor; simpl; tcsp.
  introv i; repndors; subst; tcsp; constructor; auto.
Qed.
Hint Resolve implies_nt_wf_mk_swap_cs2 : slow.

Lemma map_num_bvars_push_swap_cs_bterms {o} :
  forall n1 n2 (bs : list (@BTerm o)),
    map num_bvars (push_swap_cs_bterms n1 n2 bs)
    = map num_bvars bs.
Proof.
  introv; unfold push_swap_cs_bterms; rewrite map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl; tcsp.
Qed.
Hint Rewrite @map_num_bvars_push_swap_cs_bterms : slow.

Lemma implies_nt_wf_push_swap_cs_oterm {o} :
  forall n1 n2 can (bs : list (@BTerm o)),
    nt_wf (oterm (Can can) bs)
    -> nt_wf (push_swap_cs_can n1 n2 can bs).
Proof.
  introv wf; unfold push_swap_cs_can.
  allrw @nt_wf_oterm_iff; repnd; simpl in *; autorewrite with slow; dands; auto.
  introv i; unfold push_swap_cs_bterms in i; apply in_map_iff in i; exrepnd; subst.
  apply wf in i1; destruct a; simpl in *.
  allrw @bt_wf_iff; eauto 4 with slow.
Qed.
Hint Resolve implies_nt_wf_push_swap_cs_oterm : slow.

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
    nt_wf (oterm (NCan (NSwapCs2 nfo)) l)
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

Lemma free_vars_push_swap_cs_oterm {o} :
  forall n1 n2 can (bs : list (@BTerm o)),
    free_vars (push_swap_cs_can n1 n2 can bs) = free_vars_bterms bs.
Proof.
  introv; simpl; tcsp.
  unfold push_swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_push_swap_cs_oterm : slow.

Lemma flat_map_free_vars_bterm_push_swap_cs_bterms {o} :
  forall n1 n2 (bs : list (@BTerm o)),
    flat_map free_vars_bterm (push_swap_cs_bterms n1 n2 bs)
    = free_vars_bterms bs.
Proof.
  introv; unfold free_vars_bterms, push_swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_bterm_push_swap_cs_bterms : slow.

Lemma compute_step_preserves {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> compute_step lib t = csuccess u
    -> (subvars (free_vars u) (free_vars t) # nt_wf u).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv wf comp.

  - Case "vterm".
    rw @compute_step_eq_unfold in comp; allsimpl; ginv.

  - Case "oterm".
    rw @compute_step_eq_unfold in comp.
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      simphyps; ginv; dands; try (complete (allsimpl; tcsp)).

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [v|op bts]; try (complete (allsimpl; ginv)).

        dopid op as [can2|ncan2|exc2|abs2] SSCase.

        * SSCase "Can".
          dopid_noncan ncan SSSCase.

        { SSSCase "NApply".

          clear ind; simpl in comp.
          apply compute_step_apply_success in comp; repndors; exrepnd; subst; fold_terms.

          { dands; tcsp.

            - pose proof (eqvars_free_vars_disjoint b [(v,arg)]) as h.
              allrw @fold_subst.
              apply eqvars_sym in h.
              eapply subvars_eqvars;[|exact h].
              simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
              boolvar; simpl; allrw app_nil_r; auto.
              apply subvars_app_weak_l; auto.

              (*
            - simpl; allrw app_nil_r.
              pose proof (get_markers_lsubst b [(v,arg)]) as h.
              allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
              introv i; apply h in i; allrw in_app_iff; sp.
               *)

            - (*intro w.*)
              allrw @nt_wf_eq.
              allrw <- @wf_apply_iff; repnd.
              allrw <- @wf_lam_iff.
              apply wf_term_subst; auto.
          }

          { allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            dands; eauto 3 with slow.
            allrw @nt_wf_eq.
            allrw <- @wf_apply_iff; allrw <- @wf_eapply_iff; repnd.
            dands; auto.
          }
        }

        { SSSCase "NEApply".

          simpl in comp.
          apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
          apply nt_wf_eapply_iff in wf; exrepnd; allunfold @nobnd; ginv.
          repndors; exrepnd; subst; fold_terms.

          { clear ind.
            apply compute_step_eapply2_success in comp1; repnd; GC.
            repndors; exrepnd; subst; allunfold @mk_lam; allunfold @mk_choice_seq;
              ginv; fold_terms; allsimpl;
                autorewrite with slow;
                unfold apply_bterm; simpl; allrw @fold_subst;
                  dands; eauto 3 with slow; GC.

            - pose proof (eqvars_free_vars_disjoint b0 [(v,b)]) as h.
              allrw @fold_subst.
              apply eqvars_sym in h.
              eapply subvars_eqvars;[|exact h]; clear h.
              simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
              boolvar; simpl; allrw app_nil_r; auto.
              apply subvars_app_weak_l; auto.

            - allrw @nt_wf_eq.
              allrw <- @wf_lam_iff.
              apply wf_term_subst; auto.
          }

          { clear ind.
            allsimpl.
            allrw remove_nvars_nil_l; allrw app_nil_r.
            dands; eauto 3 with slow.
          }

          { simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            rw @subvars_app_l.
            allrw @nt_wf_eq.
            allrw <- @wf_eapply_iff.
            pose proof (ind b b []) as ih; clear ind; repeat (autodimp ih hyp); eauto 3 with slow.
            apply ih in comp1; auto;[|apply nt_wf_eq;auto]; clear ih; repnd.
            dands; eauto 3 with slow.
          }
        }

(*        { SSSCase "NApseq".

          clear ind; allsimpl.
          apply compute_step_apseq_success in comp; exrepnd; subst; allsimpl.
          fold_terms.
          dands; eauto 3 with slow.
        }*)

        { SSSCase "NFix".

          clear ind; simpl in comp.
          apply compute_step_fix_success in comp; repnd; subst; simpl.
          allrw remove_nvars_nil_l; allrw app_nil_r;
          allrw subvars_app_l; allrw subset_app; dands; auto.

          - allrw @nt_wf_eq.
            allrw @wf_fix_iff.
            apply wf_apply; auto.
            apply wf_fix; auto.
        }

        { SSSCase "NSpread".

          clear ind; simpl in comp.
          apply compute_step_spread_success in comp; exrepnd; subst; fold_terms.

          dands; tcsp.

          - pose proof (eqvars_free_vars_disjoint arg [(va,a),(vb,b)]) as h.
            allrw @fold_subst.
            apply eqvars_sym in h.
            eapply subvars_eqvars;[|exact h].
            simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands; auto;
            try (complete (apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_r; auto)).

            (*
          - simpl; allrw app_nil_r.
            pose proof (get_markers_lsubst arg [(va,a),(vb,b)]) as h.
            allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
            introv i; apply h in i; allrw in_app_iff; sp.
             *)

          - (*intro w.*)
            allrw @nt_wf_eq.
            allrw @wf_spread; repnd.
            allrw @wf_pair; repnd.
            apply lsubst_preserves_wf_term; eauto with slow.
        }

        { SSSCase "NDsup".

          clear ind; simpl in comp.
          apply compute_step_dsup_success in comp; exrepnd; subst; fold_terms.

          dands; tcsp.

          - pose proof (eqvars_free_vars_disjoint arg [(va,a),(vb,b)]) as h.
            allrw @fold_subst.
            apply eqvars_sym in h.
            eapply subvars_eqvars;[|exact h].
            simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands; auto;
            try (complete (apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_r; auto)).

            (*
          - simpl; allrw app_nil_r.
            pose proof (get_markers_lsubst arg [(va,a),(vb,b)]) as h.
            allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
            introv i; apply h in i; allrw in_app_iff; sp.
             *)

          - (*intro w.*)
            allrw @nt_wf_eq.
            allrw @wf_dsup; repnd.
            allrw @wf_sup_iff; repnd.
            apply lsubst_preserves_wf_term; eauto with slow.
        }

        { SSSCase "NDecide".

          clear ind; simpl in comp.
          apply compute_step_decide_success in comp; exrepnd; subst; fold_terms.

          dorn comp0; repnd; subst; dands; tcsp.

          - pose proof (eqvars_free_vars_disjoint t1 [(v1,d)]) as h.
            allrw @fold_subst.
            apply eqvars_sym in h.
            eapply subvars_eqvars;[|exact h].
            simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands; auto;
            try (complete (apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_r; auto;
                           apply subvars_app_weak_l; auto)).

            (*
          - simpl; allrw app_nil_r.
            pose proof (get_markers_lsubst t1 [(v1,d)]) as h.
            allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
            introv i; apply h in i; allrw in_app_iff; sp.
             *)

          - (*intro w.*)
            allrw @nt_wf_eq.
            allrw @wf_decide; repnd.
            allrw @wf_inl.
            apply wf_term_subst; auto.

          - pose proof (eqvars_free_vars_disjoint t2 [(v2,d)]) as h.
            allrw @fold_subst.
            apply eqvars_sym in h.
            eapply subvars_eqvars;[|exact h].
            simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands; auto;
            try (complete (apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_l; auto;
                           apply subvars_app_weak_r; auto));
            try (complete (apply subvars_app_weak_r; auto;
                           apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_r; auto;
                           apply subvars_app_weak_r; auto)).

            (*
          - simpl; allrw app_nil_r.
            pose proof (get_markers_lsubst t2 [(v2,d)]) as h.
            allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
            introv i; apply h in i; allrw in_app_iff; sp.
             *)

          - (*intro w.*)
            allrw @nt_wf_eq.
            allrw @wf_decide; repnd.
            allrw @wf_inr.
            apply wf_term_subst; auto.
        }

        { SSSCase "NCbv".

          clear ind; simpl in comp.
          apply compute_step_cbv_success in comp; exrepnd; subst; fold_terms.

          dands; tcsp.

          - pose proof (eqvars_free_vars_disjoint x [(v,oterm (Can can2) bts)]) as h.
            allrw @fold_subst.
            apply eqvars_sym in h.
            eapply subvars_eqvars;[|exact h].
            simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
            boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands;
            try (complete (apply subvars_app_weak_l; auto));
            try (complete (apply subvars_app_weak_r; auto)).

            (*
          - simpl; allrw app_nil_r.
            pose proof (get_markers_lsubst x [(v,oterm (Can can2) bts)]) as h.
            allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
            introv i; apply h in i; allrw in_app_iff; sp.
             *)

          - (*intro w.*)
            allrw @nt_wf_eq.
            allrw <- @wf_cbv_iff; repnd.
            apply wf_term_subst; auto.
        }

        { SSSCase "NSleep".

          clear ind; simpl in comp.
          apply compute_step_sleep_success in comp; exrepnd; subst; fold_terms.

          simpl; allrw remove_nvars_nil_l; allrw app_nil_r; dands; eauto 3 with slow.
        }

        { SSSCase "NTUni".

          clear ind; simpl in comp.
          apply compute_step_tuni_success in comp; exrepnd; subst; fold_terms.

          simpl; allrw remove_nvars_nil_l; allrw app_nil_r; dands; eauto 3 with slow.
        }

        { SSSCase "NMinus".

          clear ind; simpl in comp.
          apply compute_step_minus_success in comp; exrepnd; subst; fold_terms.

          simpl; allrw remove_nvars_nil_l; allrw app_nil_r; dands; eauto 3 with slow.
        }

        { SSSCase "NFresh".
          allsimpl; ginv.
        }

        { SSSCase "NTryCatch".

          clear ind; simpl in comp.
          apply compute_step_try_success in comp; exrepnd; subst; fold_terms.

          simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
          allrw subvars_app_l.
          allrw subset_app.

          unfold oatoml; autorewrite with slow.
          dands; tcsp; eauto 4 with slow.

          { allrw @nt_wf_eq.
            allrw @wf_atom_eq.
            allrw <- @wf_try_iff; sp. }
        }

        { SSSCase "NParallel".
          allsimpl.
          apply compute_step_parallel_success in comp; subst; allsimpl.
          allrw remove_nvars_nil_l; dands; simpl;
          autorewrite with slow; eauto with slow.
        }

        { SSSCase "NSwapCs1".
          allsimpl.
          apply compute_step_swap_cs1_success in comp; repndors; exrepnd; subst; simpl in *; tcsp;
            autorewrite with slow; allrw @nt_wf_swap_cs1_iff; exrepnd; ginv;
              inversion wf1; subst; clear wf1; simpl; autorewrite with slow; dands; eauto 3 with slow.
          { eapply ind in comp2; try (right; left); eauto; eauto 3 with slow; repnd.
            dands; eauto 3 with slow. }
          { eapply ind in comp2; try (right; left); eauto; eauto 3 with slow; repnd.
            fold_terms; eexists; eexists; eexists; dands; eauto. } }

        { SSSCase "NSwapCs2".
          allsimpl.
          apply compute_step_swap_cs2_success in comp; repndors; exrepnd; subst; simpl in *; tcsp;
            autorewrite with slow; allrw @nt_wf_swap_cs2_iff; exrepnd; ginv;
              inversion wf1; subst; clear wf1; simpl; autorewrite with slow; dands; eauto 3 with slow. }

        { SSSCase "NLastCs".

          allsimpl; autorewrite with slow in *.
          apply compute_step_last_cs_success in comp; exrepnd; subst; simpl in *.
          allrw @nt_wf_last_cs; repnd.
          autorewrite with slow; dands; auto; eauto 3 with slow.
        }

        { SSSCase "NCompSeq1".

          allsimpl.
          apply compute_step_comp_seq1_success in comp.
          exrepnd; repndors; exrepnd;subst; simpl in *; autorewrite with slow.

          { dands; eauto 3 with slow. }

          apply nt_wf_mk_comp_seq1_iff in wf; repnd.
          dands; eauto 4 with slow.
        }

        { SSSCase "NCompSeq2".

          allsimpl.
          apply compute_step_comp_seq2_success in comp; exrepnd; subst.
          repndors; exrepnd; subst; simpl; autorewrite with slow;
            try (complete (dands; auto; eauto 3 with slow)).
          repndors; exrepnd; subst; simpl; autorewrite with slow;
            try (complete (dands; auto; eauto 3 with slow)).
          apply nt_wf_mk_comp_seq2_iff in wf; repnd.
          dands; eauto 5 with slow.
        }

        { SSSCase "NCompOp".

          destruct bs; try (complete (allsimpl; dcwf h));[].

          destruct b as [l t]; try (complete (allsimpl; ginv));[].
          destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; dcwf h));[].

          allrw @nt_wf_NCompOp; exrepnd; allunfold @nobnd; ginv; fold_terms.
          allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.

          dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

          - SSSSCase "Can".
            simpl in comp.
            dcwf h;[]; allsimpl.
            apply compute_step_compop_success_can_can in comp; exrepnd; subst; allsimpl; ginv.
            repndors; exrepnd; subst;
            allrw remove_nvars_nil_l; allrw app_nil_r;
            allapply @get_param_from_cop_pki;
            allapply @get_param_from_cop_pks;
            allapply @get_param_from_cop_pka; subst.

            + boolvar; dands;
              try (allrw @nt_wf_eq; allrw @wf_compop_iff; tcsp);
              eauto with slow;
              simpl; autorewrite with slow; simpl;
              apply implies_osubset_oappl_right; simpl;
              try (complete (eexists;dands;[|eauto 3 with slow];tcsp)).

            + boolvar; dands;
              try (allrw @nt_wf_eq; allrw @wf_compop_iff; tcsp);
              eauto with slow;
              simpl; autorewrite with slow; simpl;
              apply implies_osubset_oappl_right; simpl;
              try (complete (eexists;dands;[|eauto 3 with slow];
                             allrw in_app_iff;simpl;tcsp)).

          - SSSSCase "NCan".
            simpl in comp.
            dcwf h;[].
            remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
              symmetry in Heqcomp1; destruct comp1; allsimpl; ginv.
            apply (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) in Heqcomp1;
              repnd; tcsp; eauto 3 with slow.
            dands.

            { allsimpl; allrw remove_nvars_nil_l; allrw subvars_app_l.
              dands; eauto with slow. }

            { allrw @nt_wf_NCompOp.
              unfold nobnd; eexists; eexists; eexists; eexists; dands; eauto. }

          - SSSSCase "Exc".
            allsimpl; dcwf h; ginv; allsimpl;
            allrw remove_nvars_nil_l; dands;
            autorewrite with slow; eauto with slow.

          - SSSSCase "Abs".
            allsimpl; dcwf h;[]; unfold on_success in comp; ginv.
            rw @compute_step_eq_unfold in comp; allsimpl.
            remember (compute_step_lib lib abs3 bs2) as csl;
              symmetry in Heqcsl; destruct csl; ginv; simpl.

            applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
            applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
            unfold matching_entry in Heqcsl0; repnd.

            allrw remove_nvars_nil_l; allrw app_nil_r;
            allrw subvars_app_l; allrw subset_app; dands; eauto 4 with slow.

            + apply subvars_app_weak_r; apply subvars_app_weak_l.
              unfold correct_abs in correct; repnd.
              pose proof (subvars_free_vars_mk_instance vars bs2 rhs) as h.
              repeat (autodimp h hyp).

              (*
            + pose proof (subset_get_markers_mk_instance vars bs2 rhs) as h.
              repeat (autodimp h hyp).
              introv k; apply h in k; allrw in_app_iff; allsimpl; allrw in_app_iff; dorn k; tcsp.
              right.
              apply get_markers_if_found_entry in Heqcsl1; apply Heqcsl1 in k; sp.
               *)

            + allrw @nt_wf_NCompOp; unfold nobnd.
              eexists; eexists; eexists; eexists; dands; eauto.
              apply nt_wf_eq.
              eapply wf_mk_instance; eauto.
              inversion wf3 as [|? ? imp]; auto.
              introv i; apply bt_wf_eq; apply imp; auto.
        }

        { SSSCase "NArithOp".

          destruct bs; try (complete (allsimpl; dcwf h));[].
          destruct b as [l t]; try (complete (allsimpl; ginv));[].
          destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; dcwf h));[].

          allrw @nt_wf_NArithOp; exrepnd; allunfold @nobnd; ginv; fold_terms.
          allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.

          dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

          - SSSSCase "Can".
            simpl in comp.
            dcwf h;[]; allsimpl.
            apply compute_step_arithop_success_can_can in comp;
              exrepnd; subst; allsimpl; dands; auto;
              autorewrite with slow; eauto 3 with slow.

          - SSSSCase "NCan".
            allsimpl; dcwf h;[]; allsimpl; tcsp; ginv.
            remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
              symmetry in Heqcomp1; destruct comp1; allsimpl; ginv.
            apply (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) in Heqcomp1;
              repnd; tcsp; eauto 3 with slow;[].
            dands.

            { allsimpl; allrw remove_nvars_nil_l; allrw subvars_app_l.
              dands; eauto with slow. }

            { allsimpl; allrw subset_app; dands; eauto 3 with slow.
              apply nt_wf_NArithOp; unfold nobnd; eexists; eexists; dands; eauto. }

            (*
            { repeat (rw @nt_wf_oterm_iff); allsimpl; intro w; repnd; cpx.
              dands; tcsp.
              introv k; repndors; subst; tcsp.
              constructor.
              pose proof (w (bterm [] (oterm (NCan ncan3) bs2))) as h.
              autodimp h hyp.
              inversion h; subst; sp. }
             *)

          - SSSSCase "Exc".
            allsimpl; dcwf h;[]; allsimpl; ginv; allsimpl;
            allrw remove_nvars_nil_l; dands; eauto with slow.

          - SSSSCase "Abs".
            allsimpl; dcwf h;[].
            csunf comp; allsimpl.
            remember (compute_step_lib lib abs3 bs2) as csl;
              symmetry in Heqcsl; destruct csl; allsimpl; ginv; simpl.

            applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
            applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
            unfold matching_entry in Heqcsl0; repnd.

            allrw remove_nvars_nil_l; allrw app_nil_r;
            allrw subvars_app_l; allrw subset_app; dands; eauto 4 with slow.

            + apply subvars_app_weak_r.
              unfold correct_abs in correct; repnd.
              pose proof (subvars_free_vars_mk_instance vars bs2 rhs) as h.
              repeat (autodimp h hyp).

              (*
            + pose proof (subset_get_markers_mk_instance vars bs2 rhs) as h.
              repeat (autodimp h hyp).
              introv k; apply h in k; allrw in_app_iff; allsimpl; allrw in_app_iff; dorn k; tcsp.
              right.
              apply get_markers_if_found_entry in Heqcsl1; apply Heqcsl1 in k; sp.
               *)

            + allrw @nt_wf_NArithOp; unfold nobnd; eexists; eexists; dands; eauto.
              apply nt_wf_eq.
              eapply wf_mk_instance; eauto.
              inversion wf1 as [|? ? imp]; auto.
              introv i; apply bt_wf_eq; apply imp; auto.
        }

        { SSSCase "NCanTest".

          clear ind; simpl in comp.
          apply compute_step_can_test_success in comp; exrepnd; subst; fold_terms.

          allrw @nt_wf_eq.
          allrw @wf_can_test_iff; repnd; simpl.
          allrw remove_nvars_nil_l; allrw app_nil_r.
          allrw @oappl_cons_oappl.
          allrw @oappl_app_as_oapp.
          allrw @oeqset_oappl_cons.

          remember (canonical_form_test_for c can2) as cft;
            destruct cft; dands; simpl;
            eauto 4 with slow;
            apply implies_osubset_oapp; right;
            apply implies_osubset_oapp; try (complete (left; eauto 3 with slow)).
        }

      * SSCase "NCan".
        allsimpl.
        remember (compute_step lib (oterm (NCan ncan2) bts)) as cs;
          symmetry in Heqcs; destruct cs; allsimpl; ginv.
        pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as h;
          repeat (autodimp h hyp); repnd; tcsp; eauto 3 with slow.
        allrw @nt_wf_oterm_iff; repnd; allsimpl.
        pose proof (wf (nobnd (oterm (NCan ncan2) bts))) as w1; autodimp w1 hyp.
        allrw @bt_wf_iff.
        apply h in Heqcs; clear h; repnd; auto.
        allrw remove_nvars_nil_l; allsimpl.
        allrw @oappl_cons_oappl.

        dands.

        { allsimpl; allrw remove_nvars_nil_l; allrw subvars_app_l.
          dands; eauto 3 with slow. }

        { allsimpl; allrw subset_app; dands; eauto with slow. }

        { introv i; repndors; subst; tcsp. }

      * SSCase "Exc".
        allsimpl.
        allrw @nt_wf_oterm_iff; repnd; allsimpl.
        pose proof (wf (nobnd (oterm Exc bts))) as w1; autodimp w1 hyp.
        allrw @bt_wf_iff.
        allrw remove_nvars_nil_l.
        allrw @oappl_cons_oappl.

        apply compute_step_catch_success in comp; dorn comp; exrepnd; subst;
        allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; dands; auto.

        { allrw subvars_app_l; dands; eauto with slow.
          pose proof (eqvars_free_vars_disjoint b [(v,e)]) as h.
          allrw @fold_subst.
          apply eqvars_sym in h.
          eapply subvars_eqvars;[|exact h]; clear h.
          simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
          boolvar; simpl; allrw app_nil_r; auto; allrw subvars_app_l; dands;
          eauto with slow. }

        (*
        { allrw subset_app; dands; eauto 4 with slow.
          pose proof (get_markers_lsubst b [(v,e)]) as h.
          allrw @fold_subst; allsimpl; allrw app_nil_r; auto.
          introv i; apply h in i; allrw in_app_iff; sp. }
         *)

        { allrw @nt_wf_eq.
          allrw @wf_exception_iff.
          allrw @wf_atom_eq; repnd.
          pose proof (wf (nobnd a)) as w2; autodimp w2 hyp.
          pose proof (wf (bterm [v] b)) as w3; autodimp w3 hyp.
          allrw @bt_wf_iff; allrw @nt_wf_eq.
          dands; auto.
          - apply wf_term_subst; auto.
          - apply wf_exception; auto.
        }

        { apply subvars_app_weak_l; auto. }

      * SSCase "Abs".
        allsimpl.
        rw @compute_step_eq_unfold in comp; allsimpl.
        remember (compute_step_lib lib abs2 bts) as csl;
          symmetry in Heqcsl; destruct csl; allsimpl; ginv.
        allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r;
        allrw subvars_app_l; allrw subset_app.

        applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
        applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
        unfold matching_entry in Heqcsl0; repnd.
        unfold correct_abs in correct; repnd.

        dands; eauto 4 with slow.

        { pose proof (subvars_free_vars_mk_instance vars bts rhs) as h.
          repeat (autodimp h hyp).
          eapply subvars_trans;[exact h|].
          apply subvars_app_weak_l; auto. }

        (*
        { pose proof (subset_get_markers_mk_instance vars bts rhs) as h.
          repeat (autodimp h hyp).
          eapply subset_trans;[exact h|].
          apply subset_app; dands; introv i; allrw in_app_iff; allsimpl; allrw in_app_iff; sp.
          right.
          apply get_markers_if_found_entry in Heqcsl1; apply Heqcsl1 in i; sp. }
         *)

        { allrw @nt_wf_oterm_iff; allsimpl; repnd.
          dands; tcsp.
          introv k; repndors; subst; tcsp.
          constructor.
          apply nt_wf_eq.
          eapply wf_mk_instance; eauto.
          pose proof (wf (bterm [] (oterm (Abs abs2) bts))) as h; clear wf.
          autodimp h hyp.
          inversion h as [? ? w]; subst; clear h.
          apply nt_wf_oterm_iff in w; repnd.
          introv k; apply w in k.
          apply bt_wf_eq; auto.
        }
      }

      { allsimpl.
        apply compute_step_fresh_success in comp; repnd; subst.
        repndors; exrepnd; subst; dands;
        try (complete (allsimpl; tcsp; eauto 4 with slow)).

        - allsimpl; allrw app_nil_r.
          rw @free_vars_pushdown_fresh; auto.

          (*
        - rw @get_markers_pushdown_fresh; simpl; eauto with slow.
*)

        - apply nt_wf_pushdown_fresh.
          apply nt_wf_fresh in wf; auto.

        - allsimpl; repnd; subst; allsimpl; allrw app_nil_r.
          pose proof (free_vars_subst_utokens x [(get_fresh_atom lib t, mk_var n)]) as h.
          apply (subars_remove_nvars_lr [n]) in h.
          eapply subvars_trans;[exact h|clear h].
          rw remove_nvars_app_r; simpl.
          rw remove_nvars_eq; rw app_nil_r.
          apply subars_remove_nvars_lr.
          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom lib t))) [n]) as k; repeat (autodimp k hyp); clear ind.
          { rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (k x) as h; clear k.
          allrw @nt_wf_fresh.
          repeat (autodimp h hyp; repnd).
          { apply nt_wf_subst; eauto 3 with slow. }
          rw @cl_subst_subst_aux in h0; eauto with slow; unfold subst_aux in h0.
          rw @cl_lsubst_aux_trivial2 in h0; eauto with slow.
          simpl in h0.
          eapply subvars_trans;[exact h0|].
          apply subvars_remove_nvars; eauto with slow.

          (*
        - allsimpl; repnd; subst; allsimpl; allrw app_nil_r.
          pose proof (get_markers_subst_utokens x [(get_fresh_atom t, mk_var n)]) as h.
          eapply subset_trans;[exact h|clear h]; simpl.
          rw app_nil_r.
          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as k; repeat (autodimp k hyp); clear ind.
          { rw @simple_size_subst; auto. }
          pose proof (k x) as h; clear k.
          autodimp h hyp; repnd.
          eapply subset_trans;[exact h1|].
          rw subset_app; dands; eauto with slow.
          unfold subst; eapply subset_trans;[apply get_markers_lsubst|].
          simpl; allrw app_nil_r; eauto with slow.
           *)

        - allsimpl; repnd; subst; allsimpl; allrw app_nil_r.
          allrw @nt_wf_fresh.
          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom lib t))) [n]) as k; repeat (autodimp k hyp); clear ind.
          { rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (k x) as h; clear k.
          repeat (autodimp h hyp); repnd.
          { apply nt_wf_subst; eauto 3 with slow. }
          allrw @nt_wf_eq.
          apply wf_subst_utokens; auto; eauto with slow.
      }

    + SCase "Exc".
      allsimpl; ginv; allsimpl; dands; auto.

    + SCase "Abs".
      allsimpl.

      applydup @compute_step_lib_success in comp; exrepnd; subst.
      applydup @found_entry_implies_matching_entry in comp1; auto.
      unfold matching_entry in comp0; repnd.
      unfold correct_abs in correct; repnd.

      dands.

      { pose proof (subvars_free_vars_mk_instance vars bs rhs) as h.
        repeat (autodimp h hyp). }

      { allrw @nt_wf_eq.
        allrw @wf_oterm_iff; repnd.
        eapply wf_mk_instance; eauto.
      }
Qed.

Lemma preserve_compute_step {p} :
  forall lib (t1 t2 : @NTerm p),
    compute_step lib t1 = csuccess t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv comp isp.
  pose proof (compute_step_preserves lib t1 t2) as h.
  repeat (autodimp h hyp); eauto 3 with slow; repnd.
  allunfold @isprogram; repnd.
  dands; auto.
  rw isp0 in h0.
  rw subvars_nil_r in h0; auto.
Qed.

Lemma computek_preserves_program {p} :
  forall lib k t1 t2,
    compute_at_most_k_steps lib k t1 = @csuccess p t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  induction k; intros ? ?  Hck Hpt1; inverts Hck as Hck; auto.
  remember (compute_at_most_k_steps lib k t1) as rec. destruct rec; inverts Hck as Hck.
  symmetry in Heqrec. inverts Hck as Hck. apply IHk in Heqrec; auto.
  apply preserve_compute_step in Hck; auto.
Qed.

Lemma preserve_program {p} :
  forall lib (t1 t2 : @NTerm p),
    computes_to_value lib t1 t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv Hcv Hpt1. inverts Hcv as Hcv. inverts Hcv as Hcv.
  apply computek_preserves_program in Hcv; auto.
Qed.

Lemma computek_preserves_program_exc {p} :
  forall lib a k (t1 t2 : @NTerm p),
    computes_to_exception_in_max_k_steps lib a t1 t2 k
    -> isprogram t1
    -> isprogram t2.
Proof.
  unfold computes_to_exception_in_max_k_steps, reduces_in_atmost_k_steps.
  introv c isp1; repnd.
  apply computek_preserves_program in c; auto.
  rw @isprogram_exception_iff in c; sp.
Qed.

Lemma preserve_program_exc {p} :
  forall lib a (t1 t2 : @NTerm p),
    computes_to_exception lib a t1 t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv Hcv Hpt1.
  inverts Hcv as Hcv.
  inverts Hcv as Hcv.
  apply computek_preserves_program in Hcv; auto.
  rw @isprogram_exception_iff in Hcv; sp.
Qed.

Lemma preserve_nt_wf_compute_step {p} :
  forall lib (t1 t2 : @NTerm p),
    compute_step lib t1 = csuccess t2
    -> nt_wf t1
    -> nt_wf t2.
Proof.
  introv comp w.
  pose proof (compute_step_preserves lib t1 t2) as h; sp.
Qed.

Lemma reduces_to_preserves_program {p} :
  forall lib t1 t2,
    @reduces_to p lib t1 t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv Hred Hisp. exrepnud Hred.
  apply computek_preserves_program in Hred0; auto.
Qed.
