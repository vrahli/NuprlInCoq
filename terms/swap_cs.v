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

Require Export substitution.
Require Export terms5.
Require Export sovar_alpha.



(* swaps fst and snd *)
Definition cs_swap : Type := choice_sequence_name * choice_sequence_name.

Definition swap_cs (r : cs_swap) (n : choice_sequence_name) : choice_sequence_name :=
  let (n1,n2) := r in
  if choice_sequence_name_deq n n1 then n2
  else if choice_sequence_name_deq n n2 then n1
       else n.

Definition swap_cs_can {o} (r : cs_swap) (can : @CanonicalOp o) : CanonicalOp :=
  match can with
  | Ncseq name => Ncseq (swap_cs r name)
  | _ => can
  end.

Definition swap_cs_nfo (sw : cs_swap) (nfo : SwapCsNfo) : SwapCsNfo :=
  match nfo with
  | MkSwapCsNfo n1 n2 => MkSwapCsNfo (swap_cs sw n1) (swap_cs sw n2)
  end.

(*Definition swap_cs_comp_seq_nfo1 (sw : cs_swap) (nfo : CompSeqNfo1) : CompSeqNfo1 :=
  match nfo with
  | MkCompSeqNfo1 n => MkCompSeqNfo1 (swap_cs sw (MkChoiceSequenceName n (cs_kind_seq l)))
  end.

Definition swap_cs_comp_seq_nfo2 (sw : cs_swap) (nfo : CompSeqNfo2) : CompSeqNfo2 :=
  match nfo with
  | MkCompSeqNfo2 n l k => MkCompSeqNfo2 (swap_cs sw (MkChoiceSequenceName n (cs_kind_seq l))) l k
  end.*)

Definition swap_cs_ncan (r : cs_swap) (ncan : NonCanonicalOp) : NonCanonicalOp :=
  match ncan with
  | NSwapCs2 nfo => NSwapCs2 (swap_cs_nfo r nfo)
(*  | NCompSeq1 nfo => NCompSeq1 (swap_cs_comp_seq_nfo1 r nfo)
  | NCompSeq2 nfo => NCompSeq2 (swap_cs_comp_seq_nfo2 r nfo)*)
  | _ => ncan
  end.

Definition swap_cs_op {o} (r : cs_swap) (op : @Opid o) : Opid :=
  match op with
  | Can can => Can (swap_cs_can r can)
  | NCan ncan => NCan (swap_cs_ncan r ncan)
  | _ => op
  end.

Fixpoint swap_cs_term {o} (r : cs_swap) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | oterm op bs => oterm (swap_cs_op r op) (map (swap_cs_bterm r) bs)
  end
with swap_cs_bterm {o} (r : cs_swap) (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (swap_cs_term r t)
       end.

Lemma free_vars_swap_cs_term {o} :
  forall (r : cs_swap) (t : @NTerm o),
    free_vars (swap_cs_term r t) = free_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @free_vars_swap_cs_term : slow.

Lemma closed_swap_cs_term {o} :
  forall r (t : @NTerm o),
    closed t
    -> closed (swap_cs_term r t).
Proof.
  introv cl.
  unfold closed in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_swap_cs_term : slow.

Lemma OpBindingsCan_swap_cs_can {o} :
  forall r (can : @CanonicalOp o),
    OpBindingsCan (swap_cs_can r can) = OpBindingsCan can.
Proof.
  destruct can; simpl; auto.
Qed.
Hint Rewrite @OpBindingsCan_swap_cs_can : slow.

Lemma OpBindingsNCan_swap_cs_ncan :
  forall r (ncan : NonCanonicalOp),
    OpBindingsNCan (swap_cs_ncan r ncan) = OpBindingsNCan ncan.
Proof.
  destruct ncan; simpl; auto.
Qed.
Hint Rewrite @OpBindingsNCan_swap_cs_ncan : slow.

Lemma OpBindings_swap_cs_op {o} :
  forall r (op : @Opid o),
    OpBindings (swap_cs_op r op) = OpBindings op.
Proof.
  destruct op as [can| | |]; simpl; tcsp; autorewrite with slow; auto.
Qed.
Hint Rewrite @OpBindings_swap_cs_op : slow.

Lemma implies_wf_term_swap_cs_term {o} :
  forall r (t : @NTerm o),
    wf_term t
    -> wf_term (swap_cs_term r t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "oterm".
    allrw @wf_oterm_iff.
    allrw map_map; unfold compose.
    autorewrite with slow.
    repnd; dands; auto.

    + rewrite <- wf0.
      apply eq_maps; introv i.
      destruct x; unfold num_bvars; simpl; auto.

    + introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *.
      apply wf_bterm_iff.
      eapply ind; eauto.
      apply wf in i1.
      allrw @wf_bterm_iff; tcsp.
Qed.
Hint Resolve implies_wf_term_swap_cs_term : slow.

Lemma implies_isprog_swap_cs_term {o} :
  forall r {t : @NTerm o},
    isprog t
    -> isprog (swap_cs_term r t).
Proof.
  introv isp.
  allrw @isprog_eq.
  destruct isp.
  split; dands; allrw @nt_wf_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_swap_cs_term : slow.

Definition swap_cs_cterm {o} r (ct : @CTerm o) : CTerm :=
  let (t,isp) := ct in
  mk_ct (swap_cs_term r t) (implies_isprog_swap_cs_term r isp).

Fixpoint swap_cs_sub {o} r (sub : @Sub o) :=
  match sub with
  | [] => []
  | (v,t) :: sub => (v, swap_cs_term r t) :: swap_cs_sub r sub
  end.

Lemma sub_find_swap_cs_sub {o} :
  forall r (sub : @Sub o) v,
    sub_find (swap_cs_sub r sub) v
    = match sub_find sub v with
      | Some t => Some (swap_cs_term r t)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
Qed.

Lemma sub_filter_swap_cs_sub {o} :
  forall r (sub : @Sub o) l,
    sub_filter (swap_cs_sub r sub) l
    = swap_cs_sub r (sub_filter sub l).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
  rewrite IHsub; simpl; auto.
Qed.

Lemma lsubst_aux_swap_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst_aux (swap_cs_term r t) (swap_cs_sub r sub)
    = swap_cs_term r (lsubst_aux t sub).
Proof.
  nterm_ind t as [v|t op ind] Case; introv; simpl; auto.

  { Case "vterm".
    rewrite sub_find_swap_cs_sub.
    destruct (sub_find sub v); auto. }

  Case "oterm".
  f_equal.
  allrw map_map; unfold compose; simpl.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  rewrite sub_filter_swap_cs_sub.
  erewrite ind; eauto.
Qed.

Lemma bound_vars_swap_cs_term {o} :
  forall r (t : @NTerm o),
    bound_vars (swap_cs_term r t) = bound_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @bound_vars_swap_cs_term : slow.

Lemma allvars_swap_cs_term {o} :
  forall r (t : @NTerm o),
    allvars (swap_cs_term r t) = allvars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @allvars_swap_cs_term : slow.

Lemma all_vars_swap_cs_term {o} :
  forall r (t : @NTerm o),
    all_vars (swap_cs_term r t) = all_vars t.
Proof.
  introv; unfold all_vars; autorewrite with slow; auto.
Defined.
Hint Rewrite @all_vars_swap_cs_term : slow.

Lemma flat_map_free_vars_range_swap_cs_sub {o} :
  forall r (sub : @Sub o),
    flat_map free_vars (range (swap_cs_sub r sub))
    = flat_map free_vars (range sub).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl.
  rewrite IHsub; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_range_swap_cs_sub : slow.

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

Lemma swap_cs_sub_if_allvars_sub {o} :
  forall r (sub : @Sub o),
    allvars_sub sub
    -> swap_cs_sub r sub = sub.
Proof.
  induction sub; introv allvs; simpl in *; auto; repnd; simpl in *.
  apply allvars_sub_cons in allvs; repnd.
  rewrite IHsub; auto.
  apply isvariable_implies in allvs0; exrepnd; subst; simpl; auto.
Qed.

Lemma lsubst_aux_swap_cs_term_if_allvars_sub {o} :
  forall r (t : @NTerm o) sub,
    allvars_sub sub
    -> lsubst_aux (swap_cs_term r t) sub
       = swap_cs_term r (lsubst_aux t sub).
Proof.
  introv allvs.
  rewrite <- lsubst_aux_swap_cs_term.
  rewrite swap_cs_sub_if_allvars_sub; auto.
Qed.

Lemma allvars_sub_var_ren {o} :
  forall l k, @allvars_sub o (var_ren l k).
Proof.
  introv.
  introv i.
  apply in_var_ren in i; exrepnd; subst; eexists; eauto.
Qed.
Hint Resolve allvars_sub_var_ren : slow.

Lemma change_bvars_alpha_swap_cs_term {o} :
  forall l r (t : @NTerm o),
    change_bvars_alpha l (swap_cs_term r t)
    = swap_cs_term r (change_bvars_alpha l t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl.
  erewrite ind;eauto; autorewrite with slow.
  f_equal.
  rewrite lsubst_aux_swap_cs_term_if_allvars_sub; eauto 3 with slow.
Qed.

Lemma swap_cs_idem :
  forall (r    : cs_swap)
         (name : choice_sequence_name),
    swap_cs r (swap_cs r name) = name.
Proof.
  destruct r; introv; simpl; boolvar; subst; tcsp.
Qed.
Hint Rewrite swap_cs_idem : slow.

Lemma swap_cs_nfo_idem :
  forall (r   : cs_swap)
         (nfo : SwapCsNfo),
    swap_cs_nfo r (swap_cs_nfo r nfo) = nfo.
Proof.
  introv; destruct nfo; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite swap_cs_nfo_idem : slow.

Lemma swap_cs_op_idem {o} :
  forall (r  : cs_swap)
         (op : @Opid o),
    swap_cs_op r (swap_cs_op r op) = op.
Proof.
  destruct op; simpl; auto;
    try destruct c; try destruct n; simpl; auto; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_op_idem : slow.

Lemma swap_cs_term_idem {o} :
  forall (r : cs_swap)
         (t : @NTerm o),
    swap_cs_term r (swap_cs_term r t) = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  autorewrite with slow.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_map_l; introv i.
  destruct x; apply ind in i.
  simpl; f_equal; auto.
Qed.
Hint Rewrite @swap_cs_term_idem : slow.

Lemma swap_cs_cterm_idem {o} :
  forall (r : cs_swap)
         (t : @CTerm o),
    swap_cs_cterm r (swap_cs_cterm r t) = t.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_cterm_idem : slow.

Lemma lsubst_swap_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst (swap_cs_term r t) (swap_cs_sub r sub)
    = swap_cs_term r (lsubst t sub).
Proof.
  introv.
  unfold lsubst; autorewrite with slow.
  destruct (dec_disjointv (bound_vars t) (flat_map free_vars (range sub)));
    try rewrite lsubst_aux_swap_cs_term; auto.
  rewrite change_bvars_alpha_swap_cs_term.
  rewrite lsubst_aux_swap_cs_term; auto.
Qed.

Lemma swap_cs_term_nat {o} :
  forall n sw,
    @swap_cs_cterm o sw (mkc_nat n) = mkc_nat n.
Proof.
  introv; apply cterm_eq; auto.
Qed.
Hint Rewrite @swap_cs_term_nat : slow.

Lemma subst_swap_cs_term {o} :
  forall r (t : @NTerm o) v u,
    subst (swap_cs_term r t) v (swap_cs_term r u)
    = swap_cs_term r (subst t v u).
Proof.
  introv.
  unfold subst; rewrite <- lsubst_swap_cs_term; simpl; auto.
Qed.

Lemma implies_nt_wf_swap_cs_term {o} :
  forall sw (b : @NTerm o),
    nt_wf b
    -> nt_wf (swap_cs_term sw b).
Proof.
  nterm_ind b as [v|op bs ind] Case; introv wf; simpl in *; tcsp.
  inversion wf as [|? ? imp eqm]; subst; clear wf.
  constructor.
  { introv i; apply in_map_iff in i; exrepnd; subst.
    destruct a; simpl; constructor; eapply ind; eauto.
    apply imp in i1; inversion i1; subst; auto. }
  { rewrite map_map; unfold compose; autorewrite with slow.
    rewrite <- eqm; apply eq_maps; introv i; destruct x; simpl; tcsp. }
Qed.
Hint Resolve implies_nt_wf_swap_cs_term : slow.

Lemma implies_isprogram_swap_cs_term {o} :
  forall sw (b : @NTerm o),
    isprogram b
    -> isprogram (swap_cs_term sw b).
Proof.
  introv isp.
  destruct isp as [c wf]; constructor; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_swap_cs_term : slow.

Lemma implies_iscan_swap_cs_term {o} :
  forall sw (b : @NTerm o),
    iscan b
    -> iscan (swap_cs_term sw b).
Proof.
  introv i.
  apply iscan_implies in i; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve implies_iscan_swap_cs_term : slow.

Lemma implies_isvalue_swap_cs_term {o} :
  forall sw (b : @NTerm o),
    isvalue b
    -> isvalue (swap_cs_term sw b).
Proof.
  introv isv.
  destruct isv as [isp isc].
  constructor; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_swap_cs_term : slow.

Lemma get_utokens_o_swap_cs_op {o} :
  forall r (op : @Opid o),
    get_utokens_o (swap_cs_op r op) = get_utokens_o op.
Proof.
  introv.
  destruct op; simpl; tcsp.
  destruct c; simpl; tcsp.
Qed.
Hint Rewrite @get_utokens_o_swap_cs_op : slow.
