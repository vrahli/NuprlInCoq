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



Require Export sequents2.
Require Export computation_lib_extends.
(*Require Export sequents_lib.*)
Require Export sequents_tacs2.
Require Export per_props_util.


Definition renaming : Type := opname * opname.

Definition rename_opname (r : renaming) (n : opname) : opname :=
  let (n1,n2) := r in
  if String.string_dec n n1 then n2
  else if String.string_dec n n2 then n1
       else n.

Definition rename_opabs (r : renaming) (a : opabs) : opabs :=
  match a with
  | Build_opabs name params sign => Build_opabs (rename_opname r name) params sign
  end.

Definition rename_op {o} (r : renaming) (op : @Opid o) : Opid :=
  match op with
  | Abs abs => Abs (rename_opabs r abs)
  | _ => op
  end.

Fixpoint rename_term {o} (r : renaming) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | oterm op bs => oterm (rename_op r op) (map (rename_bterm r) bs)
  end
with rename_bterm {o} (r : renaming) (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (rename_term r t)
       end.

Fixpoint rename_soterm {o} (r : renaming) (t : @SOTerm o) : SOTerm :=
  match t with
  | sovar v ts => sovar v (map (rename_soterm r) ts)
  | soterm op bs => soterm (rename_op r op) (map (rename_sobterm r) bs)
  end
with rename_sobterm {o} (r : renaming) (bt : @SOBTerm o) : SOBTerm :=
       match bt with
       | sobterm vs t => sobterm vs (rename_soterm r t)
       end.

Lemma rename_term_apply_list {o} :
  forall (r : renaming) ts (t : @NTerm o),
    rename_term r (apply_list t ts)
    = apply_list (rename_term r t) (map (rename_term r) ts).
Proof.
  induction ts; introv; simpl; tcsp.
  rewrite IHts; simpl; auto.
Qed.

Lemma soterm2nterm_rename_soterm {o} :
  forall (r : renaming) (t : @SOTerm o),
    soterm2nterm (rename_soterm r t)
    = rename_term r (soterm2nterm t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl in *; tcsp.

  - Case "sovar".
    rewrite rename_term_apply_list; simpl.
    allrw map_map; unfold compose; simpl.
    f_equal.
    apply eq_maps; tcsp.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose; simpl.
    apply eq_maps; introv i; simpl.
    destruct x; simpl.
    apply ind in i; f_equal; auto.
Qed.

Lemma free_vars_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    free_vars (rename_term r t) = free_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @free_vars_rename_term : slow.

Lemma closed_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    closed t
    -> closed (rename_term r t).
Proof.
  introv cl.
  unfold closed in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_rename_term : slow.

Lemma get_utokens_o_rename_op {o} :
  forall (r : renaming) (op : @Opid o),
    get_utokens_o (rename_op r op) = get_utokens_o op.
Proof.
  destruct op; simpl; tcsp.
Qed.
Hint Rewrite @get_utokens_o_rename_op : slow.

Lemma get_utokens_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    get_utokens (rename_term r t) = get_utokens t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  autorewrite with slow; f_equal.
  induction bs; simpl in *; auto.
  rewrite IHbs; auto;[|introv xx; eapply ind;eauto].
  destruct a; simpl; f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @get_utokens_rename_term : slow.

Lemma implies_noutokens_rename_term {o} :
  forall r (t : @NTerm o),
    noutokens t
    -> noutokens (rename_term r t).
Proof.
  introv n.
  unfold noutokens in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_noutokens_rename_term : slow.

Lemma OpBindings_rename_op {o} :
  forall r (op : @Opid o),
    OpBindings (rename_op r op) = OpBindings op.
Proof.
  destruct op as [| | |abs]; simpl; tcsp.
  destruct abs; simpl; auto.
Qed.
Hint Rewrite @OpBindings_rename_op : slow.

Lemma implies_wf_term_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    wf_term t
    -> wf_term (rename_term r t).
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
Hint Resolve implies_wf_term_rename_term : slow.

Lemma implies_wf_soterm_rename_soterm {o} :
  forall (r : renaming) (t : @SOTerm o),
    wf_soterm t
    -> wf_soterm (rename_soterm r t).
Proof.
  introv wf.
  unfold wf_soterm in *; simpl in *.
  rewrite soterm2nterm_rename_soterm.
  eauto 3 with slow.
Qed.
Hint Resolve implies_wf_soterm_rename_soterm : slow.

Lemma so_free_vars_rename_soterm {o} :
  forall (r : renaming) (t : @SOTerm o),
    so_free_vars (rename_soterm r t) = so_free_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    autorewrite with list; f_equal.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; tcsp.

  - Case "soterm".
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; tcsp.
    destruct x; simpl.
    apply ind in i.
    rewrite i; auto.
Qed.
Hint Rewrite @so_free_vars_rename_soterm : slow.

Lemma implies_socovered_rename_soterm {o} :
  forall r (t : @SOTerm o) vars,
    socovered t vars
    -> socovered (rename_soterm r t) vars.
Proof.
  introv cov.
  unfold socovered in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_socovered_rename_soterm : slow.

Lemma get_utokens_so_rename_soterm {o} :
  forall (r : renaming) (t : @SOTerm o),
    get_utokens_so (rename_soterm r t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    allrw flat_map_map; unfold compose; autorewrite with slow in *.
    apply eq_flat_maps; introv i; tcsp.

  - Case "soterm".
    allrw flat_map_map; unfold compose; autorewrite with slow in *.
    f_equal.
    apply eq_flat_maps; introv i; tcsp.
    destruct x; simpl.
    apply ind in i.
    rewrite i; auto.
Qed.
Hint Rewrite @get_utokens_so_rename_soterm : slow.

Lemma implies_no_utokens_rename_soterm {o} :
  forall r (t : @SOTerm o),
    no_utokens t
    -> no_utokens (rename_soterm r t).
Proof.
  introv.
  unfold no_utokens in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_no_utokens_rename_soterm : slow.

Lemma opabs_params_rename_opabs :
  forall r (opabs : opabs),
    opabs_params (rename_opabs r opabs) = opabs_params opabs.
Proof.
  destruct opabs; simpl; auto.
Qed.
Hint Rewrite opabs_params_rename_opabs : slow.

Lemma opabs_sign_rename_opabs :
  forall r (opabs : opabs),
    opabs_sign (rename_opabs r opabs) = opabs_sign opabs.
Proof.
  destruct opabs; simpl; auto.
Qed.
Hint Rewrite opabs_sign_rename_opabs : slow.

Lemma rename_correct {o} :
  forall {opabs vars rhs} (r : renaming) (correct : @correct_abs o opabs vars rhs),
    correct_abs (rename_opabs r opabs) vars (rename_soterm r rhs).
Proof.
  introv cor.
  unfold correct_abs in *; simpl in *; repnd; dands; eauto 3 with slow;
    autorewrite with slow in *; auto.
Qed.
Hint Resolve rename_correct : slow.

Lemma implies_isprog_rename_term {o} :
  forall r (t : @NTerm o),
    isprog t
    -> isprog (rename_term r t).
Proof.
  introv isp.
  allrw @isprog_eq.
  destruct isp.
  split; dands; allrw @nt_wf_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_rename_term : slow.

Lemma rename_opname_idem :
  forall r (n : opname),
    rename_opname r (rename_opname r n) = n.
Proof.
  introv; unfold rename_opname; destruct r; boolvar; subst; tcsp.
Qed.
Hint Rewrite rename_opname_idem : slow.

Lemma rename_opabs_idem :
  forall r (a : opabs),
    rename_opabs r (rename_opabs r a) = a.
Proof.
  introv; destruct a; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite rename_opabs_idem : slow.

Lemma rename_opid_idem {o} :
  forall r (op : @Opid o),
    rename_op r (rename_op r op) = op.
Proof.
  introv; destruct op; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_opid_idem : slow.

Lemma rename_term_idem {o} :
  forall r (t : @NTerm o),
    rename_term r (rename_term r t) = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; tcsp.

  - Case "oterm".
    autorewrite with slow in *; allrw map_map; unfold compose.
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    erewrite ind; eauto.
Qed.
Hint Rewrite @rename_term_idem : slow.

Definition rename_cterm {o} r (ct : @CTerm o) : CTerm :=
  let (t,isp) := ct in
  mk_ct (rename_term r t) (implies_isprog_rename_term r t isp).

Lemma rename_cterm_idem {o} :
  forall r (t : @CTerm o),
    rename_cterm r (rename_cterm r t) = t.
Proof.
  introv; destruct t; simpl.
  apply cterm_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_cterm_idem : slow.

Definition rename_choice_seq_val {o} (r : renaming) (v : @ChoiceSeqVal o) : ChoiceSeqVal :=
  rename_cterm r v.

Definition rename_choice_seq_vals {o} (r : renaming) (vals : @ChoiceSeqVals o) : ChoiceSeqVals :=
  map (rename_choice_seq_val r) vals.

Definition rename_restriction_pred {o} (r : renaming) (restr : @RestrictionPred o) : RestrictionPred :=
  fun n v => restr n (rename_cterm r v).

Lemma rename_correct_default {o}
      (r   : renaming)
      {d   : nat -> ChoiceSeqVal}
      {typ : @RestrictionPred o}
      (M   : forall n : nat, typ n (d n))
  : forall n : nat, rename_restriction_pred r typ n (rename_choice_seq_val r (d n)).
Proof.
  introv.
  unfold rename_restriction_pred, rename_choice_seq_val.
  autorewrite with slow; auto.
Defined.

Definition rename_choice_seq_restriction {o} (r : renaming) (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match restr with
  | csc_type d typ M =>
    csc_type (fun n => rename_choice_seq_val r (d n))
             (rename_restriction_pred r typ)
             (rename_correct_default r M)
  | csc_coq_law f => csc_coq_law (fun n => rename_cterm r (f n))
  end.

Definition rename_choice_seq_entry {o} (r : renaming) (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkChoiceSeqEntry _ (rename_choice_seq_vals r vals) (rename_choice_seq_restriction r restr)
  end.

Definition rename_library_entry {o} (r : renaming) (e : @library_entry o) : library_entry :=
  match e with
  | lib_cs name e => lib_cs name (rename_choice_seq_entry r e)
  | lib_abs opabs vars rhs correct =>
    lib_abs (rename_opabs r opabs) vars (rename_soterm r rhs) (rename_correct r correct)
  end.

Definition rename_lib {o} (r : renaming) (l : @library o) : library :=
  map (rename_library_entry r) l.

Definition rename_conclusion {o} (r : renaming) (c : @conclusion o) : conclusion :=
  match c with
  | concl_ext t e => concl_ext (rename_term r t) (rename_term r e)
  | concl_typ t => concl_typ (rename_term r t)
  end.

Definition rename_hypothesis {o} (r : renaming) (h : @hypothesis o) : hypothesis :=
  match h with
  | Build_hypothesis _ n h t l => Build_hypothesis _ n h (rename_term r t) l
  end.

Definition rename_barehypotheses {o} (r : renaming) (H : @barehypotheses o) : barehypotheses :=
  map (rename_hypothesis r) H.

Definition rename_baresequent {o} (r : renaming) (s : @baresequent o) : baresequent :=
  match s with
  | Build_baresequent _ hyps concl =>
    Build_baresequent _ (rename_barehypotheses r hyps) (rename_conclusion r concl)
  end.

Lemma rename_barehypotheses_snoc {o} :
  forall r (H : @bhyps o) h,
    rename_barehypotheses r (snoc H h)
    = snoc (rename_barehypotheses r H) (rename_hypothesis r h).
Proof.
  induction H; introv; simpl; auto.
  rewrite IHlist; auto.
Defined.

Lemma vars_hyps_rename_barehypotheses {o} :
  forall r (H : @bhyps o),
    vars_hyps (rename_barehypotheses r H)
    = vars_hyps H.
Proof.
  induction H; introv; simpl; tcsp.
  allrw.
  destruct a; simpl; auto.
Qed.
Hint Rewrite @vars_hyps_rename_barehypotheses : slow.

Lemma nh_vars_hyps_rename_barehypotheses {o} :
  forall r (H : @bhyps o),
    nh_vars_hyps (rename_barehypotheses r H)
    = nh_vars_hyps H.
Proof.
  introv; unfold nh_vars_hyps; simpl.
  induction H; simpl; tcsp.
  destruct a; simpl in *; unfold is_nh in *; simpl.
  destruct (negb hidden); simpl; tcsp.
  rewrite IHlist; auto.
Qed.
Hint Rewrite @nh_vars_hyps_rename_barehypotheses : slow.

Lemma htyp_rename_hypothesis {o} :
  forall r (h : @hypothesis o),
    htyp (rename_hypothesis r h)
    = rename_term r (htyp h).
Proof.
  destruct h; simpl; tcsp.
Qed.
Hint Rewrite @htyp_rename_hypothesis : slow.

Lemma hvar_rename_hypothesis {o} :
  forall r (h : @hypothesis o),
    hvar (rename_hypothesis r h)
    = hvar h.
Proof.
  destruct h; simpl; tcsp.
Qed.
Hint Rewrite @hvar_rename_hypothesis : slow.

Lemma implies_isprog_vars_rename_term {o} :
  forall vs r (t : @NTerm o),
    isprog_vars vs t
    -> isprog_vars vs (rename_term r t).
Proof.
  introv isp.
  unfold isprog_vars in *; autorewrite with slow; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_vars_rename_term : slow.

Lemma wf_hypotheses_rename_barehypotheses {o} :
  forall r (H : @barehypotheses o),
    wf_hypotheses H
    -> wf_hypotheses (rename_barehypotheses r H).
Proof.
  induction H using rev_list_indT; simpl; introv wf; auto.
  inversion wf as [|? ? isp ni wf1 e]; ginv; clear wf.
  apply snoc_inj in e; repnd; subst; simpl.
  rewrite rename_barehypotheses_snoc.
  constructor; simpl; auto; eauto 3 with slow;
    autorewrite with slow in *; eauto 3 with slow.
Qed.
Hint Resolve wf_hypotheses_rename_barehypotheses : slow.

Lemma wf_concl_rename_conclusion {o} :
  forall r (concl : @conclusion o),
    wf_concl concl
    -> wf_concl (rename_conclusion r concl).
Proof.
  destruct concl; introv wf; simpl in *;
    unfold wf_concl in *; simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve wf_concl_rename_conclusion : slow.

Lemma wf_sequent_rename {o} :
  forall r (s : @baresequent o),
    wf_sequent s -> wf_sequent (rename_baresequent r s).
Proof.
  introv wf.
  destruct s; simpl in *.
  unfold wf_sequent in *; simpl in *.
  allrw @vswf_hypotheses_nil_eq.
  repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve wf_sequent_rename : slow.

Definition rename_sequent {o} (r : renaming) (cs : @sequent o) : sequent :=
  let (s,wf) := cs in
  existT wf_sequent (rename_baresequent r s) (wf_sequent_rename r s wf).

Lemma closed_type_sequent_rename {o} :
  forall r (s : @sequent o),
    closed_type_sequent s -> closed_type_sequent (rename_sequent r s).
Proof.
  introv cl.
  unfold closed_type_sequent in *; simpl in *.
  unfold closed_type_baresequent in *; simpl in *.
  destruct s; simpl in *; autorewrite with slow in *.
  unfold closed_type in *; simpl in *; autorewrite with slow in *.
  destruct x; simpl in *; autorewrite with slow in *.
  unfold covered in *; simpl in *.
  destruct concl in *; simpl in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_type_sequent_rename : slow.

Definition rename_ctsequent {o} (r : renaming) (cs : @ctsequent o) : ctsequent :=
  let (s,c) := cs in
  existT closed_type_sequent (rename_sequent r s) (closed_type_sequent_rename r s c).

Lemma closed_extract_ctsequent_rename {o} :
  forall r (s : @ctsequent o),
    closed_extract_ctsequent s -> closed_extract_ctsequent (rename_ctsequent r s).
Proof.
  introv cl.
  unfold closed_extract_ctsequent in *; simpl in *.
  destruct s; simpl in *.
  unfold closed_extract_sequent in *; simpl in *.
  destruct x; simpl in *.
  destruct x; simpl in *.
  unfold closed_extract_baresequent in *; simpl in *.
  unfold closed_extract in *; simpl in *.
  destruct concl in *; simpl in *; tcsp; autorewrite with slow in *.
  unfold covered in *; simpl in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_extract_ctsequent_rename : slow.

Definition rename_csequent {o} (r : renaming) (cs : @csequent o) : csequent :=
  let (s,c) := cs in
  existT closed_extract_ctsequent (rename_ctsequent r s) (closed_extract_ctsequent_rename r s c).

(*Eval compute in (rename_term_idem
                   ("member", "MEMBER")
                   (mk_uall (vterm nvarT) nvart mk_axiom)).*)

Lemma rename_soterm_idem {o} :
  forall r (t : @SOTerm o),
    rename_soterm r (rename_soterm r t) = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; tcsp.

  - Case "soterm".
    autorewrite with slow; allrw map_map; unfold compose.
    f_equal.
    apply eq_map_l; introv i; destruct x; simpl.
    erewrite ind; eauto.
Qed.
Hint Rewrite @rename_soterm_idem : slow.

Lemma rename_choice_seq_vals_idem {o} :
  forall r (vals : @ChoiceSeqVals o),
    rename_choice_seq_vals r (rename_choice_seq_vals r vals) = vals.
Proof.
  introv; unfold rename_choice_seq_vals.
  allrw @map_map; unfold compose; simpl.
  rewrite <- (map_id vals) at 2.
  apply eq_maps; introv i.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_choice_seq_vals_idem : slow.

Lemma rename_choice_seq_val_idem {o} :
  forall r (v : @ChoiceSeqVal o),
    rename_choice_seq_val r (rename_choice_seq_val r v) = v.
Proof.
  introv; unfold rename_choice_seq_val; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_choice_seq_val_idem : slow.

Definition transport_typd {o}
           {d1 d2 : nat -> @ChoiceSeqVal o}
           {typ1 typ2 : RestrictionPred}
           (typd1 : forall n, typ1 n (d1 n))
           (eqd : forall n, d1 n = d2 n)
           (eqt : forall n v, typ1 n v = typ2 n v) : forall n, typ2 n (d2 n).
Proof.
  introv.
  rewrite <- eqd.
  rewrite <- eqt.
  auto.
Defined.

Lemma implies_eq_csc_type {o} :
  forall (d1 d2 : nat -> @ChoiceSeqVal o)
         (typ1 typ2 : RestrictionPred)
         (typd1 : forall n, typ1 n (d1 n))
         (eqd : forall n, d1 n = d2 n)
         (eqt : forall n v, typ1 n v = typ2 n v),
    csc_type d1 typ1 typd1 = csc_type d2 typ2 (transport_typd typd1 eqd eqt).
Proof.
  introv.

  assert (d1 = d2) as eqd1.
  { apply functional_extensionality; tcsp. }
  subst.

  assert (typ1 = typ2) as eqt1.
  { apply functional_extensionality; introv.
    apply functional_extensionality; introv; tcsp. }
  subst.

  f_equal.
  unfold transport_typd.
  apply functional_extensionality_dep; introv; simpl.

  assert (eqd x = eq_refl) as xx by apply UIP.
  rewrite xx; simpl.

  assert (eqt x (d2 x) = eq_refl) as yy by apply UIP.
  rewrite yy; simpl; auto.
Qed.

Lemma rename_choice_seq_restriction_idem {o} :
  forall r (restr : @ChoiceSeqRestriction o),
    rename_choice_seq_restriction r (rename_choice_seq_restriction r restr)
    = restr.
Proof.
  introv.
  destruct restr; simpl.

  {

    assert (forall n, rename_choice_seq_val r (rename_choice_seq_val r (d n)) = d n) as eqd.
    {
      introv; autorewrite with slow; auto.
    }

    assert (forall n v, rename_restriction_pred r (rename_restriction_pred r typ) n v = typ n v) as eqt.
    {
      introv; unfold rename_restriction_pred; simpl.
      autorewrite with slow; auto.
    }

    rewrite (implies_eq_csc_type
               (fun n => rename_choice_seq_val r (rename_choice_seq_val r (d n)))
               d
               (rename_restriction_pred r (rename_restriction_pred r typ))
               typ
               (rename_correct_default r (rename_correct_default r typd))
               eqd eqt).

    f_equal; simpl.
    unfold transport_typd; simpl.
    unfold rename_correct_default; simpl.
    unfold rename_restriction_pred in *; simpl in *.
    unfold rename_choice_seq_val in *.

    apply functional_extensionality_dep; introv.

    remember (eqd x) as eqdx; clear Heqeqdx.
    clear eqd.

    remember (eqt x) as eqtx; clear Heqeqtx.
    clear eqt.

    apply proof_irrelevance.
  }

  {
    f_equal.
    apply functional_extensionality; introv.
    autorewrite with slow; auto.
  }
Qed.
Hint Rewrite @rename_choice_seq_restriction_idem : slow.

Lemma rename_library_entry_idem {o} :
  forall r (e : @library_entry o),
    rename_library_entry r (rename_library_entry r e) = e.
Proof.
  introv; destruct e; simpl.

  {
    destruct entry; simpl; unfold rename_choice_seq_entry; autorewrite with slow; auto.
  }

  {
    remember (rename_correct r (rename_correct r correct)) as cor; clear Heqcor.
    revert cor.
    autorewrite with slow; introv.
    f_equal; eauto with pi.
  }
Qed.
Hint Rewrite @rename_library_entry_idem : slow.

Lemma rename_lib_idem {o} :
  forall r (lib : @library o),
    rename_lib r (rename_lib r lib) = lib.
Proof.
  induction lib; introv; simpl; auto; allrw; f_equal; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_lib_idem : slow.

Lemma eq_rename_opname_implies :
  forall r n m,
    rename_opname r n = rename_opname r m
    -> n = m.
Proof.
  introv h.
  unfold rename_opname in *.
  destruct r; boolvar; subst; tcsp.
Qed.
Hint Resolve eq_rename_opname_implies : slow.

Lemma eq_opabs_name_rename_implies :
  forall r a1 a2,
    opabs_name (rename_opabs r a1) = opabs_name (rename_opabs r a2)
    -> opabs_name a1 = opabs_name a2.
Proof.
  introv h; destruct a1, a2; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve eq_opabs_name_rename_implies : slow.

Lemma implies_not_matching_entries_rename {o} :
  forall r (e a : @library_entry o),
    ~ matching_entries e a
    -> ~ matching_entries (rename_library_entry r e) (rename_library_entry r a).
Proof.
  introv n m; destruct n.
  unfold matching_entries in *; simpl in *.
  destruct e, a; simpl in *; subst; auto.
  unfold same_opabs in *; simpl in *.
  unfold matching_entry_sign in *; simpl in *; autorewrite with slow in *.
  repnd; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve implies_not_matching_entries_rename : slow.

Lemma implies_entry_in_library_rename {o} :
  forall r e (lib : @library o),
    entry_in_library e lib
    -> entry_in_library (rename_library_entry r e) (rename_lib r lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  right.
  dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_entry_in_library_rename : slow.

Lemma implies_same_restrictions_rename {o} :
  forall r (r1 r2 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> same_restrictions (rename_choice_seq_restriction r r1) (rename_choice_seq_restriction r r2).
Proof.
  introv same.
  unfold same_restrictions in *.
  destruct r1, r2; simpl in *; repnd; dands; eauto 3 with slow.

  {
    introv; rewrite same0; auto.
  }

  {
    introv; rewrite same; auto.
  }
Qed.
Hint Resolve implies_same_restrictions_rename : slow.

Lemma rename_choice_seq_vals_app {o} :
  forall r (vals1 vals2 : @ChoiceSeqVals o),
    rename_choice_seq_vals r (vals1 ++ vals2)
    = rename_choice_seq_vals r vals1 ++ rename_choice_seq_vals r vals2.
Proof.
  induction vals1; simpl; introv; tcsp.
  rewrite IHvals1; auto.
Qed.

Lemma implies_entry_extends_rename {o} :
  forall r (e1 e2 : @library_entry o),
    entry_extends e1 e2
    -> entry_extends (rename_library_entry r e1) (rename_library_entry r e2).
Proof.
  introv ext.
  destruct e1, e2; simpl in *; repnd; subst; dands; tcsp; ginv.

  {
    unfold choice_sequence_entry_extend in *; repnd.
    unfold choice_sequence_vals_extend in *; exrepnd.
    destruct entry, entry0; simpl in *; subst.
    dands; eauto 3 with slow.
    rewrite rename_choice_seq_vals_app.
    eexists; dands; eauto.
  }

  {
    inversion ext; subst.
    f_equal.
    assert (correct = correct0) by eauto with pi; subst; auto.
  }
Qed.
Hint Resolve implies_entry_extends_rename : slow.

Lemma implies_entry_in_library_extends_rename {o} :
  forall r e (lib : @library o),
    entry_in_library_extends e lib
    -> entry_in_library_extends (rename_library_entry r e) (rename_lib r lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  {
    left; eauto 3 with slow.
  }

  {
    right.
    dands; tcsp; eauto 3 with slow.
  }
Qed.
Hint Resolve implies_entry_in_library_extends_rename : slow.

Lemma implies_lib_extends_entries_rename_lib {o} :
  forall r (lib1 lib2 : @library o),
    lib_extends_entries lib1 lib2
    -> lib_extends_entries (rename_lib r lib1) (rename_lib r lib2).
Proof.
  introv ext i.
  apply (implies_entry_in_library_rename r) in i; autorewrite with slow in *.
  apply ext in i.
  apply (implies_entry_in_library_extends_rename r) in i; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_lib_extends_entries_rename_lib : slow.

Lemma in_library_rename_iff {o} :
  forall r (e : @library_entry o) lib,
    List.In e lib <-> List.In (rename_library_entry r e) (rename_lib r lib).
Proof.
  induction lib; introv; split; intro h; simpl in *; tcsp; repndors; subst; tcsp.

  - rewrite <- IHlib; tcsp.

  - left.
    rewrite <- (rename_library_entry_idem r a).
    rewrite <- (rename_library_entry_idem r e).
    rewrite h; auto.

  - rewrite IHlib; tcsp.
Qed.

Lemma implies_subset_library_rename {o} :
  forall r (lib1 lib2 : @library o),
    subset_library lib2 lib1
    -> subset_library (rename_lib r lib2) (rename_lib r lib1).
Proof.
  introv ss i.
  apply (in_library_rename_iff r) in i.
  autorewrite with slow in *.
  apply ss in i; exrepnd.
  apply (in_library_rename_iff r) in i1.
  eexists; dands; eauto.
  apply (implies_entry_extends_rename r) in i0.
  autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_subset_library_rename : slow.

Lemma rename_choice_seq_val_eq_zero_implies {o} :
  forall r (t : @CTerm o),
    rename_choice_seq_val r t = mkc_zero
    -> t = mkc_zero.
Proof.
  introv h; destruct_cterms; simpl in *.
  inversion h as [z]; clear h.
  apply cterm_eq; simpl.
  destruct x as [v|op bs]; simpl in *; ginv;[].
  dopid op as [can|ncan|exc|abs] Case; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  destruct bs; simpl in *; ginv.
Qed.

Lemma rename_choice_seq_val_eq_tt_implies {o} :
  forall r (t : @CTerm o),
    rename_choice_seq_val r t = tt
    -> t = tt.
Proof.
  introv h; destruct_cterms; simpl in *.
  inversion h as [z]; clear h.
  apply cterm_eq; simpl.

  destruct x as [v|op bs]; simpl in *; ginv;[].
  dopid op as [can|ncan|exc|abs] Case; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
  destruct b; simpl in *.
  destruct l; simpl in *; ginv.

  destruct n as [v|op bs]; simpl in *; tcsp; ginv.
  dopid op as [can|ncan|exc|abs] SCase; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
Qed.

Lemma rename_choice_seq_val_eq_ff_implies {o} :
  forall r (t : @CTerm o),
    rename_choice_seq_val r t = ff
    -> t = ff.
Proof.
  introv h; destruct_cterms; simpl in *.
  inversion h as [z]; clear h.
  apply cterm_eq; simpl.

  destruct x as [v|op bs]; simpl in *; ginv;[].
  dopid op as [can|ncan|exc|abs] Case; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
  destruct b; simpl in *.
  destruct l; simpl in *; ginv.

  destruct n as [v|op bs]; simpl in *; tcsp; ginv.
  dopid op as [can|ncan|exc|abs] SCase; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
Qed.

Lemma rename_choice_seq_val_eq_boolean_implies {o} :
  forall r (t : @CTerm o) b,
    rename_choice_seq_val r t = mkc_boolean b
    -> t = mkc_boolean b.
Proof.
  introv h.
  destruct b; simpl in *.
  { eapply rename_choice_seq_val_eq_tt_implies; eauto. }
  { eapply rename_choice_seq_val_eq_ff_implies; eauto. }
Qed.

Lemma rename_choice_seq_val_eq_nat_implies {o} :
  forall r (t : @CTerm o) i,
    rename_choice_seq_val r t = mkc_nat i
    -> t = mkc_nat i.
Proof.
  introv h; destruct_cterms; simpl in *.
  inversion h as [z]; clear h.
  apply cterm_eq; simpl.
  destruct x as [v|op bs]; simpl in *; ginv;[].
  dopid op as [can|ncan|exc|abs] Case; simpl in *; ginv;[].
  destruct can; simpl in *; ginv.
  destruct bs; simpl in *; ginv.
Qed.

Lemma rename_restriction_pred_rename_choice_seq_val {o} :
  forall r typ n (v : @ChoiceSeqVal o),
    rename_restriction_pred r typ n (rename_choice_seq_val r v)
    <-> typ n v.
Proof.
  introv.
  unfold rename_restriction_pred.
  unfold rename_choice_seq_val; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @rename_restriction_pred_rename_choice_seq_val : slow.

Lemma is_nat_rename_choice_seq_val {o} :
  forall n r (v : @ChoiceSeqVal o),
    is_nat n (rename_choice_seq_val r v) <-> is_nat n v.
Proof.
  introv.
  unfold is_nat; split; introv q; exrepnd; exists i.
  { apply rename_choice_seq_val_eq_nat_implies in q0; auto. }
  { subst; simpl; apply cterm_eq; simpl; auto. }
Qed.
Hint Rewrite @is_nat_rename_choice_seq_val : slow.

Lemma is_bool_rename_choice_seq_val {o} :
  forall n r (v : @ChoiceSeqVal o),
    is_bool n (rename_choice_seq_val r v) <-> is_bool n v.
Proof.
  introv.
  unfold is_bool; split; introv q; exrepnd; exists b.
  { apply rename_choice_seq_val_eq_boolean_implies in q0; auto. }
  { subst; simpl; apply cterm_eq; simpl; auto; destruct b; simpl; auto. }
Qed.
Hint Rewrite @is_bool_rename_choice_seq_val : slow.

Lemma is_nat_restriction_rename_iff {o} :
  forall r (restr : @ChoiceSeqRestriction o),
    is_nat_restriction (rename_choice_seq_restriction r restr)
    <-> is_nat_restriction restr.
Proof.
  introv.
  destruct restr; simpl; tcsp.
  split; introv h; repnd; dands; tcsp.

  - introv.
    pose proof (h0 n) as q.
    apply rename_choice_seq_val_eq_zero_implies in q; auto.

  - introv.
    pose proof (h n (rename_choice_seq_val r v)) as q.
    autorewrite with slow in *; tcsp.

  - introv; rewrite h0; simpl; apply cterm_eq; simpl; auto.

  - introv.
    pose proof (h n (rename_choice_seq_val r v)) as q.
    rewrite <- (rename_restriction_pred_rename_choice_seq_val r) in q.
    autorewrite with slow in *; tcsp.
Qed.
Hint Rewrite @is_nat_restriction_rename_iff : slow.

Lemma is_bool_restriction_rename_iff {o} :
  forall r (restr : @ChoiceSeqRestriction o),
    is_bool_restriction (rename_choice_seq_restriction r restr)
    <-> is_bool_restriction restr.
Proof.
  introv.
  destruct restr; simpl; tcsp.
  split; introv h; repnd; dands; tcsp.

  - introv.
    pose proof (h0 n) as q.
    apply rename_choice_seq_val_eq_tt_implies in q; auto.

  - introv.
    pose proof (h n (rename_choice_seq_val r v)) as q.
    autorewrite with slow in *; tcsp.

  - introv; rewrite h0; simpl; apply cterm_eq; simpl; auto.

  - introv.
    pose proof (h n (rename_choice_seq_val r v)) as q.
    rewrite <- (rename_restriction_pred_rename_choice_seq_val r) in q.
    autorewrite with slow in *; tcsp.
Qed.
Hint Rewrite @is_bool_restriction_rename_iff : slow.

Lemma cterm_is_nth_rename_iff {o} :
  forall r (v : @ChoiceSeqVal o) n l,
    cterm_is_nth (rename_choice_seq_val r v) n l <-> cterm_is_nth v n l.
Proof.
  introv; unfold cterm_is_nth; split; intro h; exrepnd; exists i; dands; auto.

  - eapply rename_choice_seq_val_eq_nat_implies; eauto.

  - subst; simpl; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @cterm_is_nth_rename_iff : slow.

Lemma is_nat_seq_restriction_rename_iff {o} :
  forall r l (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l (rename_choice_seq_restriction r restr)
    <-> is_nat_seq_restriction l restr.
Proof.
  introv.
  destruct restr; simpl; tcsp.
  split; introv h; repnd; dands; tcsp.

  - introv len.
    pose proof (h0 n len) as q.
    autorewrite with slow in *; auto.

  - introv len.
    pose proof (h1 n len) as q.
    eapply rename_choice_seq_val_eq_zero_implies; eauto.

  - introv len.
    pose proof (h2 n (rename_choice_seq_val r v) len) as q.
    autorewrite with slow in *; tcsp.

  - introv len.
    pose proof (h n (rename_choice_seq_val r v) len) as q.
    autorewrite with slow in *; tcsp.

  - introv len.
    pose proof (h0 n len) as q.
    autorewrite with slow in *; auto.

  - introv len.
    pose proof (h1 n len) as q.
    rewrite q; simpl; apply cterm_eq; simpl; auto.

  - introv len.
    pose proof (h2 n (rename_choice_seq_val r v) len) as q.
    rewrite <- (rename_restriction_pred_rename_choice_seq_val r) in q.
    autorewrite with slow in *; tcsp.

  - introv len.
    pose proof (h n (rename_choice_seq_val r v) len) as q.
    rewrite <- (rename_restriction_pred_rename_choice_seq_val r) in q.
    autorewrite with slow in *; tcsp.
Qed.
Hint Rewrite @is_nat_seq_restriction_rename_iff : slow.

Lemma correct_restriction_rename_iff {o} :
  forall r name (restr : @ChoiceSeqRestriction o),
    correct_restriction name (rename_choice_seq_restriction r restr)
    <-> correct_restriction name restr.
Proof.
  introv.
  destruct name as [name kind]; unfold correct_restriction; simpl.
  destruct kind; simpl; tcsp; boolvar; subst; simpl; tcsp; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @correct_restriction_rename_iff : slow.

Lemma select_rename_choice_seq_vals {o} :
  forall r n vals (v : @ChoiceSeqVal o),
    select n (rename_choice_seq_vals r vals) = Some (rename_choice_seq_val r v)
    <-> select n vals = Some v.
Proof.
  induction n; simpl in *; introv; destruct vals; simpl in *; split; intro h; ginv; tcsp.

  - inversion h as [z]; clear h.
    rewrite <- (rename_choice_seq_val_idem r c).
    rewrite <- (rename_choice_seq_val_idem r v).
    rewrite z; auto.

  - rewrite IHn in h; auto.

  - rewrite IHn; auto.
Qed.

Lemma length_rename_choice_seq_vals {o} :
  forall r (vals : @ChoiceSeqVals o),
    length (rename_choice_seq_vals r vals) = length vals.
Proof.
  introv; unfold rename_choice_seq_vals; autorewrite with slow list; auto.
Qed.
Hint Rewrite @length_rename_choice_seq_vals : slow.

Lemma choice_sequence_satisfies_restriction_rename_iff {o} :
  forall r (vals : @ChoiceSeqVals o) restr,
    choice_sequence_satisfies_restriction
      (rename_choice_seq_vals r vals)
      (rename_choice_seq_restriction r restr)
    <-> choice_sequence_satisfies_restriction vals restr.
Proof.
  introv.
  unfold choice_sequence_satisfies_restriction.
  destruct restr; simpl; split; introv h.

  - introv i.
    pose proof (h n (rename_choice_seq_val r v)) as h.
    autorewrite with slow in *.
    apply h; auto.
    apply select_rename_choice_seq_vals; auto.

  - introv i.
    pose proof (h n (rename_choice_seq_val r v)) as h.
    autorewrite with slow in *.
    apply h.
    rewrite <- (select_rename_choice_seq_vals r) in i; autorewrite with slow in *; auto.

  - introv len.
    pose proof (h i) as h; autorewrite with slow in *.
    rewrite select_rename_choice_seq_vals in h; tcsp.

  - introv len; autorewrite with slow in *.
    apply h in len.
    apply select_rename_choice_seq_vals; auto.
Qed.

Lemma safe_library_entry_rename_iff {o} :
  forall r (e : @library_entry o),
    safe_library_entry (rename_library_entry r e) <-> safe_library_entry e.
Proof.
  introv.
  destruct e; simpl; tcsp.
  destruct entry as [entry restr]; simpl.
  rewrite choice_sequence_satisfies_restriction_rename_iff.
  rewrite correct_restriction_rename_iff; tcsp.
Qed.

Lemma safe_library_rename_iff {o} :
  forall r (lib : @library o),
    safe_library (rename_lib r lib) <-> safe_library lib.
Proof.
  introv; split; introv h i.

  - apply (implies_entry_in_library_rename r) in i.
    apply h in i.
    apply safe_library_entry_rename_iff in i; auto.

  - apply (implies_entry_in_library_rename r) in i.
    autorewrite with slow in *.
    apply h in i.
    apply safe_library_entry_rename_iff in i; auto.
Qed.
Hint Rewrite @safe_library_rename_iff : slow.

Lemma implies_lib_extends_rename_lib {o} :
  forall r (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> lib_extends (rename_lib r lib1) (rename_lib r lib2).
Proof.
  introv ext.
  destruct ext as [ext safe ss].
  split; dands; eauto 3 with slow;[].
  allrw @safe_library_rename_iff; tcsp.
Qed.
Hint Resolve implies_lib_extends_rename_lib : slow.

Definition rename_var_cterm {o} r (p : NVar * @CTerm o) : NVar * CTerm :=
  let (v,t) := p in (v,rename_cterm r t).

Definition rename_csub {o} r (s : @CSub o) : @CSub o :=
  map (rename_var_cterm r) s.

Lemma rename_csub_snoc {o} :
  forall r (s : @CSub o) v t,
    rename_csub r (snoc s (v,t))
    = snoc (rename_csub r s) (v, rename_cterm r t).
Proof.
  induction s; introv; simpl; tcsp.
  f_equal; tcsp.
Qed.

Ltac sim_snoc3 :=
  match goal with
  | [ |- similarity _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ ?h) ] =>
    let w := fresh "w" in
    let c := fresh "c" in
    assert (wf_term (htyp h)) as w;
    [ auto
    | assert (cover_vars (htyp h) s1) as c;
      [ auto
      | apply similarity_snoc; simpl;
        exists s1 s2 t1 t2 w c
      ]
    ]
  end.

Lemma dom_csub_rename_csub {o} :
  forall r (s : @CSub o),
    dom_csub (rename_csub r s) = dom_csub s.
Proof.
  unfold dom_csub, rename_csub; introv.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; auto.
Qed.
Hint Rewrite @dom_csub_rename_csub : slow.

Lemma implies_covered_rename {o} :
  forall r (t : @NTerm o) vars,
    covered t vars
    -> covered (rename_term r t) vars.
Proof.
  introv cov.
  unfold covered in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_covered_rename : slow.

Lemma implies_cover_vars_rename {o} :
  forall r (t : @NTerm o) s,
    cover_vars t s
    -> cover_vars (rename_term r t) (rename_csub r s).
Proof.
  introv cov.
  allrw @cover_vars_covered; autorewrite with slow.
  eauto 3 with slow.
Qed.
Hint Resolve implies_cover_vars_rename : slow.

Lemma implies_isnoncan_like_rename_term {o} :
  forall r (t : @NTerm o),
    isnoncan_like t
    -> isnoncan_like (rename_term r t).
Proof.
  introv isn.
  unfold isnoncan_like in *; repndors;[left|right].

  - unfold isnoncan in *.
    destruct t as [|op bs]; simpl in *; auto.
    destruct op; simpl; auto.

  - unfold isabs in *.
    destruct t as [|op bs]; simpl in *; auto.
    destruct op; simpl; auto.
Qed.
Hint Resolve implies_isnoncan_like_rename_term : slow.

Lemma implies_iscan_rename_term {o} :
  forall r (t : @NTerm o),
    iscan t
    -> iscan (rename_term r t).
Proof.
  introv isc.
  unfold iscan in *.
  destruct t as [|op bs]; simpl in *; auto.
  destruct op; simpl; auto.
Qed.
Hint Resolve implies_iscan_rename_term : slow.

Lemma implies_isexc_rename_term {o} :
  forall r (t : @NTerm o),
    isexc t
    -> isexc (rename_term r t).
Proof.
  introv ise.
  unfold isexc in *.
  destruct t as [|op bs]; simpl in *; auto.
  destruct op; simpl; auto.
Qed.
Hint Resolve implies_isexc_rename_term : slow.

Lemma implies_isvalue_like_rename_term {o} :
  forall r (t : @NTerm o),
    isvalue_like t
    -> isvalue_like (rename_term r t).
Proof.
  introv isv.
  unfold isvalue_like in *; repndors;[left|right]; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_like_rename_term : slow.

Definition rename_var_term {o} r (p : NVar * @NTerm o) : NVar * NTerm :=
  let (v,t) := p in (v,rename_term r t).

Definition rename_sub {o} r (s : @Sub o) : @Sub o :=
  map (rename_var_term r) s.

Lemma sub_find_rename_sub {o} :
  forall r (s : @Sub o) v,
    sub_find (rename_sub r s) v
    = match sub_find s v with
      | Some t => Some (rename_term r t)
      | None => None
      end.
Proof.
  induction s; introv; simpl; tcsp; repnd; simpl; boolvar; auto.
Defined.

Lemma rename_sub_sub_filter {o} :
  forall r (s : @Sub o) l,
    rename_sub r (sub_filter s l)
    = sub_filter (rename_sub r s) l.
Proof.
  induction s; introv; simpl; tcsp.
  repnd; simpl; boolvar; tcsp.
  simpl; rewrite IHs; auto.
Defined.

Lemma rename_term_lsubst_aux {o} :
  forall r (t : @NTerm o) s,
    rename_term r (lsubst_aux t s) = lsubst_aux (rename_term r t) (rename_sub r s).
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp.

  - Case "vterm".

    rewrite sub_find_rename_sub.
    remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    f_equal.
    induction bs; simpl; auto.
    rewrite IHbs; simpl in *; tcsp;[|introv xx; eapply ind; eauto].
    destruct a; simpl.
    erewrite ind; eauto.
    rewrite rename_sub_sub_filter; auto.
Defined.

Lemma bound_vars_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    bound_vars (rename_term r t) = bound_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @bound_vars_rename_term : slow.

Lemma all_vars_rename_term {o} :
  forall r (t : @NTerm o),
    all_vars (rename_term r t) = all_vars t.
Proof.
  introv; unfold all_vars; autorewrite with slow; auto.
Qed.
Hint Rewrite @all_vars_rename_term : slow.

Lemma rename_sub_var_ren {o} :
  forall r l1 l2, @rename_sub o r (var_ren l1 l2) = var_ren l1 l2.
Proof.
  unfold var_ren.
  induction l1; introv; simpl; auto.
  destruct l2; simpl; auto.
  rewrite IHl1; auto.
Qed.
Hint Rewrite @rename_sub_var_ren : slow.

Lemma rename_term_change_bvars_alpha {o} :
  forall r vs (t : @NTerm o),
    rename_term r (change_bvars_alpha vs t)
    = change_bvars_alpha vs (rename_term r t).
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl in *; tcsp.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  erewrite <- ind; eauto 3 with slow;[].
  autorewrite with slow; f_equal.
  rewrite rename_term_lsubst_aux; autorewrite with slow; auto.
Defined.

Lemma flat_map_free_vars_range_rename_sub {o} :
  forall r (s : @Sub o),
    flat_map free_vars (range (rename_sub r s))
    = flat_map free_vars (range s).
Proof.
  induction s; simpl; auto.
  rewrite IHs; repnd; simpl; clear IHs.
  autorewrite with slow; auto.
Defined.
Hint Rewrite @flat_map_free_vars_range_rename_sub : slow.

Lemma rename_term_lsubst {o} :
  forall r (t : @NTerm o) s,
    rename_term r (lsubst t s) = lsubst (rename_term r t) (rename_sub r s).
Proof.
  introv.
  unfold lsubst.
  autorewrite with slow.
  boolvar; auto; rewrite rename_term_lsubst_aux; auto.
  rewrite rename_term_change_bvars_alpha; auto.
Defined.

Lemma rename_term_subst {o} :
  forall r (t : @NTerm o) v u,
    rename_term r (subst t v u) = subst (rename_term r t) v (rename_term r u).
Proof.
  introv; unfold subst.
  rewrite rename_term_lsubst; auto.
Defined.

Lemma eapply_wf_def_rename_term {o} :
  forall r (t : @NTerm o),
    eapply_wf_def t
    -> eapply_wf_def (rename_term r t).
Proof.
  introv wf.
  unfold eapply_wf_def in *; repndors; exrepnd; subst; simpl in *; tcsp.
  - unfold mk_choice_seq; left; eexists; eauto.
  - unfold mk_lam; right; eexists; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_rename_term : slow.

Lemma maybe_new_var_rename_term {o} :
  forall v l r (t : @NTerm o),
    maybe_new_var v l (rename_term r t)
    = maybe_new_var v l t.
Proof.
  introv; unfold maybe_new_var, newvar; autorewrite with slow; auto.
Qed.
Hint Rewrite @maybe_new_var_rename_term : slow.

Lemma pushdown_fresh_rename_term {o} :
  forall v r (t : @NTerm o),
    pushdown_fresh v (rename_term r t)
    = rename_term r (pushdown_fresh v t).
Proof.
  introv; unfold pushdown_fresh.
  destruct t as [z|op bs]; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; autorewrite with slow; auto.
Qed.

Lemma get_fresh_atom_rename_term {o} :
  forall r lib (t : @NTerm o),
    get_fresh_atom lib (rename_term r t) = get_fresh_atom lib t.
Proof.
  introv; unfold get_fresh_atom, get_utokens_lib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_fresh_atom_rename_term : slow.

Definition rename_name_term {o} r (p : get_patom_set o * @NTerm o) : get_patom_set o * NTerm :=
  let (v,t) := p in (v,rename_term r t).

Definition rename_utok_sub {o} r (s : @utok_sub o) : @utok_sub o :=
  map (rename_name_term r) s.

Lemma rename_term_oterm {o} :
  forall r op (bs : list (@BTerm o)),
    rename_term r (oterm op bs)
    = oterm (rename_op r op) (map (rename_bterm r) bs).
Proof.
  tcsp.
Qed.

Lemma get_utok_rename_op {o} :
  forall r (op : @Opid o),
    get_utok (rename_op r op) = get_utok op.
Proof.
  introv; destruct op; simpl; tcsp.
Qed.
Hint Rewrite @get_utok_rename_op : slow.

Lemma utok_sub_find_rename_utok_sub {o} :
  forall r (s : @utok_sub o) a,
    utok_sub_find (rename_utok_sub r s) a
    = match utok_sub_find s a with
      | Some t => Some (rename_term r t)
      | None => None
      end.
Proof.
  induction s; introv; simpl; tcsp.
  repnd; simpl; boolvar; subst; tcsp.
Qed.

Lemma rename_term_subst_utok {o} :
  forall r (a : get_patom_set o) bs s,
    rename_term r (subst_utok a bs s)
    = subst_utok a (map (rename_bterm r) bs) (rename_utok_sub r s).
Proof.
  introv.
  unfold subst_utok; autorewrite with slow.
  rewrite utok_sub_find_rename_utok_sub.
  remember (utok_sub_find s a) as f; symmetry in Heqf; destruct f; auto.
Qed.

Lemma rename_term_subst_utokens_aux {o} :
  forall r (t : @NTerm o) (s : utok_sub),
    rename_term r (subst_utokens_aux t s)
    = subst_utokens_aux (rename_term r t) (rename_utok_sub r s).
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; tcsp;[].
  rewrite rename_term_oterm.
  repeat (rewrite subst_utokens_aux_oterm).
  autorewrite with slow in *.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; simpl in *; tcsp.

  - rewrite rename_term_subst_utok; allrw map_map; unfold compose.
    f_equal.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    eapply ind; eauto.

  - f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    eapply ind; eauto.
Qed.

Lemma free_vars_utok_sub_rename_utok_sub {o} :
  forall r (s : @utok_sub o),
    free_vars_utok_sub (rename_utok_sub r s)
    = free_vars_utok_sub s.
Proof.
  induction s; introv; simpl; tcsp.
  repnd; simpl; autorewrite with slow; allrw; auto.
Qed.
Hint Rewrite @free_vars_utok_sub_rename_utok_sub : slow.

Lemma rename_term_subst_utokens {o} :
  forall r (t : @NTerm o) (s : utok_sub),
    rename_term r (subst_utokens t s)
    = subst_utokens (rename_term r t) (rename_utok_sub r s).
Proof.
  introv; unfold subst_utokens; autorewrite with slow in *.
  boolvar.

  - apply rename_term_subst_utokens_aux.

  - rewrite rename_term_subst_utokens_aux; autorewrite with slow.
    rewrite rename_term_change_bvars_alpha; auto.
Qed.

Definition rename_sosub_kind {o} r (s : @sosub_kind o) : sosub_kind :=
  match s with
  | sosk l t => sosk l (rename_term r t)
  end.

Definition rename_var_sk {o} r (p : NVar * @sosub_kind o) : NVar * sosub_kind :=
  let (v,t) := p in (v,rename_sosub_kind r t).

Definition rename_sosub {o} r (s : @SOSub o) : @SOSub o :=
  map (rename_var_sk r) s.

Lemma sosub_find_rename_sosub {o} :
  forall r (s : @SOSub o) v,
    sosub_find (rename_sosub r s) v
    = match sosub_find s v with
      | Some t => Some (rename_sosub_kind r t)
      | None => None
      end.
Proof.
  induction s; introv; simpl; tcsp; repnd; simpl; boolvar; auto;
    destruct a; simpl; boolvar; auto.
Qed.

Lemma rename_sub_combine {o} :
  forall r l (ts : list (@NTerm o)),
    length l = length ts
    -> rename_sub r (combine l ts)
       = combine l (map (rename_term r) ts).
Proof.
  induction l; introv len; simpl in *; tcsp.
  destruct ts; simpl in *; ginv.
  rewrite IHl; auto.
Qed.

Lemma rename_sosub_ossub_filter {o} :
  forall r (s : @SOSub o) l,
    rename_sosub r (sosub_filter s l)
    = sosub_filter (rename_sosub r s) l.
Proof.
  induction s; introv; simpl; tcsp.
  repnd; simpl; boolvar; tcsp.
  destruct a; simpl; boolvar; tcsp.
  simpl; rewrite IHs; auto.
Qed.

Lemma rename_term_sosub_aux {o} :
  forall r (t : @SOTerm o) s,
    rename_term r (sosub_aux s t)
    = sosub_aux (rename_sosub r s) (rename_soterm r t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case ; introv; simpl in *; tcsp.

  - Case "sovar".

    rewrite sosub_find_rename_sosub.
    autorewrite with list.
    remember (sosub_find s (v,length ts)) as sf; symmetry in Heqsf; destruct sf; simpl; auto.

    + destruct s0; simpl.
      rewrite rename_term_lsubst_aux; simpl.
      apply sosub_find_some in Heqsf; repnd.
      rewrite rename_sub_combine; autorewrite with list; auto.
      allrw map_map; unfold compose.
      f_equal; f_equal.
      apply eq_maps; introv i; tcsp.

    + rewrite rename_term_apply_list; simpl; f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i; tcsp.

  - Case "soterm".
    f_equal; allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    erewrite ind;eauto.
    rewrite rename_sosub_ossub_filter; auto.
Qed.

Lemma fo_bound_vars_rename_soterm {o} :
  forall r (t : @SOTerm o),
    fo_bound_vars (rename_soterm r t)
    = fo_bound_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.

  - Case "soterm".
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.
    introv i; destruct x; simpl; f_equal.
    eapply ind; eauto.
Qed.
Hint Rewrite @fo_bound_vars_rename_soterm : slow.

Lemma free_vars_sosub_rename_sosub {o} :
  forall r (s : @SOSub o),
    free_vars_sosub (rename_sosub r s)
    = free_vars_sosub s.
Proof.
  unfold free_vars_sosub, rename_sosub; introv.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; repnd; simpl.
  destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_sosub_rename_sosub : slow.

Lemma all_fo_vars_rename_soterm {o} :
  forall r (t : @SOTerm o),
    all_fo_vars (rename_soterm r t)
    = all_fo_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp;
    allrw flat_map_map; unfold compose.

  - f_equal; apply eq_flat_maps; auto.

  - apply eq_flat_maps; introv i; destruct x; simpl; f_equal.
    eapply ind; eauto.
Qed.
Hint Rewrite @all_fo_vars_rename_soterm : slow.

Lemma bound_vars_sosub_rename_sosub {o} :
  forall r (s : @SOSub o),
    bound_vars_sosub (rename_sosub r s)
    = bound_vars_sosub s.
Proof.
  introv.
  unfold bound_vars_sosub, rename_sosub.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; repnd; simpl.
  destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @bound_vars_sosub_rename_sosub : slow.

Lemma rename_soterm_so_change_bvars_alpha {o} :
  forall r (t : @SOTerm o) vs k,
    rename_soterm r (so_change_bvars_alpha vs k t)
    = so_change_bvars_alpha vs k (rename_soterm r t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl in *; tcsp.

  - Case "sovar".
    autorewrite with list; f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; tcsp.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    erewrite <- ind; eauto 3 with slow;[].
    autorewrite with slow; f_equal.
Qed.

Lemma rename_soterm_fo_change_bvars_alpha {o} :
  forall r (t : @SOTerm o) vs k,
    rename_soterm r (fo_change_bvars_alpha vs k t)
    = fo_change_bvars_alpha vs k (rename_soterm r t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl in *; tcsp.

  - Case "sovar".
    autorewrite with list; f_equal.
    boolvar; subst; simpl in *; ginv; tcsp;
      try (complete (destruct ts; simpl in *; tcsp)).
    f_equal; allrw map_map; unfold compose.
    apply eq_maps; tcsp.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    erewrite <- ind; eauto 3 with slow;[].
    autorewrite with slow; f_equal.
Qed.

Lemma all_fo_vars_fo_change_bvars_alpha_rename_soterm {o} :
  forall r (t : @SOTerm o) l k,
    all_fo_vars (fo_change_bvars_alpha l k (rename_soterm r t))
    = all_fo_vars (fo_change_bvars_alpha l k t).
Proof.
  introv; rewrite <- rename_soterm_fo_change_bvars_alpha; autorewrite with slow; auto.
Qed.
Hint Rewrite @all_fo_vars_fo_change_bvars_alpha_rename_soterm : slow.

Lemma allvars_rename_term {o} :
  forall r (t : @NTerm o),
    allvars (rename_term r t) = allvars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; f_equal; eapply ind; eauto.
Qed.
Hint Rewrite @allvars_rename_term : slow.

Lemma allvars_range_sosub_rename_sosub {o} :
  forall r (s : @SOSub o),
    allvars_range_sosub (rename_sosub r s)
    = allvars_range_sosub s.
Proof.
  introv; unfold allvars_range_sosub, rename_sosub.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; repnd; simpl.
  destruct x; simpl; f_equal; autorewrite with slow; auto.
Qed.
Hint Rewrite @allvars_range_sosub_rename_sosub : slow.

Lemma all_vars_change_bvars_alpha_rename_term {o} :
  forall l r (t : @NTerm o),
    all_vars (change_bvars_alpha l (rename_term r t))
    = all_vars (change_bvars_alpha l t).
Proof.
  introv.
  rewrite <- rename_term_change_bvars_alpha.
  introv; unfold all_vars; autorewrite with slow; auto.
Qed.
Hint Rewrite @all_vars_change_bvars_alpha_rename_term : slow.

Lemma rename_sosub_sosub_change_bvars_alpha {o} :
  forall r l (s : @SOSub o),
    rename_sosub r (sosub_change_bvars_alpha l s)
    = sosub_change_bvars_alpha l (rename_sosub r s).
Proof.
  introv; unfold sosub_change_bvars_alpha, rename_sosub.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; repnd; simpl.
  destruct x; simpl.
  unfold sk_change_bvars_alpha; simpl; autorewrite with slow.
  f_equal; f_equal.
  rewrite rename_term_lsubst_aux; simpl.
  rewrite <- rename_term_change_bvars_alpha; autorewrite with slow; auto.
Qed.

Lemma rename_term_sosub {o} :
  forall r s (t : @SOTerm o),
    rename_term r (sosub s t)
    = sosub (rename_sosub r s) (rename_soterm r t).
Proof.
  introv; unfold sosub; autorewrite with slow.
  boolvar; tcsp.

  - rewrite rename_term_sosub_aux; auto.

  - rewrite rename_term_sosub_aux; auto.
    rewrite rename_sosub_sosub_change_bvars_alpha; auto.

  - rewrite rename_term_sosub_aux; auto.
    rewrite rename_soterm_fo_change_bvars_alpha; auto.

  - rewrite rename_term_sosub_aux; simpl.
    rewrite rename_soterm_fo_change_bvars_alpha; auto.
    rewrite rename_sosub_sosub_change_bvars_alpha; auto.
Qed.

Lemma rename_sosub_mk_abs_subst {o} :
  forall r vars (bs : list (@BTerm o)),
    rename_sosub r (mk_abs_subst vars bs)
    = mk_abs_subst vars (map (rename_bterm r) bs).
Proof.
  induction vars; introv; simpl; auto.
  destruct a; simpl.
  destruct bs; simpl; auto.
  destruct b; simpl.
  boolvar; simpl; auto.
  rewrite IHvars; auto.
Qed.

Lemma implies_matching_entry_rename {o} :
  forall r abs1 abs2 vars (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> matching_entry (rename_opabs r abs1) (rename_opabs r abs2) vars (map (rename_bterm r) bs).
Proof.
  unfold  matching_entry in *; introv h; repnd.
  destruct abs1, abs2; simpl in *; subst; dands; auto.
  unfold matching_bterms in *.
  allrw map_map; unfold compose.
  rewrite h.
  apply eq_maps; introv i.
  destruct x; simpl; unfold num_bvars; simpl; auto.
Qed.
Hint Resolve implies_matching_entry_rename : slow.

Lemma implies_found_entry_rename {o} :
  forall r lib abs bs oa vars (rhs : @SOTerm o) correct,
    found_entry lib abs bs oa vars rhs correct
    -> found_entry
         (rename_lib r lib)
         (rename_opabs r abs)
         (map (rename_bterm r) bs)
         (rename_opabs r oa)
         vars
         (rename_soterm r rhs)
         (rename_correct r correct).
Proof.
  introv fe; unfold found_entry in *.
  revert abs bs oa vars rhs correct fe.
  induction lib; introv fe; simpl in *; ginv.
  destruct a; simpl in *; try (complete (apply IHlib in fe; auto));[].

  boolvar; ginv; tcsp.

  - inversion fe; subst; GC.
    assert (correct0 = correct) as xx by (eauto 3 with pi).
    subst; GC; auto.

  - apply (implies_matching_entry_rename r) in m.
    autorewrite with slow in *.
    apply not_matching_entry_iff in n; destruct n.
    allrw map_map; unfold compose in *.
    assert (map (fun x => rename_bterm r (rename_bterm r x)) bs = bs) as xx; try congruence.
    apply eq_map_l; introv i; destruct x; simpl; autorewrite with slow; auto.

  - apply (implies_matching_entry_rename r) in m.
    apply not_matching_entry_iff in n; destruct n; auto.
Qed.

Lemma find_cs_rename_eq {o} :
  forall r (lib : @library o) name,
    find_cs (rename_lib r lib) name
    = match find_cs lib name with
      | Some v => Some (rename_choice_seq_entry r v)
      | None => None
      end.
Proof.
  induction lib; introv; simpl; tcsp.
  destruct a; simpl; boolvar; subst; tcsp.
Qed.

Lemma select_rename_choice_seq_vals_eq {o} :
  forall r n (vals : @ChoiceSeqVals o),
    select n (rename_choice_seq_vals r vals)
    = match select n vals with
      | Some v => Some (rename_choice_seq_val r v)
      | None => None
      end.
Proof.
  induction n; introv; simpl; destruct vals; simpl; tcsp.
Qed.

Lemma find_cs_value_at_rename_eq {o} :
  forall r (lib : @library o) name n,
    find_cs_value_at (rename_lib r lib) name n
    = match find_cs_value_at lib name n with
      | Some v => Some (rename_choice_seq_val r v)
      | None => None
      end.
Proof.
  introv.
  unfold find_cs_value_at.
  rewrite find_cs_rename_eq.
  remember (find_cs lib name) as f; symmetry in Heqf; destruct f; auto.
  repeat (rewrite find_value_of_cs_at_is_select).
  destruct c; simpl.
  rewrite select_rename_choice_seq_vals_eq; auto.
Qed.

Lemma rename_term_CSVal2term {o} :
  forall r (v : @ChoiceSeqVal o),
    rename_term r (CSVal2term v)
    = CSVal2term (rename_choice_seq_val r v).
Proof.
  introv; destruct v; simpl; auto.
Qed.

Lemma get_utokens_library_rename {o} :
  forall r (lib : @library o),
    get_utokens_library (rename_lib r lib) = get_utokens_library lib.
Proof.
  induction lib; introv; simpl; auto.
  rewrite IHlib; f_equal.
  destruct a; simpl; autorewrite with slow; auto.
  destruct entry as [vals restr]; simpl.
  unfold rename_choice_seq_vals.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  unfold rename_choice_seq_val.
  destruct_cterms; unfold getc_utokens; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_library_rename : slow.

Lemma get_fresh_atom_rename_lib {o} :
  forall r (lib : @library o) t,
    get_fresh_atom (rename_lib r lib) t = get_fresh_atom lib t.
Proof.
  introv; unfold get_fresh_atom, get_utokens_lib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_fresh_atom_rename_lib : slow.

Lemma compute_step_rename {o} :
  forall r lib (a b : @NTerm o),
    compute_step lib a = csuccess b
    -> compute_step (rename_lib r lib) (rename_term r a) = csuccess (rename_term r b).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv comp; simpl in *.

  - Case "vterm".

    csunf comp; simpl in *; ginv.

  - Case "oterm".

    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".

      csunf comp; simpl in *; ginv.
      csunf; simpl; auto.

    + SCase "NCan".

      destruct bs as [|w]; try (complete (allsimpl; ginv)).
      destruct w as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv));[|].

      {
        destruct t as [x|op bts]; try (complete (allsimpl; ginv)); [].

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; simpl in comp.
              apply compute_step_apply_success in comp; repndors; exrepnd; subst; tcsp.
              csunf; simpl; unfold apply_bterm; simpl.
              rewrite rename_term_subst; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; simpl in comp.

              apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl; tcsp.
              repndors; repnd; subst; tcsp.

              - apply compute_step_eapply2_success in comp1; repnd.
                subst; simpl in *.
                repndors; exrepnd; subst; ginv; tcsp;[|].

                + unfold mk_lam in *; ginv; simpl.
                  fold_terms; unfold mk_eapply.
                  rewrite compute_step_eapply_lam_iscan; eauto 3 with slow;[].
                  unfold apply_bterm; simpl.
                  rewrite rename_term_lsubst; auto.

                + unfold mk_choice_seq in *; ginv; simpl.
                  fold_terms; unfold mk_eapply.
                  csunf; simpl.
                  unfold compute_step_eapply; simpl; boolvar; try omega.
                  allrw @Znat.Nat2Z.id; auto.
                  rewrite find_cs_value_at_rename_eq.
                  allrw; auto.
                  rewrite rename_term_CSVal2term; auto.

              - fold_terms; unfold mk_eapply.
                rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow.
                apply (eapply_wf_def_rename_term r) in comp2; simpl in comp2; auto.

              - exrepnd; subst; simpl in *.
                fold_terms.
                apply (eapply_wf_def_rename_term r) in comp2; simpl in comp2; auto.
                rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 3 with slow;[].
                apply q in comp1; clear q.
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; simpl in comp.
              apply compute_step_fix_success in comp; repnd; subst; simpl; tcsp.
            }

            {
              SSSCase "NSpread".

              csunf comp; simpl in comp.
              apply compute_step_spread_success in comp; exrepnd; subst; simpl; tcsp.
              csunf; simpl; unfold apply_bterm.
              rewrite rename_term_lsubst; simpl; tcsp.
            }

            {
              SSSCase "NDsup".

              csunf comp; simpl in comp.
              apply compute_step_dsup_success in comp; exrepnd; subst; simpl; tcsp.
              csunf; simpl; unfold apply_bterm.
              rewrite rename_term_lsubst; simpl; tcsp.
            }

            {
              SSSCase "NDecide".

              csunf comp; simpl in comp.
              apply compute_step_decide_success in comp; exrepnd; subst; simpl; tcsp.
              csunf; simpl; unfold apply_bterm.
              repndors; exrepnd; subst; simpl; rewrite rename_term_subst; simpl; tcsp.
            }

            {
              SSSCase "NCbv".

              csunf comp; simpl in comp.
              apply compute_step_cbv_success in comp; exrepnd; subst; simpl; tcsp.
              csunf; simpl; unfold apply_bterm.
              repndors; exrepnd; subst; simpl; rewrite rename_term_subst; simpl; tcsp.
            }

            {
              SSSCase "NSleep".

              csunf comp; simpl in comp.
              apply compute_step_sleep_success in comp; exrepnd; subst; simpl; tcsp.
            }

            {
              SSSCase "NTUni".

              csunf comp; simpl in comp.
              apply compute_step_tuni_success in comp; exrepnd; subst; simpl; tcsp.
              csunf; simpl; tcsp.
              unfold compute_step_tuni; simpl; boolvar; try omega.
              allrw @Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; simpl in comp.
              apply compute_step_minus_success in comp; exrepnd; subst; simpl; tcsp.
            }

            {
              SSSCase "NFresh".

              csunf comp; simpl in comp; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; simpl in comp.
              apply compute_step_try_success in comp; exrepnd; subst; simpl; tcsp.
            }

            {
              SSSCase "NParallel".

              csunf comp; simpl in comp; ginv.
              apply compute_step_parallel_success in comp; exrepnd; subst; simpl; tcsp.
            }

            {
              SSSCase "NCompSeq1".
              csunf comp; simpl in comp; ginv.
              apply compute_step_comp_seq1_success in comp; exrepnd; subst; simpl in *.
              repndors; exrepnd; subst; csunf; simpl; boolvar; tcsp; try omega;
                autorewrite with slow nat in *; subst; simpl in *; tcsp; try omega.
            }

            {
              SSSCase "NCompSeq2".
              csunf comp; simpl in comp; ginv.
              apply compute_step_comp_seq2_success in comp; exrepnd; subst; simpl in *.
              repndors; exrepnd; subst; csunf; simpl; boolvar; tcsp; try omega;
                autorewrite with slow nat in *; subst; simpl in *; tcsp; try omega.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; subst; simpl; tcsp.

              - apply compute_step_compop_success_can_can in comp1; exrepnd; subst; GC; ginv.
                repndors; exrepnd; subst;
                  csunf; simpl; dcwf h;
                    unfold compute_step_comp; simpl; allrw; boolvar; auto.

              - rewrite compute_step_ncompop_ncanlike2; eauto 3 with slow;[].
                simpl in *; dcwf h;[].
                pose proof (ind t t []) as q; clear ind; repeat (autodimp q hyp); eauto 3 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; simpl in *.
                csunf; simpl; dcwf h; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; subst; simpl; tcsp.

              - apply compute_step_arithop_success_can_can in comp1; exrepnd; subst; GC; ginv.
                repndors; exrepnd; subst;
                  csunf; simpl; dcwf h;
                    unfold compute_step_arith; simpl; allrw; boolvar; auto.

              - rewrite compute_step_narithop_ncanlike2; eauto 3 with slow;[].
                simpl in *; dcwf h;[].
                pose proof (ind t t []) as q; clear ind; repeat (autodimp q hyp); eauto 3 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; simpl in *.
                csunf; simpl; dcwf h; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; simpl in *.
              apply compute_step_can_test_success in comp; exrepnd; subst; simpl in *.
              csunf; simpl.
              destruct (canonical_form_test_for c can2); auto.
            }

          + SSCase "NCan".

            csunf comp; simpl in *.
            remember (compute_step lib (oterm (NCan ncan2) bts)) as comp'; symmetry in Heqcomp'.
            destruct comp'; simpl in *; ginv;[].
            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 3 with slow.
            apply q in Heqcomp'; clear q.
            csunf; simpl in *.
            rewrite Heqcomp'; simpl; auto.

          + SSCase "Exc".

            csunf comp; simpl in *.
            apply compute_step_catch_success in comp; repndors; exrepnd; subst; simpl in *; tcsp.

            * csunf; simpl.
              rewrite rename_term_subst; auto.

            * csunf; simpl.
              rewrite compute_step_catch_if_diff; auto.

          + SSCase "Abs".

            csunf comp; simpl in *.
            remember (compute_step lib (oterm (Abs abs2) bts)) as comp'; symmetry in Heqcomp'.
            destruct comp'; simpl in *; ginv;[].
            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 3 with slow.
            apply q in Heqcomp'; clear q.
            csunf; simpl in *.
            rewrite Heqcomp'; simpl; auto.
      }

      {
        (* fresh *)

        csunf comp; simpl in comp.
        apply compute_step_fresh_success in comp; exrepnd; subst; simpl in *.
        repndors; exrepnd; subst; tcsp.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; eauto 3 with slow.
          rewrite pushdown_fresh_rename_term; auto.

        - pose proof (ind t (subst t n (mk_utoken (get_fresh_atom lib t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto with slow;
            try (complete (rewrite simple_osize_subst; simpl; auto; eauto 3 with slow)).
          apply q in comp2; clear q.
          rewrite computation3.compute_step_fresh_if_isnoncan_like; eauto 3 with slow.
          rewrite rename_term_subst in comp2; simpl in *; autorewrite with slow in *.
          fold_terms.
          rewrite comp2; simpl; auto.
          rewrite rename_term_subst_utokens; auto.
      }

    + SCase "Exc".

      csunf comp; simpl in comp; ginv.
      csunf; simpl; auto.

    + SCase "Abs".

      csunf comp; simpl in comp.
      apply compute_step_lib_success in comp; exrepnd; subst.
      csunf; simpl.

      apply (implies_found_entry_rename r) in comp0.
      apply found_entry_implies_compute_step_lib_success in comp0.
      rewrite comp0; clear comp0.
      unfold mk_instance; simpl.

      rewrite rename_term_sosub.
      rewrite rename_sosub_mk_abs_subst; auto.
Qed.

Lemma reduces_to_rename {o} :
  forall r lib (a b : @NTerm o),
    reduces_to lib a b
    -> reduces_to (rename_lib r lib) (rename_term r a) (rename_term r b).
Proof.
  introv h; unfold reduces_to in *; exrepnd; exists k.
  revert a b h0.
  induction k; introv h.

  - allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply (compute_step_rename r) in h1.
    apply IHk in h0.
    allrw.
    eexists; dands; eauto.
Qed.
Hint Resolve reduces_to_rename : slow.

Lemma nt_wf_rename_term {o} :
  forall r (t : @NTerm o),
    nt_wf t
    -> nt_wf (rename_term r t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv wf; simpl in *; auto.

  - Case "oterm".
    allrw @nt_wf_oterm_iff; repnd.
    allrw map_map; unfold compose; simpl in *.
    autorewrite with slow.
    rewrite <- wf0.
    dands.

    + apply eq_maps; introv i; destruct x; simpl; tcsp.

    + introv i.
      allrw in_map_iff; exrepnd; subst; simpl in *.
      destruct a; simpl in *.
      applydup wf in i1.
      apply ind in i1; auto.
      allrw @bt_wf_iff; auto.
Qed.
Hint Resolve nt_wf_rename_term : slow.

Lemma isprogram_rename_term {o} :
  forall r (t : @NTerm o),
    isprogram t
    -> isprogram (rename_term r t).
Proof.
  introv isp.
  unfold isprogram in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve isprogram_rename_term : slow.

Lemma isvalue_rename_term {o} :
  forall r (t : @NTerm o),
    isvalue t
    -> isvalue (rename_term r t).
Proof.
  introv isv.
  allrw @isvalue_iff; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve isvalue_rename_term : slow.

Lemma computes_to_value_rename {o} :
  forall r lib (a b : @NTerm o),
    computes_to_value lib a b
    -> computes_to_value (rename_lib r lib) (rename_term r a) (rename_term r b).
Proof.
  introv comp.
  unfold computes_to_value in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_rename : slow.

Lemma computes_to_valc_rename {o} :
  forall r lib (a b : @CTerm o),
    computes_to_valc lib a b
    -> computes_to_valc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; unfold computes_to_valc; simpl; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_rename : slow.

Lemma rename_cterm_mkc_uni {o} :
  forall r j, @rename_cterm o r (mkc_uni j) = mkc_uni j.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_uni : slow.

Lemma rename_cterm_mkc_integer {o} :
  forall r j, @rename_cterm o r (mkc_integer j) = mkc_integer j.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_integer : slow.

Lemma rename_cterm_mkc_token {o} :
  forall r j, @rename_cterm o r (mkc_token j) = mkc_token j.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_token : slow.

Lemma rename_cterm_mkc_utoken {o} :
  forall r j, @rename_cterm o r (mkc_utoken j) = mkc_utoken j.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_utoken : slow.

Lemma rename_cterm_mkc_equality {o} :
  forall r (a b c : @CTerm o),
    rename_cterm r (mkc_equality a b c)
    = mkc_equality (rename_cterm r a) (rename_cterm r b) (rename_cterm r c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_equality : slow.

Lemma rename_cterm_mkc_free_from_atom {o} :
  forall r (a b c : @CTerm o),
    rename_cterm r (mkc_free_from_atom a b c)
    = mkc_free_from_atom (rename_cterm r a) (rename_cterm r b) (rename_cterm r c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_free_from_atom : slow.

Lemma rename_cterm_mkc_efree_from_atom {o} :
  forall r (a b c : @CTerm o),
    rename_cterm r (mkc_efree_from_atom a b c)
    = mkc_efree_from_atom (rename_cterm r a) (rename_cterm r b) (rename_cterm r c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_efree_from_atom : slow.

Lemma rename_cterm_mkc_free_from_atoms {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_free_from_atoms a b)
    = mkc_free_from_atoms (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_free_from_atoms : slow.

Lemma rename_cterm_mkc_apply {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_apply a b)
    = mkc_apply (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_apply : slow.

Lemma rename_cterm_mkc_apply2 {o} :
  forall r (a b c : @CTerm o),
    rename_cterm r (mkc_apply2 a b c)
    = mkc_apply2 (rename_cterm r a) (rename_cterm r b) (rename_cterm r c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_apply2 : slow.

Lemma rename_cterm_mkc_sup {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_sup a b)
    = mkc_sup (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_sup : slow.

Lemma rename_cterm_mkc_texc {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_texc a b)
    = mkc_texc (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_texc : slow.

Lemma rename_cterm_mkc_union {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_union a b)
    = mkc_union (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_union : slow.

Lemma rename_cterm_mkc_image {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_image a b)
    = mkc_image (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_image : slow.

Lemma rename_cterm_mkc_exception {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_exception a b)
    = mkc_exception (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_exception : slow.

Lemma rename_cterm_mkc_refl {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_refl a)
    = mkc_refl (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_refl : slow.

Lemma rename_cterm_mkc_inl {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_inl a)
    = mkc_inl (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_inl : slow.

Lemma rename_cterm_mkc_pertype {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_pertype a)
    = mkc_pertype (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_pertype : slow.

Lemma rename_cterm_mkc_ipertype {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_ipertype a)
    = mkc_ipertype (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_ipertype : slow.

Lemma rename_cterm_mkc_spertype {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_spertype a)
    = mkc_spertype (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_spertype : slow.

Lemma rename_cterm_mkc_inr {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_inr a)
    = mkc_inr (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_inr : slow.

Lemma rename_cterm_mkc_partial {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_partial a)
    = mkc_partial (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_partial : slow.

Lemma rename_cterm_mkc_mono {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_mono a)
    = mkc_mono (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_mono : slow.

Lemma rename_cterm_mkc_admiss {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_admiss a)
    = mkc_admiss (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_admiss : slow.

Lemma rename_cterm_mkc_requality {o} :
  forall r (a b c : @CTerm o),
    rename_cterm r (mkc_requality a b c)
    = mkc_requality (rename_cterm r a) (rename_cterm r b) (rename_cterm r c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_requality : slow.

Lemma rename_cterm_mkc_tequality {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_tequality a b)
    = mkc_tequality (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_tequality : slow.

Lemma rename_cterm_mkc_pair {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_pair a b)
    = mkc_pair (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_pair : slow.

Lemma rename_cterm_mkc_int {o} :
  forall r, @rename_cterm o r mkc_int = mkc_int.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_int : slow.

Lemma rename_cterm_mkc_base {o} :
  forall r, @rename_cterm o r mkc_base = mkc_base.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_base : slow.

Lemma rename_cterm_mkc_atom {o} :
  forall r, @rename_cterm o r mkc_atom = mkc_atom.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_atom : slow.

Lemma rename_cterm_mkc_uatom {o} :
  forall r, @rename_cterm o r mkc_uatom = mkc_uatom.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_uatom : slow.

Lemma rename_cterm_mkc_axiom {o} :
  forall r, @rename_cterm o r mkc_axiom = mkc_axiom.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_axiom : slow.

Lemma implies_alpha_eq_term_rename {o} :
  forall r (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (rename_term r a) (rename_term r b).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv aeq.

  - Case "vterm".
    inversion aeq; subst; clear aeq; simpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; simpl.
    apply alpha_eq_oterm_combine; repeat (rewrite map_length in * ); dands; auto.
    introv i.
    rewrite <- map_combine in i.
    allrw in_map_iff; exrepnd; ginv.
    applydup aeq0 in i1; clear aeq0.
    destruct a0, a; simpl in *.
    inversion i0 as [? ? ? ? ? disj len1 len2 norep aeq]; subst.
    applydup in_combine in i1; repnd.

    pose proof (ind n (lsubst n (var_ren l lv)) l) as q; clear ind.
    rewrite lsubst_allvars_preserves_osize2 in q.
    repeat (autodimp q hyp); eauto 2 with slow.
    apply q in aeq; clear q.
    repeat (rewrite @rename_term_lsubst in * ).
    autorewrite with slow in *.
    exists lv; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_alpha_eq_term_rename : slow.

Lemma implies_alpha_eq_bterm_rename {o} :
  forall r (a b : @BTerm o),
    alpha_eq_bterm a b
    -> alpha_eq_bterm (rename_bterm r a) (rename_bterm r b).
Proof.
  introv aeq.
    destruct a as [l1 t1], b as [l2 t2]; simpl in *.
    inversion aeq as [? ? ? ? ? disj len1 len2 norep aeq']; subst; clear aeq.
    exists lv; autorewrite with slow in *; auto.
    apply (implies_alpha_eq_term_rename r) in aeq'.
    repeat (rewrite @rename_term_lsubst in * ); autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_alpha_eq_bterm_rename : slow.

Lemma rename_bterm_idem {o} :
  forall r (b : @BTerm o),
    rename_bterm r (rename_bterm r b) = b.
Proof.
  introv; destruct b as [l t]; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_bterm_idem : slow.

Lemma rename_sub_idem {o} :
  forall r (s : @Sub o),
    rename_sub r (rename_sub r s) = s.
Proof.
  induction s; introv; repnd; simpl; autorewrite with slow; allrw; auto.
Qed.
Hint Rewrite @rename_sub_idem : slow.

Lemma implies_wf_sub_rename {o} :
  forall r (sub : @Sub o),
    wf_sub sub
    -> wf_sub (rename_sub r sub).
Proof.
  induction sub; introv wf; simpl in *; auto; repnd.
  allrw @wf_sub_cons_iff; repnd; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_wf_sub_rename : slow.

Lemma computes_to_exception_rename {o} :
  forall r lib (a b c : @NTerm o),
    computes_to_exception lib a b c
    -> computes_to_exception (rename_lib r lib) (rename_term r a) (rename_term r b) (rename_term r c).
Proof.
  introv comp.
  unfold computes_to_exception in *.
  apply (reduces_to_rename r) in comp; simpl in *; auto.
Qed.
Hint Resolve computes_to_exception_rename : slow.

Definition rename_seq {o} r (f : @ntseq o) : ntseq :=
  fun n => rename_term r (f n).

(*Lemma computes_to_seq_rename {o} :
  forall r lib (a : @NTerm o) f,
    computes_to_seq lib a f
    -> computes_to_seq (rename_lib r lib) (rename_term r a) (rename_seq r f).
Proof.
  introv comp.
  unfold computes_to_exception in *.
  apply (reduces_to_rename r) in comp; simpl in *; auto.
Qed.
Hint Resolve computes_to_seq_rename : slow.*)

Lemma implies_approx_rename {o} :
  forall r lib (a b : @NTerm o),
    approx lib a b
    -> approx (rename_lib r lib) (rename_term r a) (rename_term r b).
Proof.
  cofix IND; introv apr.
  inversion apr as [cl]; clear apr.
  constructor.
  unfold close_comput in *.
  repnd; dands; eauto 2 with slow.

  - clear cl3 cl.
    unfold close_compute_val in *.
    introv comp.
    apply (computes_to_value_rename r) in comp; simpl in *.
    autorewrite with slow in *.

    apply cl2 in comp; clear cl2.
    exrepnd.
    apply (computes_to_value_rename r) in comp1; simpl in *.
    eexists; dands; eauto.

    unfold lblift in *.
    rewrite map_length in *.
    repnd; dands; auto.
    introv h.
    applydup comp0 in h; clear comp0.

    rewrite selectbt_map; try omega.
    rewrite selectbt_map in h0; auto.

    remember (tl_subterms {[n]}) as u.
    remember (tr_subterms {[n]}) as v.
    clear Hequ Heqv.

    unfold blift in *; exrepnd.
    exists lv (rename_term r nt1) (rename_term r nt2).

    dands;
      try (complete (apply (implies_alpha_eq_bterm_rename r) in h2; simpl in *; autorewrite with slow in *; auto));
      try (complete (apply (implies_alpha_eq_bterm_rename r) in h1; simpl in *; autorewrite with slow in *; auto));[].

    unfold olift in *; repnd; dands; eauto 2 with slow;[].

    introv wf isp1 isp2.
    pose proof (h0 (rename_sub r sub)) as q.
    repeat (autodimp q hyp); eauto 2 with slow;
      try (complete (apply (isprogram_rename_term r) in isp1;rewrite rename_term_lsubst in isp1;autorewrite with slow in isp1;auto));
      try (complete (apply (isprogram_rename_term r) in isp2;rewrite rename_term_lsubst in isp2;autorewrite with slow in isp2;auto));[].

    repndors; tcsp;[].
    left.
    apply (IND r) in q.
    repeat (rewrite @rename_term_lsubst in * ).
    autorewrite with slow in *; auto.

  - clear cl2 cl.
    unfold close_compute_exc in *.
    introv comp.
    apply (computes_to_exception_rename r) in comp; simpl in *.
    autorewrite with slow in *.

    apply cl3 in comp; clear cl3.
    exrepnd.
    apply (computes_to_exception_rename r) in comp0; simpl in *.
    eexists; eexists; dands; eauto.

    + clear comp1.
      repndors; tcsp; left.
      apply (IND r) in comp2.
      repeat (rewrite @rename_term_lsubst in * ).
      autorewrite with slow in *; auto.

    + clear comp2.
      repndors; tcsp; left.
      apply (IND r) in comp1.
      repeat (rewrite @rename_term_lsubst in * ).
      autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_approx_rename : slow.

Lemma implies_approxc_rename {o} :
  forall r lib (a b : @CTerm o),
    approxc lib a b
    -> approxc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv ceq; destruct_cterms; unfold approxc in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_approxc_rename : slow.

Lemma implies_capproxc_rename {o} :
  forall r lib (a b : @CTerm o),
    capproxc lib a b
    -> capproxc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv apr; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_capproxc_rename : slow.

Lemma implies_cequivc_rename {o} :
  forall r lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv ceq; destruct_cterms; unfold cequivc in *; simpl in *.
  destruct ceq as [ap1 ap2].
  split; eauto 2 with slow.
Qed.
Hint Resolve implies_cequivc_rename : slow.

Lemma implies_ccequivc_rename {o} :
  forall r lib (a b : @CTerm o),
    ccequivc lib a b
    -> ccequivc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv apr; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_ccequivc_rename : slow.

Definition rename_cvterm {o} {vs} r (t : @CVTerm o vs) : CVTerm vs :=
  let (u,isp) := t in
  mk_cvterm vs (rename_term r u) (implies_isprog_vars_rename_term vs r u isp).

Lemma rename_cterm_isect {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_isect A v B)
    = mkc_isect (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_isect : rename.

Lemma rename_cterm_disect {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_disect A v B)
    = mkc_disect (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_disect : rename.

Lemma rename_cterm_function {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_function A v B)
    = mkc_function (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_function : rename.

Lemma rename_cterm_set {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_set A v B)
    = mkc_set (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_set : rename.

Lemma rename_cterm_product {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_product A v B)
    = mkc_product (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_product : rename.

Lemma rename_cterm_tunion {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_tunion A v B)
    = mkc_tunion (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_tunion : rename.

Lemma rename_cterm_w {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_w A v B)
    = mkc_w (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_w : rename.

Lemma rename_cterm_m {o} :
  forall r (A : @CTerm o) v B,
    rename_cterm r (mkc_m A v B)
    = mkc_m (rename_cterm r A) v (rename_cvterm r B).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_m : rename.

Lemma rename_cterm_substc {o} :
  forall r (a : @CTerm o) v b,
    rename_cterm r (substc a v b)
    = substc (rename_cterm r a) v (rename_cvterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  rewrite rename_term_subst; auto.
Qed.
Hint Rewrite @rename_cterm_substc : rename.

Definition rename_per1 {o} (r : renaming) (e : per(o)) : per :=
  fun a b =>
    exists a' b',
      a = rename_cterm r a'
      /\ b = rename_cterm r b'
      /\ e a' b'.

Definition rename_per {o} (r : renaming) (e : per(o)) : per :=
  fun a b => e (rename_cterm r a) (rename_cterm r b).

Lemma rename_per_iff {o} :
  forall r (e : per(o)), (rename_per r e) <=2=> (rename_per1 r e).
Proof.
  repeat introv; unfold rename_per, rename_per1; simpl; split; intro h.

  - exists (rename_cterm r t1) (rename_cterm r t2); autorewrite with slow; auto.

  - exrepnd; subst; autorewrite with slow; auto.
Qed.

Lemma rename_cterm_approx {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_approx a b)
    = mkc_approx (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_approx : rename.

Lemma rename_cterm_cequiv {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_cequiv a b)
    = mkc_cequiv (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_cequiv : rename.

Definition rename_per_fam {o} {ea : per(o)} r (eb : forall (a b : @CTerm o) (e : ea a b), per(o)) : per-fam(rename_per r ea) :=
  fun (a b : @CTerm o) (e : rename_per r ea a b) =>
    rename_per r (eb (rename_cterm r a) (rename_cterm r b) e).

Definition rename_fper {o} r (p : @CTerm o -> @CTerm o -> per(o)) :=
  fun a b => rename_per r (p (rename_cterm r a) (rename_cterm r b)).

Lemma inhabited_rename_fper {o} :
  forall r (p : @CTerm o -> @CTerm o -> per(o)) x y,
    inhabited (rename_fper r p x y) <=> inhabited (p (rename_cterm r x) (rename_cterm r y)).
Proof.
  introv; unfold inhabited, rename_fper, rename_per; split; introv h; exrepnd.
  - eexists; eauto.
  - exists (rename_cterm r t); autorewrite with slow; auto.
Qed.

Lemma is_per_rename_fper {o} :
  forall r (p : @CTerm o -> @CTerm o -> per(o)),
    is_per p -> is_per (rename_fper r p).
Proof.
  introv isp.
  unfold is_per in *; repnd.
  dands; introv; repeat (rw @inhabited_rename_fper); tcsp;[].
  introv inh1 inh2.
  eapply isp; eauto.
Qed.
Hint Resolve is_per_rename_fper : slow.

Lemma implies_rename_per {o} :
  forall r (e : per(o)) a b,
    e a b -> rename_per r e (rename_cterm r a) (rename_cterm r b).
Proof.
  introv h; unfold rename_per; autorewrite with slow; auto.
Defined.
Hint Resolve implies_rename_per : slow.

Lemma implies_weq_rename {o} :
  forall r lib eqa eqb (t1 t2 : @CTerm o),
    weq lib eqa eqb t1 t2
    -> weq (rename_lib r lib) (rename_per r eqa) (rename_per_fam r eqb) (rename_cterm r t1) (rename_cterm r t2).
Proof.
  introv w; induction w as [? ? ? ? ? ? ea c1 c2 ha hb]; spcast.
  apply (computes_to_valc_rename r) in c1.
  apply (computes_to_valc_rename r) in c2.
  autorewrite with slow rename in *.
  apply (weq_cons
           (rename_lib r lib)
           (rename_per r eqa)
           (rename_per_fam r eqb)
           (rename_cterm r t)
           (rename_cterm r t')
           (rename_cterm r a)
           (rename_cterm r f)
           (rename_cterm r a')
           (rename_cterm r f')
           (implies_rename_per r eqa a a' ea)); spcast; auto.
  introv w.
  unfold rename_per_fam, rename_per in w; autorewrite with slow rename in w.
  unfold implies_rename_per in w; simpl in w.

  remember (rename_choice_seq_val_idem r a') as r1; clear Heqr1.
  remember (rename_choice_seq_val_idem r a) as r2; clear Heqr2.
  revert r1 r2 w.
  unfold rename_choice_seq_val.
  rewrite (rename_cterm_idem r a).
  rewrite (rename_cterm_idem r a').
  introv w.

  unfold eq_ind_r in w; simpl in w.

  assert (r1 = eq_refl) as eqr1.
  { apply UIP. }
  assert (r2 = eq_refl) as eqr2.
  { apply UIP. }

  subst; simpl in *.
  apply hb in w; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_weq_rename : slow.

Lemma implies_meq_rename {o} :
  forall r lib eqa eqb (t1 t2 : @CTerm o),
    meq lib eqa eqb t1 t2
    -> meq (rename_lib r lib) (rename_per r eqa) (rename_per_fam r eqb) (rename_cterm r t1) (rename_cterm r t2).
Proof.
  cofix IND.
  introv m.
  destruct m as [? ? ? ? ea c1 c2 hb]; spcast.
  apply (computes_to_valc_rename r) in c1.
  apply (computes_to_valc_rename r) in c2.
  autorewrite with slow rename in *.
  apply (meq_cons
           (rename_lib r lib)
           (rename_per r eqa)
           (rename_per_fam r eqb)
           (rename_cterm r t1)
           (rename_cterm r t2)
           (rename_cterm r a)
           (rename_cterm r f)
           (rename_cterm r a')
           (rename_cterm r f')
           (implies_rename_per r eqa a a' ea)); spcast; auto.
  introv w.
  unfold rename_per_fam, rename_per in w; autorewrite with slow rename in w.
  unfold implies_rename_per in w; simpl in w.

  remember (rename_choice_seq_val_idem r a') as r1; clear Heqr1.
  remember (rename_choice_seq_val_idem r a) as r2; clear Heqr2.
  revert r1 r2 w.
  unfold rename_choice_seq_val.
  rewrite (rename_cterm_idem r a).
  rewrite (rename_cterm_idem r a').
  introv w.

  unfold eq_ind_r in w; simpl in w.

  assert (r1 = eq_refl) as eqr1.
  { apply UIP. }
  assert (r2 = eq_refl) as eqr2.
  { apply UIP. }

  subst; simpl in *.
  apply hb in w; autorewrite with slow in *; auto.
  apply (IND r) in w; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_meq_rename : slow.

Lemma rename_computes_to_excc {o} :
  forall r lib (n t e : @CTerm o),
    computes_to_excc lib n t e
    -> computes_to_excc (rename_lib r lib) (rename_cterm r n) (rename_cterm r t) (rename_cterm r e).
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_excc in *; simpl in *.
  apply (computes_to_exception_rename r) in comp; auto.
Qed.

Lemma implies_ccequivc_ext_rename {o} :
  forall r lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
  introv ceq ext.
  apply (implies_lib_extends_rename_lib r) in ext; autorewrite with slow in ext.
  apply ceq in ext; spcast.
  apply (implies_cequivc_rename r) in ext; autorewrite with slow in ext; auto.
Qed.
Hint Resolve implies_ccequivc_ext_rename : slow.

Lemma rename_per_image_eq {o} :
  forall r lib eqa (a b c : @CTerm o),
    per_image_eq (rename_lib r lib) (rename_per r eqa) (rename_cterm r a) (rename_cterm r b) (rename_cterm r c)
    <=> per_image_eq lib eqa a b c.
Proof.
  introv; split; introv h.

  - remember (rename_lib r lib) as lib'; revert lib Heqlib'.
    remember (rename_cterm r a) as a'; revert a Heqa'.
    remember (rename_cterm r b) as b'; revert b Heqb'.
    remember (rename_cterm r c) as c'; revert c Heqc'.

    induction h as [|? ? ? ? ? h1 h2]; introv e1 e2 e3 el; subst.

    + pose proof (IHh1 (rename_cterm r t)) as q; autorewrite with slow in q; autodimp q hyp; clear IHh1.
      pose proof (q b) as q; autodimp q hyp.
      pose proof (q a) as q; autodimp q hyp.
      pose proof (q lib) as q; autodimp q hyp.

      pose proof (IHh2 c) as w; autodimp w hyp; clear IHh2.
      pose proof (w (rename_cterm r t)) as w; autorewrite with slow in w; autodimp w hyp.
      pose proof (w a) as w; autodimp w hyp.
      pose proof (w lib) as w; autodimp w hyp.
      econstructor; eauto.

    + apply (implies_ccequivc_ext_rename r) in h1.
      apply (implies_ccequivc_ext_rename r) in h2.
      autorewrite with slow in *.
      eapply image_eq_eq; spcast; eauto.

  - induction h as [|? ? ? ? ? h1 h2].

    + econstructor; eauto.

    + apply (implies_ccequivc_ext_rename r) in h1.
      apply (implies_ccequivc_ext_rename r) in h2.
      autorewrite with slow in *.
      eapply image_eq_eq; spcast; eauto.
      unfold rename_per; autorewrite with slow; auto.
Qed.
Hint Resolve rename_per_image_eq : slow.

Lemma implies_rename_hasvaluec {o} :
  forall r lib (a : @CTerm o),
    hasvaluec lib a
    -> hasvaluec (rename_lib r lib) (rename_cterm r a).
Proof.
  unfold hasvaluec; introv hv; destruct_cterms; unfold hasvalue in *; simpl in *.
  exrepnd.
  apply (computes_to_value_rename r) in hv0.
  eexists; eauto.
Qed.
Hint Resolve implies_rename_hasvaluec : slow.

Lemma chaltsc_rename_iff {o} :
  forall r lib (a : @CTerm o),
    chaltsc lib a <=> chaltsc (rename_lib r lib) (rename_cterm r a).
Proof.
  introv; split; introv h; spcast.
  - apply (implies_rename_hasvaluec r) in h; auto.
  - apply (implies_rename_hasvaluec r) in h; autorewrite with slow in *; auto.
Qed.

Lemma implies_inhabited_rename_per_fam {o} :
  forall r (ea : per(o)) (eb : per-fam(ea)) a b (e : ea (rename_cterm r a) (rename_cterm r b)),
    inhabited (eb (rename_cterm r a) (rename_cterm r b) e)
    -> inhabited (rename_per_fam r eb a b e).
Proof.
  introv; unfold inhabited, rename_per_fam, rename_per.
  introv h; exrepnd.
  exists (rename_cterm r t); autorewrite with slow; auto.
Qed.

Lemma inhabited_rename_per_fam_implies {o} :
  forall r (ea : per(o)) (eb : per-fam(ea)) a b (e : ea (rename_cterm r a) (rename_cterm r b)),
    inhabited (rename_per_fam r eb a b e)
    -> inhabited (eb (rename_cterm r a) (rename_cterm r b) e).
Proof.
  introv; unfold inhabited, rename_per_fam, rename_per.
  introv h; exrepnd.
  exists (rename_cterm r t); autorewrite with slow; auto.
Qed.

Lemma rename_per_eq {o} :
  forall r (e : per(o)) a b,
    e a b = rename_per r e (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; unfold rename_per.
  f_equal; rewrite @rename_cterm_idem; auto.
Defined.

Lemma implies_rename_per_fam {o} :
  forall r (eqa : per(o)) (eqb : per-fam(eqa)) a a' b b' (e : eqa a a'),
    eqb a a' e b b'
    -> rename_per_fam
         r
         eqb
         (rename_cterm r a) (rename_cterm r a')
         (implies_rename_per r eqa a a' e)
         (rename_cterm r b) (rename_cterm r b').
Proof.
  introv h.
  unfold rename_per_fam, rename_per.
  unfold implies_rename_per, eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
  autorewrite with slow.

  remember (rename_choice_seq_val_idem r a) as w; clear Heqw.
  remember (rename_choice_seq_val_idem r a') as z; clear Heqz.
  unfold rename_choice_seq_val in *.
  revert w z; autorewrite with slow; introv.
  rewrite (UIP_refl _ _ w); auto; clear w.
  rewrite (UIP_refl _ _ z); auto; clear z.
Defined.

Lemma implies_rename_per_tunion_eq {o} :
  forall r (ea : per(o)) (eb : per-fam(ea)) t1 t2,
    per_tunion_eq ea eb t1 t2
    -> per_tunion_eq (rename_per r ea) (rename_per_fam r eb) (rename_cterm r t1) (rename_cterm r t2).
Proof.
  introv h.
  induction h as [|? ? ? ? h1 h2].

  - econstructor; eauto.

  - apply (tunion_eq_eq _ _ _ _ (rename_cterm r a1) (rename_cterm r a2) (implies_rename_per r ea a1 a2 h1)).
    apply implies_rename_per_fam; auto.
Qed.

Lemma eq_rename_per_idem {o} :
  forall r (e : per(o)),
    (rename_per r (rename_per r e)) <=2=> e.
Proof.
  repeat introv; unfold rename_per; autorewrite with slow; auto; tcsp.
Qed.

Lemma eq_rename_per_idem2 {o} :
  forall r (e : per(o)) a b,
    rename_per r (rename_per r e) a b = e a b.
Proof.
  repeat introv; unfold rename_per; autorewrite with slow; auto.
Defined.

Lemma eq_term_equals_per_tunion_eq_if2 {o} :
  forall (eqa1 eqa2 : per(o)) (eqb1 : per-fam(eqa1)) (eqb2 : per-fam(eqa2))
         (w : forall a b, eqa1 a b = eqa2 a b),
    (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2),
        (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 (@eq_ind _ _ (fun x => x) e1 (eqa2 a1 a2) (w a1 a2))))
    -> (forall (a1 a2 : CTerm) (e1 : eqa2 a1 a2),
           (eqb2 a1 a2 e1) <=2=> (eqb1 a1 a2 (@eq_ind _ _ (fun x => x) e1 (eqa1 a1 a2) (eq_sym (w a1 a2)))))
    -> (per_tunion_eq eqa1 eqb1) <=2=> (per_tunion_eq eqa2 eqb2).
Proof.
  introv imp1 imp2.
  introv; split; intro k; induction k.

  - apply @tunion_eq_cl with (t := t); sp.

  - apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := (eq_ind (eqa1 a1 a2) (fun x : [U] => x) e (eqa2 a1 a2) (w a1 a2))); sp; spcast.
    apply (imp1 a1 a2 e); auto.

  - apply @tunion_eq_cl with (t := t); sp.

  - apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := (eq_ind (eqa2 a1 a2) (fun x : [U] => x) e (eqa1 a1 a2) (eq_sym (w a1 a2)))); sp; spcast.
    apply (imp2 a1 a2 e); auto.
Qed.

Lemma rename_per_tunion_eq_implies {o} :
  forall r (ea : per(o)) (eb : per-fam(ea)) t1 t2,
    per_tunion_eq (rename_per r ea) (rename_per_fam r eb) (rename_cterm r t1) (rename_cterm r t2)
    -> per_tunion_eq ea eb t1 t2.
Proof.
  introv h.
  apply (implies_rename_per_tunion_eq r) in h; autorewrite with slow in h.

  eapply (eq_term_equals_per_tunion_eq_if2 _ _ _ _ (eq_rename_per_idem2 r ea));
    [| |eauto]; repeat introv.

  - unfold rename_per_fam, rename_per.
    unfold eq_ind, eq_rect; simpl.
    remember (eq_rename_per_idem2 r ea a1 a2) as w; clear Heqw.
    revert e1 w.
    unfold rename_per.
    autorewrite with slow; introv.
    rewrite (UIP_refl _ _ w); auto; tcsp.

  - unfold rename_per_fam, rename_per.
    unfold eq_ind, eq_rect; simpl.
    remember (eq_rename_per_idem2 r ea a1 a2) as w; clear Heqw.
    revert e1 w.
    unfold rename_per.
    autorewrite with slow; introv.
    rewrite (UIP_refl _ _ w); auto; tcsp.
Qed.

Lemma implies_rename_per2 {o} :
  forall r (e : per(o)) a b,
    e (rename_cterm r a) (rename_cterm r b) -> rename_per r e a b.
Proof.
  introv h; unfold rename_per; autorewrite with slow; auto.
Defined.

Lemma weq_eq_term_equals2 {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2 t1 t2
         (w : forall a b, eqa1 a b = eqa2 a b),
    (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2),
        (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 (@eq_ind _ _ (fun x => x) e1 (eqa2 a1 a2) (w a1 a2))))
    -> weq lib eqa1 eqb1 t1 t2
    -> weq lib eqa2 eqb2 t1 t2.
Proof.
  introv imp1 weqt.
  induction weqt as [t t' a f a' f' e c c' h h'].
  apply @weq_cons with (a := a) (a' := a') (f := f) (f' := f') (e := (eq_ind (eqa1 a a') (fun x => x) e (eqa2 a a') (w a a'))); sp.
  apply h'.
  apply imp1; auto.
Qed.

Lemma weq_rename_implies {o} :
  forall r lib eqa eqb (t1 t2 : @CTerm o),
    weq (rename_lib r lib) (rename_per r eqa) (rename_per_fam r eqb) (rename_cterm r t1) (rename_cterm r t2)
    -> weq lib eqa eqb t1 t2.
Proof.
  introv w.
  apply (implies_weq_rename r) in w; autorewrite with slow in *.
  eapply (weq_eq_term_equals2 _ _ _ _ _ _ _ (eq_rename_per_idem2 r eqa));[|eauto]; clear w.

  repeat introv.
  unfold rename_per_fam, rename_per.
  unfold eq_ind, eq_rect; simpl.
  remember (eq_rename_per_idem2 r eqa a1 a2) as w; clear Heqw.
  revert e1 w.
  unfold rename_per.
  autorewrite with slow; introv.
  rewrite (UIP_refl _ _ w); auto; tcsp.
Qed.
Hint Resolve weq_rename_implies : slow.

Lemma meq_eq_term_equals2 {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2 t1 t2
         (w : forall a b, eqa1 a b = eqa2 a b),
    (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2),
        (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 (@eq_ind _ _ (fun x => x) e1 (eqa2 a1 a2) (w a1 a2))))
    -> meq lib eqa1 eqb1 t1 t2
    -> meq lib eqa2 eqb2 t1 t2.
Proof.
  cofix IND.
  introv imp1 weqt.
  destruct weqt as [a f a' f' e c c' h].
  apply @meq_cons with (a := a) (a' := a') (f := f) (f' := f') (e := (eq_ind (eqa1 a a') (fun x => x) e (eqa2 a a') (w a a'))); sp.
  eapply IND;[|apply h]; auto.
  apply imp1; auto.
Qed.

Lemma meq_rename_implies {o} :
  forall r lib eqa eqb (t1 t2 : @CTerm o),
    meq (rename_lib r lib) (rename_per r eqa) (rename_per_fam r eqb) (rename_cterm r t1) (rename_cterm r t2)
    -> meq lib eqa eqb t1 t2.
Proof.
  introv w.
  apply (implies_meq_rename r) in w; autorewrite with slow in *.
  eapply (meq_eq_term_equals2 _ _ _ _ _ _ _ (eq_rename_per_idem2 r eqa));[|eauto]; clear w.

  repeat introv.
  unfold rename_per_fam, rename_per.
  unfold eq_ind, eq_rect; simpl.
  remember (eq_rename_per_idem2 r eqa a1 a2) as w; clear Heqw.
  revert e1 w.
  unfold rename_per.
  autorewrite with slow; introv.
  rewrite (UIP_refl _ _ w); auto; tcsp.
Qed.
Hint Resolve meq_rename_implies : slow.

Lemma getc_utokens_rename_cterm {o} :
  forall (r : renaming) (t : @CTerm o),
    getc_utokens (rename_cterm r t) = getc_utokens t.
Proof.
  introv; destruct_cterms; unfold getc_utokens; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @getc_utokens_rename_cterm : slow.

Lemma rename_name_not_in_upto {o} :
  forall r lib (a x : @CTerm o) e,
    name_not_in_upto (rename_lib r lib) (rename_cterm r a) (rename_cterm r x) (rename_per r e)
                     <=> name_not_in_upto lib a x e.
Proof.
  introv.
  unfold name_not_in_upto; split; intro h; exrepnd; spcast.

  - apply (computes_to_valc_rename r) in h0.
    unfold rename_per in *; autorewrite with slow in *.
    eexists; eexists; dands; spcast; eauto.
    autorewrite with slow; auto.

  - apply (computes_to_valc_rename r) in h0.
    unfold rename_per in *; autorewrite with slow in *.
    exists u (rename_cterm r y); dands; spcast; eauto; autorewrite with slow; auto.
Qed.

Lemma implies_noutokensc_rename_cterm {o} :
  forall (r : renaming) (t : @CTerm o),
    noutokensc t -> noutokensc (rename_cterm r t).
Proof.
  introv nout; destruct_cterms; unfold noutokensc in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_noutokensc_rename_cterm : slow.

Lemma rename_cterm_fix_approxc {o} :
  forall r k (f : @CTerm o),
    rename_cterm r (fix_approxc k f) = fix_approxc k (rename_cterm r f).
Proof.
  induction k; introv; simpl; auto.

  - apply cterm_eq; simpl; auto.

  - autorewrite with slow in *.
    rewrite IHk; auto.
Qed.

Lemma rename_cterm_subst_fapproxc {o} :
  forall r v (a : @CVTerm o [v]) f k,
    rename_cterm r (subst_fapproxc a f k)
    = subst_fapproxc (rename_cvterm r a) (rename_cterm r f) k.
Proof.
  introv; unfold subst_fapproxc.
  rewrite rename_cterm_substc; f_equal.
  apply rename_cterm_fix_approxc.
Qed.

Lemma rename_cvterm_idem {o} :
  forall r vs (t : @CVTerm o vs),
    rename_cvterm r (rename_cvterm r t) = t.
Proof.
  introv; destruct t; simpl.
  apply cvterm_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_cvterm_idem : slow.

Lemma cofinite_subst_fapprox_eqc_rename {o} :
  forall r (e : per(o)) v (a b : @CVTerm o [v]) f,
    cofinite_subst_fapprox_eqc e a b f
    -> cofinite_subst_fapprox_eqc (rename_per r e) (rename_cvterm r a) (rename_cvterm r b) (rename_cterm r f).
Proof.
  introv cof.
  unfold cofinite_subst_fapprox_eqc in *; exrepnd.
  exists j; introv h.
  apply cof0 in h; clear cof0.
  unfold rename_per.
  repeat (rewrite rename_cterm_subst_fapproxc).
  autorewrite with slow; auto.
Qed.

Lemma rename_cofinite_subst_fapprox_eqc {o} :
  forall r (e : per(o)) v (a b : @CVTerm o [v]) f,
    cofinite_subst_fapprox_eqc (rename_per r e) (rename_cvterm r a) (rename_cvterm r b) (rename_cterm r f)
    -> cofinite_subst_fapprox_eqc e a b f.
Proof.
  introv cof.
  unfold cofinite_subst_fapprox_eqc in *; exrepnd.
  exists j; introv h.
  apply cof0 in h; clear cof0.
  unfold rename_per in *.
  repeat (rewrite rename_cterm_subst_fapproxc in h).
  autorewrite with slow in *; auto.
Qed.

Lemma rename_cofinite_subst_fapprox_eqc2 {o} :
  forall r (e : per(o)) v (a b : @CVTerm o [v]) f,
    cofinite_subst_fapprox_eqc (rename_per r e) a b f
    -> cofinite_subst_fapprox_eqc e (rename_cvterm r a) (rename_cvterm r b) (rename_cterm r f).
Proof.
  introv cof.
  unfold cofinite_subst_fapprox_eqc in *; exrepnd.
  exists j; introv h.
  apply cof0 in h; clear cof0.
  unfold rename_per in *.
  repeat (rewrite rename_cterm_subst_fapproxc in h).
  autorewrite with slow in *; auto.
Qed.

Lemma rename_cterm_mkc_fix {o} :
  forall r (a : @CTerm o),
    rename_cterm r (mkc_fix a)
    = mkc_fix (rename_cterm r a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_mkc_fix : slow.

Lemma admissible_equality_rename {o} :
  forall r (e : per(o)),
    admissible_equality (rename_per r e)
                        <=> admissible_equality e.
Proof.
  introv; unfold admissible_equality; split; introv h cof.

  - apply (cofinite_subst_fapprox_eqc_rename r) in cof.
    apply h in cof; clear h.
    unfold subst_fix_eqc, rename_per, subst_fixc in *.
    repeat (rewrite rename_cterm_substc in cof); autorewrite with slow in cof; auto.

  - apply (rename_cofinite_subst_fapprox_eqc2 r) in cof.
    apply h in cof; clear h.
    unfold subst_fix_eqc, rename_per, subst_fixc in *.
    repeat (rewrite rename_cterm_substc); autorewrite with slow; auto.
Qed.

Lemma mono_equality_rename {o} :
  forall r lib (ea : per(o)),
    mono_equality (rename_lib r lib) (rename_per r ea)
    <=> mono_equality lib ea.
Proof.
  introv; split; introv mono e apr; unfold mono_equality in *.

  - apply (implies_approxc_rename r) in apr.
    apply mono in apr; auto; eauto 3 with slow.
    unfold rename_per in *; autorewrite with slow in *; auto.

  - apply (implies_approxc_rename r) in apr.
    autorewrite with slow in *.
    apply mono in apr; auto; eauto 3 with slow.
Qed.

Lemma rename_cterm_pw {o} :
  forall r (P : @CTerm o) ap A bp ba B cp ca cb C p ,
    rename_cterm r (mkc_pw P ap A bp ba B cp ca cb C p)
    = mkc_pw (rename_cterm r P) ap (rename_cvterm r A) bp ba (rename_cvterm r B) cp ca cb (rename_cvterm r C) (rename_cterm r p).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_pw : rename.

Lemma rename_cterm_pm {o} :
  forall r (P : @CTerm o) ap A bp ba B cp ca cb C p ,
    rename_cterm r (mkc_pm P ap A bp ba B cp ca cb C p)
    = mkc_pm (rename_cterm r P) ap (rename_cvterm r A) bp ba (rename_cvterm r B) cp ca cb (rename_cvterm r C) (rename_cterm r p).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_pm : rename.

Definition rename_per_fam_fam
           {o}
           r
           {ep : per(o)}
           {ea : forall p p', ep p p' -> per(o)}
           (eb : forall p p' (ep : ep p p') a a', ea p p' ep a a' -> per(o))
  : per-fam-fam(rename_per r ep,rename_per_fam r ea) :=
  fun (p p' : @CTerm o)
      (e : rename_per r ep p p')
      a a'
      (f : rename_per r (ea (rename_cterm r p) (rename_cterm r p') e) a a') =>
    rename_per r (eb (rename_cterm r p) (rename_cterm r p') e (rename_cterm r a) (rename_cterm r a') f).

Lemma rename_sub_csub2sub {o} :
  forall r (s : @CSub o),
    rename_sub r (csub2sub s) = csub2sub (rename_csub r s).
Proof.
  introv; unfold rename_sub, rename_csub, csub2sub.
  allrw map_map; unfold compose; auto.
  apply eq_maps; introv i; repnd; simpl; auto.
  destruct_cterms; simpl; auto.
Qed.

Lemma rename_csubst {o} :
  forall r (t : @NTerm o) s,
    rename_term r (csubst t s) = csubst (rename_term r t) (rename_csub r s).
Proof.
  introv.
  unfold csubst.
  rewrite rename_term_lsubst.
  rewrite rename_sub_csub2sub; auto.
Qed.
Hint Rewrite @rename_csubst : rename.

Lemma rename_cterm_lsubstc2 {o} :
  forall r a (A : @CTerm o) b B C,
    rename_cterm r (lsubstc2 a A b B C)
    = lsubstc2 a (rename_cterm r A) b (rename_cterm r B) (rename_cvterm r C).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  rewrite rename_csubst; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_lsubstc2 : rename.

Lemma rename_cterm_lsubstc3 {o} :
  forall r a (A : @CTerm o) b B c C D,
    rename_cterm r (lsubstc3 a A b B c C D)
    = lsubstc3 a (rename_cterm r A) b (rename_cterm r B) c (rename_cterm r C) (rename_cvterm r D).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  rewrite rename_csubst; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_lsubstc3 : rename.

Lemma implies_pweq_rename {o} :
  forall r lib eqp eqa eqb cp ca cb C p (t1 t2 : @CTerm o),
    pweq lib eqp eqa eqb cp ca cb C p t1 t2
    -> pweq
         (rename_lib r lib)
         (rename_per r eqp)
         (rename_per_fam r eqa)
         (rename_per_fam_fam r eqb)
         cp ca cb
         (rename_cvterm r C)
         (rename_cterm r p)
         (rename_cterm r t1)
         (rename_cterm r t2).
Proof.
  introv w; induction w as [? ? ? ? ? ? ? ? ea c1 c2 ha hb]; spcast.
  apply (computes_to_valc_rename r) in c1.
  apply (computes_to_valc_rename r) in c2.
  autorewrite with slow rename in *.
  apply (pweq_cons
           (rename_lib r lib)
           (rename_per r eqp)
           (rename_per_fam r eqa)
           (rename_per_fam_fam r eqb)
           cp ca cb
           (rename_cvterm r C)
           (rename_cterm r p)
           (rename_cterm r t1)
           (rename_cterm r t2)
           (implies_rename_per r eqp p p ep)
           (rename_cterm r a1)
           (rename_cterm r f1)
           (rename_cterm r a2)
           (rename_cterm r f2)
           (implies_rename_per_fam r eqp eqa p p a1 a2 ep ea)
        ); spcast; auto.
  introv w.
  unfold rename_per_fam_fam, rename_per_fam, rename_per in w; autorewrite with slow rename in w.

  unfold implies_rename_per, implies_rename_per_fam in w; simpl in w.

  remember (rename_choice_seq_val_idem r a1) as ra1; clear Heqra1.
  remember (rename_choice_seq_val_idem r a2) as ra2; clear Heqra2.
  remember (rename_choice_seq_val_idem r p) as rp; clear Heqrp.
  revert ra1 ra2 rp w.
  unfold rename_choice_seq_val.
  rewrite (rename_cterm_idem r a1).
  rewrite (rename_cterm_idem r a2).
  rewrite (rename_cterm_idem r p).
  introv w.

  unfold eq_ind_r in w; simpl in w.

  assert (ra1 = eq_refl) as eqr1.
  { apply UIP. }
  assert (ra2 = eq_refl) as eqr2.
  { apply UIP. }
  assert (rp = eq_refl) as eqr3.
  { apply UIP. }

  subst; simpl in w.

  unfold eq_ind, eq_rect, eq_sym in w.
  rewrite Equality.UIP_refl_refl in w.
  apply hb in w; autorewrite with rename slow in *; auto; tcsp.
Qed.

Lemma implies_pmeq_rename {o} :
  forall r lib eqp eqa eqb cp ca cb C p (t1 t2 : @CTerm o),
    pmeq lib eqp eqa eqb cp ca cb C p t1 t2
    -> pmeq
         (rename_lib r lib)
         (rename_per r eqp)
         (rename_per_fam r eqa)
         (rename_per_fam_fam r eqb)
         cp ca cb
         (rename_cvterm r C)
         (rename_cterm r p)
         (rename_cterm r t1)
         (rename_cterm r t2).
Proof.
  cofix IND.
  introv w; destruct w as [? ? ? ? ? ea c1 c2 hb]; spcast.
  apply (computes_to_valc_rename r) in c1.
  apply (computes_to_valc_rename r) in c2.
  autorewrite with slow rename in *.
  apply (pmeq_cons
           (rename_lib r lib)
           (rename_per r eqp)
           (rename_per_fam r eqa)
           (rename_per_fam_fam r eqb)
           cp ca cb
           (rename_cvterm r C)
           (rename_cterm r p)
           (rename_cterm r t1)
           (rename_cterm r t2)
           (implies_rename_per r eqp p p ep)
           (rename_cterm r a1)
           (rename_cterm r f1)
           (rename_cterm r a2)
           (rename_cterm r f2)
           (implies_rename_per_fam r eqp eqa p p a1 a2 ep ea)
        ); spcast; auto.
  introv w.
  unfold rename_per_fam_fam, rename_per_fam, rename_per in w; autorewrite with slow rename in w.

  unfold implies_rename_per, implies_rename_per_fam in w; simpl in w.

  remember (rename_choice_seq_val_idem r a1) as ra1; clear Heqra1.
  remember (rename_choice_seq_val_idem r a2) as ra2; clear Heqra2.
  remember (rename_choice_seq_val_idem r p) as rp; clear Heqrp.
  revert ra1 ra2 rp w.
  unfold rename_choice_seq_val.
  rewrite (rename_cterm_idem r a1).
  rewrite (rename_cterm_idem r a2).
  rewrite (rename_cterm_idem r p).
  introv w.

  unfold eq_ind_r in w; simpl in w.

  assert (ra1 = eq_refl) as eqr1.
  { apply UIP. }
  assert (ra2 = eq_refl) as eqr2.
  { apply UIP. }
  assert (rp = eq_refl) as eqr3.
  { apply UIP. }

  subst; simpl in w.

  unfold eq_ind_r in w; simpl in w.
  unfold eq_ind, eq_rect, eq_sym in w.
  rewrite Equality.UIP_refl_refl in w.
  apply hb in w; autorewrite with rename slow in *; auto.
  apply (IND r) in w; autorewrite with slow rename in *; auto.
Qed.

Lemma eq_pweq_implies {o} :
  forall lib
         (eqp1 eqp2 : per(o))
         (eqa1 : per-fam(eqp1)) (eqa2 : per-fam(eqp2))
         (eqb1 : per-fam-fam(eqp1,eqa1)) (eqb2 : per-fam-fam(eqp2,eqa2))
         cp ca cb C p t1 t2
         (w1 : forall a b, eqp1 a b = eqp2 a b)
         (w2 : forall a b (e1 : eqp1 a b) c d,
             eqa1 a b e1 c d
             = eqa2 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b)) c d)
         (w3 : forall a b (e1 : eqp1 a b) c d (e2 : eqa1 a b e1 c d) e f,
             eqb1 a b e1 c d e2 e f
             = eqb2
                 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b))
                 c d (@eq_ind _ _ (fun x => x) e2 (eqa2 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b)) c d) (w2 a b e1 c d))
                 e f),
    pweq lib eqp1 eqa1 eqb1 cp ca cb C p t1 t2
    -> pweq lib eqp2 eqa2 eqb2 cp ca cb C p t1 t2.
Proof.
  introv w3 pw.
  induction pw as [p t1 t2 ep a f a' f' e c c' h h'].

  apply (pweq_cons
           lib eqp2 eqa2 eqb2 cp ca cb C p t1 t2
           (@eq_ind _ _ (fun x => x) ep (eqp2 p p) (w1 p p))
           a f a' f'
           (@eq_ind _ _ (fun x => x) e (eqa2 p p (@eq_ind _ _ (fun x => x) ep (eqp2 p p) (w1 p p)) a a') (w2 p p ep a a'))); spcast; auto.
  introv w.
  apply h'.
  pose proof (w3 p p ep a a' e b1 b2) as z.
  rewrite z; auto.
Qed.

Lemma pweq_rename_implies {o} :
  forall r lib eqp eqa eqb cp ca cb C p (t1 t2 : @CTerm o),
    pweq
      (rename_lib r lib)
      (rename_per r eqp)
      (rename_per_fam r eqa)
      (rename_per_fam_fam r eqb)
      cp ca cb
      (rename_cvterm r C)
      (rename_cterm r p)
      (rename_cterm r t1)
      (rename_cterm r t2)
    -> pweq lib eqp eqa eqb cp ca cb C p t1 t2.
Proof.
  introv w.
  apply (implies_pweq_rename r) in w; autorewrite with slow in *.

  assert (forall a b, rename_per r (rename_per r eqp) a b = eqp a b) as w1.
  { introv; unfold rename_per; autorewrite with slow; auto. }

  assert (forall a b (e1 : rename_per r (rename_per r eqp) a b) c d,
             rename_per_fam r (rename_per_fam r eqa) a b e1 c d
             = eqa a b (@eq_ind _ _ (fun x => x) e1 (eqp a b) (w1 a b)) c d) as w2.
  {
    introv.
    revert e1.
    remember (w1 a b) as q; clear Heqq.
    revert q.
    unfold rename_per_fam, rename_per; autorewrite with slow.
    introv.
    unfold eq_ind, eq_rect; simpl.
    rewrite (UIP_refl _ _ q); auto.
  }

  eapply (eq_pweq_implies _ _ _ _ _ _ _ _ _ _ _ _ _ _ w1 w2);[|exact w].
  clear w.
  introv.

  remember (w2 a b e1 c d) as q; clear Heqq.
  remember (w1 a b) as z; clear Heqz.

  revert e1 e2 z q.
  unfold eq_ind, eq_rect; simpl.
  unfold rename_per_fam_fam, rename_per_fam, rename_per; simpl.
  autorewrite with slow rename.
  introv.
  revert q.
  rewrite (UIP_refl _ _ z); auto.
  introv.
  rewrite (UIP_refl _ _ q); auto.
Qed.
Hint Resolve pweq_rename_implies : slow.

Lemma eq_pmeq_implies {o} :
  forall lib
         (eqp1 eqp2 : per(o))
         (eqa1 : per-fam(eqp1)) (eqa2 : per-fam(eqp2))
         (eqb1 : per-fam-fam(eqp1,eqa1)) (eqb2 : per-fam-fam(eqp2,eqa2))
         cp ca cb C p t1 t2
         (w1 : forall a b, eqp1 a b = eqp2 a b)
         (w2 : forall a b (e1 : eqp1 a b) c d,
             eqa1 a b e1 c d
             = eqa2 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b)) c d)
         (w3 : forall a b (e1 : eqp1 a b) c d (e2 : eqa1 a b e1 c d) e f,
             eqb1 a b e1 c d e2 e f
             = eqb2
                 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b))
                 c d (@eq_ind _ _ (fun x => x) e2 (eqa2 a b (@eq_ind _ _ (fun x => x) e1 (eqp2 a b) (w1 a b)) c d) (w2 a b e1 c d))
                 e f),
    pmeq lib eqp1 eqa1 eqb1 cp ca cb C p t1 t2
    -> pmeq lib eqp2 eqa2 eqb2 cp ca cb C p t1 t2.
Proof.
  cofix IND.
  introv w3 pw.
  destruct pw as [ ep a f a' f' e c c' h].

  apply (pmeq_cons
           lib eqp2 eqa2 eqb2 cp ca cb C p t1 t2
           (@eq_ind _ _ (fun x => x) ep (eqp2 p p) (w1 p p))
           a f a' f'
           (@eq_ind _ _ (fun x => x) e (eqa2 p p (@eq_ind _ _ (fun x => x) ep (eqp2 p p) (w1 p p)) a a') (w2 p p ep a a'))); spcast; auto.
  introv w.
  eapply IND; eauto.
  apply h.
  pose proof (w3 p p ep a a' e b1 b2) as z.
  rewrite z; auto.
Qed.

Lemma pmeq_rename_implies {o} :
  forall r lib eqp eqa eqb cp ca cb C p (t1 t2 : @CTerm o),
    pmeq
      (rename_lib r lib)
      (rename_per r eqp)
      (rename_per_fam r eqa)
      (rename_per_fam_fam r eqb)
      cp ca cb
      (rename_cvterm r C)
      (rename_cterm r p)
      (rename_cterm r t1)
      (rename_cterm r t2)
    -> pmeq lib eqp eqa eqb cp ca cb C p t1 t2.
Proof.
  introv w.
  apply (implies_pmeq_rename r) in w; autorewrite with slow in *.

  assert (forall a b, rename_per r (rename_per r eqp) a b = eqp a b) as w1.
  { introv; unfold rename_per; autorewrite with slow; auto. }

  assert (forall a b (e1 : rename_per r (rename_per r eqp) a b) c d,
             rename_per_fam r (rename_per_fam r eqa) a b e1 c d
             = eqa a b (@eq_ind _ _ (fun x => x) e1 (eqp a b) (w1 a b)) c d) as w2.
  {
    introv.
    revert e1.
    remember (w1 a b) as q; clear Heqq.
    revert q.
    unfold rename_per_fam, rename_per; autorewrite with slow.
    introv.
    unfold eq_ind, eq_rect; simpl.
    rewrite (UIP_refl _ _ q); auto.
  }

  eapply (eq_pmeq_implies _ _ _ _ _ _ _ _ _ _ _ _ _ _ w1 w2);[|exact w].
  clear w.
  introv.

  remember (w2 a b e1 c d) as q; clear Heqq.
  remember (w1 a b) as z; clear Heqz.

  revert e1 e2 z q.
  unfold eq_ind, eq_rect; simpl.
  unfold rename_per_fam_fam, rename_per_fam, rename_per; simpl.
  autorewrite with slow rename.
  introv.
  revert q.
  rewrite (UIP_refl _ _ z); auto.
  introv.
  rewrite (UIP_refl _ _ q); auto.
Qed.
Hint Resolve pmeq_rename_implies : slow.


Lemma implies_iff_all_in_ex_bar {o} :
  forall (lib : @library o) F G,
    in_ext lib (fun lib => F lib <-> G lib)
    -> (all_in_ex_bar lib F <=> all_in_ex_bar lib G).
Proof.
  introv h; split; intro q.
  - eapply all_in_ex_bar_modus_ponens1;[|exact q]; clear q; introv xt q; apply h; auto.
  - eapply all_in_ex_bar_modus_ponens1;[|exact q]; clear q; introv xt q; apply h; auto.
Qed.

Definition rename_inf_choice_seq_vals {o} r (f : @InfChoiceSeqVals o) : InfChoiceSeqVals :=
  fun n => rename_choice_seq_val r (f n).

Definition rename_inf_choice_seq_entry {o} (r : renaming) (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  match e with
  | MkInfChoiceSeqEntry _ vals restr =>
    MkInfChoiceSeqEntry _ (rename_inf_choice_seq_vals r vals) (rename_choice_seq_restriction r restr)
  end.

Definition rename_inf_library_entry {o} (r : renaming) (e : @inf_library_entry o) : inf_library_entry :=
  match e with
  | inf_lib_cs name e => inf_lib_cs name (rename_inf_choice_seq_entry r e)
  | inf_lib_abs opabs vars rhs correct =>
    inf_lib_abs (rename_opabs r opabs) vars (rename_soterm r rhs) (rename_correct r correct)
  end.

Definition rename_inf_lib {o} r (infl : @inf_library o) : inf_library :=
  fun n => rename_inf_library_entry r (infl n).

Lemma implies_inf_choice_sequence_vals_extend_rename {o} :
  forall r ivals (vals : @ChoiceSeqVals o),
    inf_choice_sequence_vals_extend ivals vals
    -> inf_choice_sequence_vals_extend (rename_inf_choice_seq_vals r ivals) (rename_choice_seq_vals r vals).
Proof.
  introv h i.
  unfold inf_choice_sequence_vals_extend in *.
  unfold rename_inf_choice_seq_vals.
  unfold rename_choice_seq_val.
  rewrite select_rename_choice_seq_vals_eq in i.
  remember (select n vals) as sel; symmetry in Heqsel; destruct sel; ginv.
  apply h in Heqsel; rewrite Heqsel; auto.
Qed.
Hint Resolve implies_inf_choice_sequence_vals_extend_rename : slow.

Lemma implies_inf_choice_sequence_entry_extends_rename {o} :
  forall r (ie : @InfChoiceSeqEntry o) e,
    inf_choice_sequence_entry_extend ie e
    -> inf_choice_sequence_entry_extend (rename_inf_choice_seq_entry r ie) (rename_choice_seq_entry r e).
Proof.
  introv h.
  destruct ie, e; simpl in *.
  unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_inf_choice_sequence_entry_extends_rename : slow.

Lemma implies_inf_entry_extends_rename {o} :
  forall r (ie : @inf_library_entry o) e,
    inf_entry_extends ie e
    -> inf_entry_extends (rename_inf_library_entry r ie) (rename_library_entry r e).
Proof.
  introv h.
  destruct ie, e; simpl in *; repnd; subst; tcsp.
  dands; eauto 3 with slow.
Qed.
Hint Resolve implies_inf_entry_extends_rename : slow.

Lemma implies_inf_matching_entries_rename {o} :
  forall r (ie : @inf_library_entry o) e,
    inf_matching_entries ie e
    -> inf_matching_entries (rename_inf_library_entry r ie) (rename_library_entry r e).
Proof.
  introv h; destruct ie, e; unfold inf_matching_entries in *; simpl in *; tcsp.
  destruct opabs, opabs0; unfold same_opabs, matching_entry_sign in *; simpl in *; repnd; subst; dands; tcsp.
Qed.
Hint Resolve implies_inf_matching_entries_rename : slow.

Lemma rename_inf_choice_seq_vals_idem {o} :
  forall r (ivals : @InfChoiceSeqVals o),
    rename_inf_choice_seq_vals r (rename_inf_choice_seq_vals r ivals) = ivals.
Proof.
  introv.
  apply functional_extensionality; introv; simpl.
  unfold rename_inf_choice_seq_vals; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_inf_choice_seq_vals_idem : slow.

Lemma rename_inf_choice_seq_entry_idem {o} :
  forall r (entry : @InfChoiceSeqEntry o),
    rename_inf_choice_seq_entry r (rename_inf_choice_seq_entry r entry) = entry.
Proof.
  introv; destruct entry; simpl; autorewrite with slow; f_equal.
Qed.
Hint Rewrite @rename_inf_choice_seq_entry_idem : slow.

Lemma rename_inf_library_entry_idem {o} :
  forall r (ie : @inf_library_entry o),
    rename_inf_library_entry r (rename_inf_library_entry r ie) = ie.
Proof.
  introv; destruct ie; simpl; autorewrite with slow; auto;[].
  remember (rename_correct r (rename_correct r correct)) as cor; clear Heqcor.
  revert cor.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Rewrite @rename_inf_library_entry_idem : slow.

Lemma implies_entry_in_inf_library_extends_rename {o} :
  forall r (entry : @library_entry o) n infLib,
    entry_in_inf_library_extends entry n infLib
    -> entry_in_inf_library_extends (rename_library_entry r entry) n (rename_inf_lib r infLib).
Proof.
  induction n; introv h; simpl in *; tcsp.
  repndors;[left|right]; eauto 3 with slow.

  - unfold rename_inf_lib; simpl; eauto 3 with slow.

  - repnd.
    dands; eauto 3 with slow.
    introv xx; destruct h0.
    unfold rename_inf_lib in *; simpl in *.
    apply (implies_inf_matching_entries_rename r) in xx.
    autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_entry_in_inf_library_extends_rename : slow.

Lemma rename_is_default_choice_seq_entry_iff {o} :
  forall r (entry : @ChoiceSeqEntry o),
    is_default_choice_seq_entry (rename_choice_seq_entry r entry)
    <-> is_default_choice_seq_entry entry.
Proof.
  introv.
  unfold is_default_choice_seq_entry; destruct entry as [vals restr]; simpl.
  unfold is_default_choice_sequence; destruct restr; simpl; split; introv h.

  - introv w.
    pose proof (select_rename_choice_seq_vals_eq r n vals) as q.
    rewrite w in q.
    apply h in q.
    rewrite <- (rename_cterm_idem r v).
    rewrite <- (rename_cterm_idem r (d n)).
    unfold rename_choice_seq_val in *; rewrite q; auto.

  - introv w.
    rewrite select_rename_choice_seq_vals_eq in w.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; ginv.
    apply h in Heqsel; subst; auto.

  - introv w.
    pose proof (select_rename_choice_seq_vals_eq r n vals) as q.
    rewrite w in q.
    apply h in q.
    rewrite <- (rename_cterm_idem r v).
    rewrite <- (rename_cterm_idem r (f n)).
    unfold rename_choice_seq_val in *; rewrite q; auto.

  - introv w.
    rewrite select_rename_choice_seq_vals_eq in w.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; ginv.
    apply h in Heqsel; subst; auto.
Qed.
Hint Rewrite @rename_is_default_choice_seq_entry_iff : slow.

Lemma is_cs_default_entry_rename_iff {o} :
  forall r (entry : @library_entry o),
    is_cs_default_entry (rename_library_entry r entry)
    <-> is_cs_default_entry entry.
Proof.
  introv.
  unfold is_cs_default_entry.
  destruct entry; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @is_cs_default_entry_rename_iff : slow.

Lemma implies_entry_in_inf_library_default {o} :
  forall r (entry : @library_entry o) infLib,
    entry_in_inf_library_default entry infLib
    -> entry_in_inf_library_default (rename_library_entry r entry) (rename_inf_lib r infLib).
Proof.
  unfold entry_in_inf_library_default; introv h; repnd; dands; eauto 3 with slow.

  {
    introv q.
    destruct (h0 n).
    apply (implies_inf_matching_entries_rename r) in q.
    unfold rename_inf_lib in *; autorewrite with slow in *; auto.
  }

  { apply safe_library_entry_rename_iff; auto. }

  { apply is_cs_default_entry_rename_iff; auto. }
Qed.
Hint Resolve implies_entry_in_inf_library_default : slow.

Lemma implies_inf_lib_extends_ext_entries_rename {o} :
  forall r (infLib : @inf_library o) lib,
    inf_lib_extends_ext_entries infLib lib
    -> inf_lib_extends_ext_entries (rename_inf_lib r infLib) (rename_lib r lib).
Proof.
  introv h i.
  apply (implies_entry_in_library_rename r) in i; autorewrite with slow in *.
  apply h in i; repndors; exrepnd;[left|right]; eauto 3 with slow.

  - exists n.
    apply (implies_entry_in_inf_library_extends_rename r) in i0; autorewrite with slow in *; auto.

  - apply (implies_entry_in_inf_library_default r) in i; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_rename : slow.

Lemma implies_rename_matching_inf_entries {o} :
  forall r (e1 e2 : @inf_library_entry o),
    matching_inf_entries e1 e2
    -> matching_inf_entries (rename_inf_library_entry r e1) (rename_inf_library_entry r e2).
Proof.
  introv h.
  unfold matching_inf_entries in *.
  destruct e1, e2; simpl in *; subst; tcsp.
  destruct opabs, opabs0; unfold same_opabs, matching_entry_sign in *; simpl in *; repnd; subst; dands; tcsp.
Qed.

Lemma implies_entry_in_inf_library_n_rename {o} :
  forall r n e (lib : @inf_library o),
    entry_in_inf_library_n n e lib
    -> entry_in_inf_library_n n (rename_inf_library_entry r e) (rename_inf_lib r lib).
Proof.
  induction n; introv h; simpl in *; tcsp.
  repndors; subst; repnd; tcsp.
  right; dands; eauto 3 with slow.
  introv xx; destruct h0.
  apply (implies_rename_matching_inf_entries r) in xx.
  unfold rename_inf_lib in *.
  autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_entry_in_inf_library_n_rename : slow.

Lemma inf_choice_sequence_satisfies_restriction_rename {o} :
  forall r (vals : @InfChoiceSeqVals o) restr,
    inf_choice_sequence_satisfies_restriction
      (rename_inf_choice_seq_vals r vals)
      (rename_choice_seq_restriction r restr)
    <-> inf_choice_sequence_satisfies_restriction vals restr.
Proof.
  introv.
  unfold inf_choice_sequence_satisfies_restriction.
  destruct restr; simpl; split; intro h; introv.

  - pose proof (h n) as h.
    unfold rename_restriction_pred in *.
    unfold rename_inf_choice_seq_vals in *.
    unfold rename_choice_seq_val in *.
    autorewrite with slow in *; auto.

  - unfold rename_restriction_pred in *.
    unfold rename_inf_choice_seq_vals in *.
    unfold rename_choice_seq_val in *.
    autorewrite with slow in *; auto.

  - pose proof (h n) as h.
    unfold rename_inf_choice_seq_vals in *.
    unfold rename_choice_seq_val in *.
    rewrite <- (rename_cterm_idem r (vals n)).
    rewrite <- (rename_cterm_idem r (f n)).
    rewrite h; auto.

  - unfold rename_inf_choice_seq_vals in *.
    rewrite h; auto.
Qed.
Hint Rewrite @inf_choice_sequence_satisfies_restriction_rename : slow.

Lemma safe_inf_choice_sequence_entry_rename {o} :
  forall r name (entry : @InfChoiceSeqEntry o),
    safe_inf_choice_sequence_entry name (rename_inf_choice_seq_entry r entry)
    <-> safe_inf_choice_sequence_entry name entry.
Proof.
  introv.
  unfold safe_inf_choice_sequence_entry; destruct entry; simpl.
  autorewrite with slow; tcsp.
Qed.
Hint Rewrite @safe_inf_choice_sequence_entry_rename : slow.

Lemma safe_inf_library_entry_rename {o} :
  forall r (e : @inf_library_entry o),
    safe_inf_library_entry (rename_inf_library_entry r e)
    <-> safe_inf_library_entry e.
Proof.
  introv.
  unfold safe_inf_library_entry.
  destruct e; simpl; tcsp; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @safe_inf_library_entry_rename : slow.

Lemma rename_is_default_inf_choice_seq_entry_iff {o} :
  forall r (entry : @InfChoiceSeqEntry o),
    is_default_inf_choice_seq_entry (rename_inf_choice_seq_entry r entry)
    <-> is_default_inf_choice_seq_entry entry.
Proof.
  introv.
  unfold is_default_inf_choice_seq_entry; destruct entry as [vals restr]; simpl.
  unfold is_default_inf_choice_sequence; destruct restr; simpl; split; introv h.

  - introv.
    pose proof (h n) as h.
    unfold rename_inf_choice_seq_vals in *.
    rewrite <- (rename_choice_seq_val_idem r (vals n)).
    rewrite <- (rename_choice_seq_val_idem r (d n)).
    rewrite h; auto.

  - introv.
    unfold rename_inf_choice_seq_vals; rewrite h; auto.

  - introv.
    pose proof (h n) as h.
    unfold rename_inf_choice_seq_vals in *.
    unfold rename_choice_seq_val in *.
    rewrite <- (rename_cterm_idem r (vals n)).
    rewrite <- (rename_cterm_idem r (f n)).
    rewrite h; auto.

  - introv.
    unfold rename_inf_choice_seq_vals; rewrite h; auto.
Qed.
Hint Rewrite @rename_is_default_inf_choice_seq_entry_iff : slow.

Lemma is_cs_default_inf_entry_rename_iff {o} :
  forall r (entry : @inf_library_entry o),
    is_cs_default_inf_entry (rename_inf_library_entry r entry)
    <-> is_cs_default_inf_entry entry.
Proof.
  introv.
  unfold is_cs_default_inf_entry.
  destruct entry; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @is_cs_default_entry_rename_iff : slow.

Lemma implies_rename_inf_entry_in_inf_library_default {o} :
  forall r e (lib : @inf_library o),
    inf_entry_in_inf_library_default e lib
    -> inf_entry_in_inf_library_default (rename_inf_library_entry r e) (rename_inf_lib r lib).
Proof.
  introv h.
  unfold inf_entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.

  {
    introv q.
    destruct (h0 n).
    apply (implies_rename_matching_inf_entries r) in q.
    unfold rename_inf_lib in *; autorewrite with slow in *; auto.
  }

  { apply safe_inf_library_entry_rename; auto. }

  { apply is_cs_default_inf_entry_rename_iff; auto. }
Qed.
Hint Resolve implies_rename_inf_entry_in_inf_library_default : slow.

Lemma implies_entry_in_inf_library_rename {o} :
  forall r e (lib : @inf_library o),
    entry_in_inf_library e lib
    -> entry_in_inf_library (rename_inf_library_entry r e) (rename_inf_lib r lib).
Proof.
  introv h.
  unfold entry_in_inf_library in *; repndors; exrepnd;[left|right]; eauto 3 with slow.
Qed.
Hint Resolve implies_entry_in_inf_library_rename : slow.

Lemma rename_inf_lib_idem {o} :
  forall r (lib : @inf_library o),
    rename_inf_lib r (rename_inf_lib r lib) = lib.
Proof.
  introv.
  apply functional_extensionality; introv; simpl.
  unfold rename_inf_lib; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_inf_lib_idem : slow.

Lemma safe_inf_library_rename_iff {o} :
  forall r (lib : @inf_library o),
    safe_inf_library (rename_inf_lib r lib) <-> safe_inf_library lib.
Proof.
  introv; split; introv h i.

  - apply (implies_entry_in_inf_library_rename r) in i.
    apply h in i.
    apply safe_inf_library_entry_rename in i; auto.

  - apply (implies_entry_in_inf_library_rename r) in i.
    autorewrite with slow in *.
    apply h in i.
    apply safe_inf_library_entry_rename in i; auto.
Qed.
Hint Rewrite @safe_inf_library_rename_iff : slow.

Lemma implies_inf_lib_extends_rename {o} :
  forall r (infLib : @inf_library o) lib,
    inf_lib_extends infLib lib
    -> inf_lib_extends (rename_inf_lib r infLib) (rename_lib r lib).
Proof.
  introv h.
  destruct h as [ext safe].
  split; eauto 3 with slow;[].
  rewrite safe_library_rename_iff.
  rewrite safe_inf_library_rename_iff; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_rename : slow.

Definition bar_ren_lib2bar {o} r {lib} (b : @BarLib o (rename_lib r lib)) : BarLib lib.
Proof.
  exists (fun lib => bar_lib_bar b (rename_lib r lib)).

  - destruct b as [bar bars ext]; simpl in *.
    introv i.
    pose proof (bars (rename_inf_lib r infLib)) as bars.
    autodimp bars hyp; eauto 3 with slow;[].
    exrepnd.
    exists (rename_lib r lib'); autorewrite with slow; dands; auto.

    { apply (implies_lib_extends_rename_lib r) in bars2.
      autorewrite with slow in *; auto. }

    { apply (implies_inf_lib_extends_rename r) in bars0.
      autorewrite with slow in *; auto. }

  - destruct b as [bar bars ext]; simpl in *.
    introv i.
    pose proof (ext (rename_lib r lib') i) as ext.
    apply (implies_lib_extends_rename_lib r) in ext.
    autorewrite with slow in *; auto.
Defined.

Definition bar2bar_ren_lib {o} r {lib} (b : @BarLib o lib) : BarLib (rename_lib r lib).
Proof.
  exists (fun lib => bar_lib_bar b (rename_lib r lib)).

  - destruct b as [bar bars ext]; simpl in *.
    introv i.
    pose proof (bars (rename_inf_lib r infLib)) as bars.
    autodimp bars hyp; eauto 3 with slow.
    { apply (implies_inf_lib_extends_rename r) in i; autorewrite with slow in i; auto. }
    exrepnd.
    exists (rename_lib r lib'); autorewrite with slow; dands; auto.

    { apply (implies_lib_extends_rename_lib r) in bars2.
      autorewrite with slow in *; auto. }

    { apply (implies_inf_lib_extends_rename r) in bars0.
      autorewrite with slow in *; auto. }

  - destruct b as [bar bars ext]; simpl in *.
    introv i.
    pose proof (ext (rename_lib r lib') i) as ext.
    apply (implies_lib_extends_rename_lib r) in ext.
    autorewrite with slow in *; auto.
Defined.

Lemma all_in_ex_bar_rename_lib {o} :
  forall r (lib : @library o) G,
    all_in_ex_bar (rename_lib r lib) G
    <-> all_in_ex_bar lib (fun lib => G (rename_lib r lib)).
Proof.
  introv; split; intro h; unfold all_in_ex_bar in *; exrepnd.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    apply (h0 _ br _ ext).

  - exists (bar2bar_ren_lib r bar).
    introv br ext; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext) as h0; simpl in h0.
    autorewrite with slow in h0; auto.
Qed.

Lemma all_in_ex_bar_rename_lib2 {o} :
  forall r (lib : @library o) G,
    all_in_ex_bar (rename_lib r lib) G
    <=> all_in_ex_bar lib (fun lib => G (rename_lib r lib)).
Proof.
  introv; split; intro h; unfold all_in_ex_bar in *; exrepnd.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    apply (h0 _ br _ ext).

  - exists (bar2bar_ren_lib r bar).
    introv br ext; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext) as h0; simpl in h0.
    autorewrite with slow in h0; auto.
Qed.

Lemma equality_of_int_bar_as_all_in_ex_bar {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_int_bar lib t1 t2
    <-> all_in_ex_bar lib (fun lib => equality_of_int lib t1 t2).
Proof.
  tcsp.
Qed.

Lemma equality_of_int_bar_as_all_in_ex_bar2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_int_bar lib t1 t2
    <=> all_in_ex_bar lib (fun lib => equality_of_int lib t1 t2).
Proof.
  tcsp.
Qed.

Lemma equality_of_nat_bar_as_all_in_ex_bar2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat_bar lib t1 t2
    <=> all_in_ex_bar lib (fun lib => equality_of_nat lib t1 t2).
Proof.
  tcsp.
Qed.

Lemma equality_of_atom_bar_as_all_in_ex_bar2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_atom_bar lib t1 t2
    <=> all_in_ex_bar lib (fun lib => equality_of_atom lib t1 t2).
Proof.
  tcsp.
Qed.

Lemma equality_of_uatom_bar_as_all_in_ex_bar2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_uatom_bar lib t1 t2
    <=> all_in_ex_bar lib (fun lib => equality_of_uatom lib t1 t2).
Proof.
  tcsp.
Qed.

Lemma equality_of_csname_bar_as_all_in_ex_bar2 {o} :
  forall lib n (t1 t2 : @CTerm o),
    equality_of_csname_bar lib n t1 t2
    <=> all_in_ex_bar lib (fun lib => equality_of_csname lib n t1 t2).
Proof.
  tcsp.
Qed.

Lemma per_base_eq_as_all_in_ex_bar2 {o} :
  forall lib (t1 t2 : @CTerm o),
    per_base_eq lib t1 t2
    <=> all_in_ex_bar lib (fun lib => t1 ~=~(lib) t2).
Proof.
  tcsp.
Qed.

Lemma per_approx_eq_bar_as_all_in_ex_bar2 {o} :
  forall lib a b (t1 t2 : @CTerm o),
    per_approx_eq_bar lib a b t1 t2
    <=> all_in_ex_bar lib (fun lib => per_approx_eq lib a b t1 t2).
Proof.
  tcsp.
Qed.

Lemma per_cequiv_eq_bar_as_all_in_ex_bar2 {o} :
  forall lib a b (t1 t2 : @CTerm o),
    per_cequiv_eq_bar lib a b t1 t2
    <=> all_in_ex_bar lib (fun lib => per_cequiv_eq lib a b t1 t2).
Proof.
  tcsp.
Qed.

Lemma lib_extends_rename_r2l {o} :
  forall {r} {lib' lib : @library o},
    lib_extends lib' (rename_lib r lib)
    -> lib_extends (rename_lib r lib') lib.
Proof.
  introv h.
  apply (implies_lib_extends_rename_lib r) in h; autorewrite with slow in *; auto.
Qed.

Definition rename_lib_per {o} r {lib} (eqa : lib-per(lib,o)) : lib-per(rename_lib r lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' (rename_lib r lib)) => rename_per r (eqa (rename_lib r lib') (lib_extends_rename_r2l x)));[].
  repeat introv; simpl.
  unfold rename_per.
  apply eqa.
Defined.

Definition rename_cts {o} (r : renaming) (ts : cts(o)) : cts :=
  fun lib t1 t2 e => ts (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r e).

Lemma implies_eq_term_equals_rename_per {o} :
  forall r (e1 e2 : per(o)),
    (e1 <=2=> e2)
    -> (rename_per r e1) <=2=> (rename_per r e2).
Proof.
  introv h; introv; unfold rename_per; apply h.
Qed.

Lemma eq_term_equals_rename_per_per_bar_eq {o} :
  forall r {lib} (bar : @BarLib o lib) eqa,
    (rename_per r (per_bar_eq bar eqa))
    <=2=> (per_bar_eq (bar2bar_ren_lib r bar) (rename_lib_per r eqa)).
Proof.
  repeat introv; unfold rename_per.
  split; intro h.

  - unfold per_bar_eq in *.
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h _ br _ ext (lib_extends_rename_r2l x)) as h; simpl in h.
    exrepnd.
    exists (bar_ren_lib2bar r bar').

    introv br' ext'; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext'.
    pose proof (h0 _ br' _ ext' (implies_lib_extends_rename_lib r _ _ x0)) as h0; simpl in h0.
    unfold rename_per.
    eapply lib_per_cond; eauto.

  - unfold per_bar_eq in *.
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h (rename_lib r lib')) as h; simpl in h.
    autorewrite with slow in h; autodimp h hyp;[].
    pose proof (h _ ext (implies_lib_extends_rename_lib r _ _ x)) as h; simpl in h.
    exrepnd.
    exists (bar_ren_lib2bar r bar').

    introv br' ext'; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext'.
    pose proof (h0 _ br' _ ext' (implies_lib_extends_rename_lib r _ _ x0)) as h0; simpl in h0.
    revert h0; unfold rename_per in *.
    remember (lib_extends_rename_r2l
                (lib_extends_trans (implies_lib_extends_rename_lib r lib'2 lib'0 x0)
                                   (implies_lib_extends_rename_lib r lib'0 lib x))) as w; clear Heqw.
    revert w.
    autorewrite with slow; introv h.
    eapply lib_per_cond; eauto.
Qed.

Lemma rename_eq_per_eq_bar {o} :
  forall r lib (a1 a2 : @CTerm o) eqa t1 t2,
    (eq_per_eq_bar lib a1 a2 eqa t1 t2)
      <=>
      eq_per_eq_bar
      (rename_lib r lib)
      (rename_cterm r a1)
      (rename_cterm r a2)
      (rename_lib_per r eqa)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold eq_per_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    unfold eq_per_eq in *; repnd; spcast.
    apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto.
    apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto.
    dands; spcast; auto.
    unfold rename_per; autorewrite with slow; auto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    unfold eq_per_eq in *; repnd; spcast.
    apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto.
    apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto.
    dands; spcast; auto.
    revert h0; unfold rename_per.
    remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as e; clear Heqe.
    revert e; autorewrite with slow in *; introv w.
    eapply lib_per_cond; eauto.
Qed.

Definition rename_lib_per_fam {o} r {lib} {eqa : lib-per(lib,o)} (eqb : lib-per-fam(lib,eqa,o)) : lib-per-fam(rename_lib r lib,rename_lib_per r eqa, o).
Proof.
  exists (fun lib' (x : lib_extends lib' (rename_lib r lib))
              a a' (p : rename_lib_per r eqa lib' x a a') =>
            rename_per r (eqb
                            (rename_lib r lib')
                            (lib_extends_rename_r2l x)
                            (rename_cterm r a)
                            (rename_cterm r a')
                            p));[].
  repeat introv; simpl.
  unfold rename_per.
  apply eqb.
Defined.

Lemma rename_per_func_ext_eq {o} :
  forall r lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    (per_func_ext_eq lib eqa eqb t1 t2)
      <=>
      per_func_ext_eq
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_lib_per_fam r eqb)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_func_ext_eq in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    introv; simpl.
    unfold rename_per in *; simpl in *.
    pose proof (h0 _ _ e) as h0.
    autorewrite with slow; auto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    introv; simpl.
    unfold rename_per in *; simpl in *.
    pose proof (h0 (rename_cterm r a) (rename_cterm r a')) as h0; simpl in h0.
    remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as w; clear Heqw.
    revert w h0.
    autorewrite with slow; introv h0.
    dup e as z.
    eapply (lib_per_cond _ eqa) in z.
    pose proof (h0 z) as h0.
    eapply eqb; eauto.
Qed.

Lemma rename_per_union_eq_bar {o} :
  forall r lib (eqa eqb : lib-per(lib,o)) t1 t2,
    (per_union_eq_bar lib eqa eqb t1 t2)
      <=>
      per_union_eq_bar
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_lib_per r eqb)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_union_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *;
      repndors; exrepnd; spcast;[left|right];
        apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto;
          apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto;
            eexists; eexists; dands; spcast; eauto;
              unfold rename_per; autorewrite with slow; auto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *;
      repndors; exrepnd; spcast;[left|right];
        apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto;
          apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto;
            eexists; eexists; dands; spcast; eauto;
              revert h0; unfold rename_per;
                remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as e; clear Heqe;
                  revert e; autorewrite with slow in *; introv w;
                    eapply lib_per_cond; eauto.
Qed.

Lemma rename_per_image_eq_bar {o} :
  forall r lib (f : @CTerm o) eqa t1 t2,
    (per_image_eq_bar lib eqa f t1 t2)
      <=>
      per_image_eq_bar
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_cterm r f)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_image_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    rewrite <- (rename_lib_idem r lib'0) at 1.
    apply rename_per_image_eq; auto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    apply (rename_per_image_eq r); auto.

    eapply implies_eq_term_equals_eq_image_eq;[|eauto]; clear h0.
    introv; unfold rename_per.
    remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as z; clear Heqz.
    revert z; autorewrite with slow; introv; apply eqa.
Qed.

Lemma rename_per_set_eq_bar {o} :
  forall r lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    (per_set_eq_bar lib eqa eqb t1 t2)
      <=>
      per_set_eq_bar
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_lib_per_fam r eqb)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_set_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    unfold per_set_eq in *; exrepnd.

    assert (rename_per
              r
              (eqa (rename_lib r lib'0) (lib_extends_rename_r2l x))
              (rename_cterm r t1)
              (rename_cterm r t2)) as z.
    { unfold rename_per; autorewrite with slow; auto. }
    exists z.
    unfold inhabited in *; exrepnd.
    exists (rename_cterm r t).
    unfold rename_per.
    revert z; unfold rename_per; simpl.
    autorewrite with slow; introv.
    eapply eqb; eauto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    unfold per_set_eq in *; exrepnd.

    assert (eqa lib'0 x t1 t2) as z.
    { clear h1; revert e.
      remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as z; clear Heqz.
      revert z.
      unfold rename_per; autorewrite with slow; auto.
      introv w; eapply eqa; eauto. }
    exists z.
    unfold inhabited in *; exrepnd.
    exists (rename_cterm r t).
    revert h0.
    remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as w; clear Heqw.
    revert w e.
    unfold rename_per.
    autorewrite with slow; introv.
    eapply eqb; eauto.
Qed.

Lemma rename_per_product_eq_bar {o} :
  forall r lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    (per_product_eq_bar lib eqa eqb t1 t2)
      <=>
      per_product_eq_bar
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_lib_per_fam r eqb)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_product_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x)) as h0; simpl in h0.
    unfold per_product_eq in *; exrepnd.

    exists (rename_cterm r a) (rename_cterm r a') (rename_cterm r b) (rename_cterm r b').

    assert (rename_per
              r
              (eqa (rename_lib r lib'0) (lib_extends_rename_r2l x))
              (rename_cterm r a)
              (rename_cterm r a')) as z.
    { unfold rename_per; autorewrite with slow; auto. }
    exists z.

    spcast.
    apply (computes_to_valc_rename r) in h0.
    apply (computes_to_valc_rename r) in h2.
    autorewrite with rename slow in *.
    dands; spcast; auto.

    unfold rename_per.
    revert z; unfold rename_per; simpl.
    autorewrite with slow; introv.
    eapply eqb; eauto.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x)) as h0; simpl in h0.
    unfold per_product_eq in *; exrepnd.
    GC.

    spcast.
    apply (computes_to_valc_rename r) in h0.
    apply (computes_to_valc_rename r) in h2.
    autorewrite with rename slow in *.

    exists (rename_cterm r a) (rename_cterm r a') (rename_cterm r b) (rename_cterm r b').

    assert (eqa lib'0 x (rename_cterm r a) (rename_cterm r a')) as z.
    { clear h1; revert e.
      remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as z; clear Heqz.
      revert z.
      unfold rename_per; autorewrite with slow; auto.
      introv w; eapply eqa; eauto. }

    exists z.
    dands; spcast; auto.

    remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x)) as w; clear Heqw.
    revert w e h1; unfold rename_per; simpl.
    autorewrite with slow; introv q.
    eapply eqb; eauto.
Qed.

Lemma rename_cterm_ffdefs {o} :
  forall r (a b : @CTerm o),
    rename_cterm r (mkc_free_from_defs a b)
    = mkc_free_from_defs (rename_cterm r a) (rename_cterm r b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @rename_cterm_ffdefs : rename.

Definition rename_def_kind (r : renaming) (d : def_kind) : def_kind :=
  match d with
  | defk_abs abs => defk_abs (rename_opabs r abs)
  | defk_cs cs => defk_cs cs
  end.

Lemma get_defs_o_rename_op {o} :
  forall r (op : @Opid o),
    get_defs_o (rename_op r op)
    = map (rename_def_kind r) (get_defs_o op).
Proof.
  introv.
  destruct op; simpl; tcsp.
  destruct c; simpl; tcsp.
Qed.

Lemma get_defs_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    get_defs (rename_term r t)
    = map (rename_def_kind r) (get_defs t).
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto; autorewrite with slow list;
    try rewrite get_defs_o_rename_op; auto.
  rewrite map_app.
  f_equal.
  autodimp IHbs hyp.
  { introv i; eapply ind; simpl; eauto. }
  rewrite map_app in *.
  rewrite get_defs_o_rename_op in IHbs.
  apply app_inv_head in IHbs.
  rewrite IHbs; f_equal.
  destruct a; simpl.
  erewrite ind; simpl; eauto.
Defined.

Lemma implies_nodefsc_rename_cterm {o} :
  forall r (t : @CTerm o),
    nodefsc t
    -> nodefsc (rename_cterm r t).
Proof.
  introv nodf.
  destruct_cterms; unfold nodefsc in *; simpl in *.
  unfold nodefs.
  rewrite get_defs_rename_term.
  rewrite nodf; simpl; auto.
Qed.
Hint Resolve implies_nodefsc_rename_cterm : slow.

Lemma rename_per_ffdefs_eq_bar {o} :
  forall r lib (eqa : lib-per(lib,o)) x t1 t2,
    (per_ffdefs_eq_bar lib eqa x t1 t2)
      <=>
      per_ffdefs_eq_bar
      (rename_lib r lib)
      (rename_lib_per r eqa)
      (rename_cterm r x)
      (rename_cterm r t1)
      (rename_cterm r t2).
Proof.
  introv; split; introv h; unfold per_ffdefs_eq_bar in *; exrepnd.

  - exists (bar2bar_ren_lib r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (lib_extends_rename_r2l x0)) as h0; simpl in h0.
    unfold per_ffdefs_eq in *;
      repndors; exrepnd; spcast;
        apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto;
          apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto;
            eexists; eexists; dands; spcast; eauto;
    unfold ex_nodefsc in *; exrepnd.
    exists (rename_cterm r u); dands; autorewrite with slow; eauto 3 with slow.

  - exists (bar_ren_lib2bar r bar).
    introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (h0 _ br _ ext (implies_lib_extends_rename_lib r _ _ x0)) as h0; simpl in h0.
    unfold per_ffdefs_eq in *;
      repndors; exrepnd; spcast;
        apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto;
          apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; auto;
            eexists; eexists; dands; spcast; eauto.
    unfold ex_nodefsc in *; exrepnd.
    exists (rename_cterm r u); dands; autorewrite with slow; eauto 3 with slow.
    revert h0; unfold rename_per;
      remember (lib_extends_rename_r2l (implies_lib_extends_rename_lib r lib'0 lib x0)) as e; clear Heqe;
        revert e; autorewrite with slow in *; introv w;
          eapply lib_per_cond; eauto.
Qed.

Lemma implies_close_rename {o} :
  forall r (u : cts(o)) (lib : library) (t1 t2 : @CTerm o) e,
    (forall lib t1 t2 e,
        u lib t1 t2 e
        -> u (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r e))
    -> close u lib t1 t2 e
    -> close
         u
         (rename_lib r lib)
         (rename_cterm r t1)
         (rename_cterm r t2)
         (rename_per r e).
Proof.
  introv imp cl.
  close_cases (induction cl using @close_ind') Case; subst.

  - Case "CL_init".
    apply CL_init.
    apply imp; auto.

  - Case "CL_bar".
    apply CL_bar.
    unfold per_bar.
    exists (bar2bar_ren_lib r bar) (rename_lib_per r eqa).
    dands.

    + introv br ext; introv; simpl in *.
      apply (implies_lib_extends_rename_lib r) in ext.
      pose proof (reca _ br _ ext (lib_extends_rename_r2l x)) as reca; simpl in reca.
      autorewrite with slow in *.
      apply reca; tcsp.

    + eapply eq_term_equals_trans;
        [apply implies_eq_term_equals_rename_per;eauto|].
      apply eq_term_equals_rename_per_per_bar_eq.

  - Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    repeat (rw @equality_of_int_bar_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.

    unfold equality_of_int; split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists k; dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists k; dands; spcast; auto.

  - Case "CL_nat".
    apply CL_nat.
    unfold per_nat in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    repeat (rw @equality_of_nat_bar_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.

    unfold equality_of_nat; split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists n; dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists n; dands; spcast; auto.

  - Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; exrepnd; spcast.
    apply (computes_to_valc_rename r) in per2.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    exists n; dands; spcast; auto;[].
    unfold rename_per; introv; rw per0.
    repeat (rw @equality_of_csname_bar_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.

    unfold equality_of_csname; split; introv h; exrepnd; spcast;
      exists name.

    + apply (computes_to_valc_rename r) in h2.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h2.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      dands; spcast; auto.

  - Case "CL_atom".
    apply CL_atom.
    unfold per_atom in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    repeat (rw @equality_of_atom_bar_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.
    unfold equality_of_atom; split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists s; dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists s; dands; spcast; auto.

  - Case "CL_uatom".
    apply CL_uatom.
    unfold per_uatom in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    repeat (rw @equality_of_uatom_bar_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.
    unfold equality_of_uatom; split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      eexists; dands; spcast; eauto.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      eexists; dands; spcast; eauto.

  - Case "CL_base".
    apply CL_base.
    unfold per_base in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    repeat (rw @per_base_eq_as_all_in_ex_bar2).
    rw @all_in_ex_bar_rename_lib2.
    apply implies_iff_all_in_ex_bar.
    introv ext.
    split; introv h; exrepnd; spcast;
      apply (implies_cequivc_rename r) in h; autorewrite with slow in *; auto.

  - Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per2.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists; dands; spcast; eauto.

    + introv ext.
      apply lib_extends_rename_r2l in ext.
      pose proof (per3 _ ext) as per3; simpl in *.
      split; intro h;
        apply (implies_capproxc_rename r) in h; autorewrite with slow in *;
          apply per3 in h; apply (implies_capproxc_rename r) in h; auto;
            autorewrite with slow in *; auto.

    + introv; unfold rename_per; simpl.
      rw per1; clear per1.
      repeat (rw @per_approx_eq_bar_as_all_in_ex_bar2).
      rw @all_in_ex_bar_rename_lib2.
      apply implies_iff_all_in_ex_bar.
      introv ext.
      unfold per_approx_eq; split; introv h; exrepnd; spcast.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto; eauto 3 with slow.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto; eauto 3 with slow.
        apply (implies_approxc_rename r) in h; autorewrite with slow in *; auto.

  - Case "CL_cequiv".
    apply CL_cequiv.
    unfold per_cequiv in *; exrepnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per2.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists; dands; spcast; eauto.

    + introv ext.
      apply lib_extends_rename_r2l in ext.
      pose proof (per3 _ ext) as per3; simpl in *.
      split; intro h;
        apply (implies_ccequivc_rename r) in h; autorewrite with slow in *;
          apply per3 in h; apply (implies_ccequivc_rename r) in h; auto;
            autorewrite with slow in *; auto.

    + introv; unfold rename_per; simpl.
      rw per1; clear per1.
      repeat (rw @per_cequiv_eq_bar_as_all_in_ex_bar2).
      rw @all_in_ex_bar_rename_lib2.
      apply implies_iff_all_in_ex_bar.
      introv ext.
      unfold per_cequiv_eq; split; introv h; exrepnd; spcast.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto; eauto 3 with slow.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto; eauto 3 with slow.
        apply (implies_cequivc_rename r) in h; autorewrite with slow in *; auto.

  - Case "CL_eq".
    repeat (autodimp IHcl hyp).
    apply CL_eq.
    spcast.
    unfold per_eq.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (rename_lib_per r eqa).
    dands; spcast; eauto;[| | |].

    + introv.
      pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *; auto.

    + introv.
      pose proof (eos1 _ (lib_extends_rename_r2l e)) as eos1; simpl in eos1.
      destruct eos1 as [eos1|eos1];[left|right]; spcast; eauto 3 with slow.

      * unfold rename_lib_per, rename_per; simpl; autorewrite with slow; auto.

      * apply (implies_ccequivc_ext_rename r) in eos1; autorewrite with slow in *; auto.

    + introv.
      pose proof (eos2 _ (lib_extends_rename_r2l e)) as eos2; simpl in eos2.
      destruct eos2 as [eos2|eos2];[left|right]; spcast; eauto 3 with slow.

      * unfold rename_lib_per, rename_per; simpl; autorewrite with slow; auto.

      * apply (implies_ccequivc_ext_rename r) in eos2; autorewrite with slow in *; auto.

    + introv; unfold rename_per.
      rw eqiff; autorewrite with slow; tcsp.
      eapply tiff_trans; [apply (rename_eq_per_eq_bar r)|].
      autorewrite with slow; tcsp.

(*  - Case "CL_req".
    repeat (autodimp IHcl hyp).
    apply CL_req.
    spcast.
    unfold per_req.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto;[| |].

    + destruct eo1 as [eos1|eos1];[left|right]; spcast; eauto 3 with slow.

    + destruct eo2 as [eos2|eos2];[left|right]; spcast; eauto 3 with slow.

    + introv; unfold rename_per.
      rw eqiff; autorewrite with slow; tcsp.
      unfold per_req_eq; split; introv h; exrepnd; eexists; eexists; dands; tcsp; spcast;
        try (complete (apply (computes_to_valc_rename r) in h0; autorewrite with slow in *; eauto));
        try (complete (apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; eauto));
        try (complete (apply (computes_to_valc_rename r) in h2; autorewrite with slow in *; eauto)).

  - Case "CL_teq".
    repeat (autodimp IHcl hyp).
    apply CL_teq.
    spcast.
    unfold per_teq.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autodimp IHcl1 hyp.
    autodimp IHcl2 hyp.
    autodimp IHcl3 hyp.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto.

    introv; unfold rename_per.
    rw eqiff; autorewrite with slow; tcsp.

  - Case "CL_isect".
    apply CL_isect.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_per r eqa) (rename_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.
      introv.

      dup e as q.
      apply rename_per_iff in q.
      unfold rename_per1 in q; exrepnd; subst.
      revert e; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
      pose proof (recb a'0 b' e) as q; repeat (autodimp q hyp).
      unfold rename_per in q; auto.
      autorewrite with rename in *; auto.

    + introv.
      split; introv h.

      * introv.
        dup e as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert e; unfold rename_per_fam, rename_per in *; autorewrite with slow; introv.
        rw eqiff in h; apply h.

      * unfold rename_per.
        apply eqiff.
        introv.
        pose proof (h (rename_cterm r a) (rename_cterm r a')) as q.
        revert q; unfold rename_per_fam, rename_per; autorewrite with slow.
        introv; tcsp.*)

  - Case "CL_func".
    apply CL_func.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_lib_per r eqa) (rename_lib_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

      {
        introv.
        pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
        repeat (autodimp reca hyp);[].
        autorewrite with slow in *; auto.
      }

      {
        introv; simpl.
        unfold rename_lib_per in e0; simpl in e0.
        unfold rename_per in e0; simpl in e0.
        pose proof (recb _ (lib_extends_rename_r2l e) (rename_cterm r a) (rename_cterm r a') e0) as recb; simpl in recb.
        repeat (autodimp recb hyp);[].
        autorewrite with rename slow in *; auto.
      }

    + introv.
      unfold rename_per; simpl.
      rw eqiff.
      eapply tiff_trans; [apply (rename_per_func_ext_eq r)|].
      autorewrite with slow; tcsp.

(*  - Case "CL_disect".
    apply CL_disect.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_per r eqa) (rename_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.
      introv.

      dup e as q.
      apply rename_per_iff in q.
      unfold rename_per1 in q; exrepnd; subst.
      revert e; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
      pose proof (recb a'0 b' e) as q; repeat (autodimp q hyp).
      unfold rename_per in q; auto.
      autorewrite with rename in *; auto.

    + introv.
      split; introv h.

      * unfold rename_per in h.
        apply eqiff in h; exrepnd.
        unfold rename_per_fam, rename_per; simpl.
        eexists; eauto.

      * exrepnd.
        unfold rename_per.
        apply eqiff.
        eexists; eauto.

  - Case "CL_pertype".
    repeat (autodimp IHcl hyp).
    apply CL_pertype.
    spcast.
    unfold per_pertype.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.
    eexists; eexists.

    exists (rename_fper r eq1) (rename_fper r eq2).
    dands; spcast; eauto; eauto 3 with slow.

    + introv.
      pose proof (rec1 (rename_cterm r x) (rename_cterm r y)) as q; autodimp q hyp.
      autorewrite with slow in *; auto.

    + introv.
      pose proof (rec2 (rename_cterm r x) (rename_cterm r y)) as q; autodimp q hyp.
      autorewrite with slow in *; auto.

    + introv; repeat (rw @inhabited_rename_fper); tcsp.

    + introv; unfold rename_per.
      rw @inhabited_rename_fper.
      rw eqiff; tcsp.

  - Case "CL_ipertype".
    repeat (autodimp IHcl hyp).
    apply CL_ipertype.
    spcast.
    unfold per_ipertype.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.
    eexists; eexists.

    exists (rename_fper r eq1).
    dands; spcast; eauto; eauto 3 with slow.

    + introv.
      pose proof (rec1 (rename_cterm r x) (rename_cterm r y)) as q; autodimp q hyp.
      autorewrite with slow in *; auto.

    + introv; unfold rename_per.
      rw @inhabited_rename_fper.
      rw eqiff; tcsp.

  - Case "CL_spertype".
    repeat (autodimp IHcl hyp).
    apply CL_spertype.
    spcast.
    unfold per_spertype.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.
    eexists; eexists.

    exists (rename_fper r eq1).
    dands; spcast; eauto; eauto 3 with slow.

    + introv.
      pose proof (rec1 (rename_cterm r x) (rename_cterm r y)) as q; autodimp q hyp.
      autorewrite with slow in *; auto.

    + introv inh.
      apply inhabited_rename_fper in inh.
      apply (rec2 _ (rename_cterm r y)) in inh; auto.
      autorewrite with slow in *; auto.

    + introv inh.
      apply inhabited_rename_fper in inh.
      apply (rec3 (rename_cterm r x)) in inh; auto.
      autorewrite with slow in *; auto.

    + introv; unfold rename_per.
      rw @inhabited_rename_fper.
      rw eqiff; tcsp.

  - Case "CL_w".
    apply CL_w.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_per r eqa) (rename_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.
      introv.

      dup e as q.
      apply rename_per_iff in q.
      unfold rename_per1 in q; exrepnd; subst.
      revert e; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
      pose proof (recb a'0 b' e) as q; repeat (autodimp q hyp).
      unfold rename_per in q; auto.
      autorewrite with rename in *; auto.

    + introv.
      split; introv h.

      * unfold rename_per in h.
        apply eqiff in h; exrepnd.
        apply (implies_weq_rename r) in h; autorewrite with slow in *; auto.

      * unfold rename_per.
        apply eqiff.
        apply (weq_rename_implies r); autorewrite with slow; auto.

  - Case "CL_m".
    apply CL_m.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_per r eqa) (rename_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.
      introv.

      dup e as q.
      apply rename_per_iff in q.
      unfold rename_per1 in q; exrepnd; subst.
      revert e; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
      pose proof (recb a'0 b' e) as q; repeat (autodimp q hyp).
      unfold rename_per in q; auto.
      autorewrite with rename in *; auto.

    + introv.
      split; introv h.

      * unfold rename_per in h.
        apply eqiff in h; exrepnd.
        apply (implies_meq_rename r) in h; autorewrite with slow in *; auto.

      * unfold rename_per.
        apply eqiff.
        apply (meq_rename_implies r); autorewrite with slow; auto.

  - Case "CL_pw".
    apply CL_pw.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.

    repeat (autodimp IHcl hyp).

    exists (rename_per r eqp) (rename_per_fam r eqa) (rename_per_fam_fam r eqb).
    exists (rename_cterm r p) (rename_cterm r p') cp cp' ca ca' cb cb'.
    exists (rename_cvterm r C) (rename_cvterm r C').
    dands;[|].

    + unfold type_pfamily.
      eexists; eexists; eexists; eexists; eexists; eexists.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; spcast; eauto;[| | |].

      * introv.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
        pose proof (reca a' b' ep) as q; repeat (autodimp q hyp).
        unfold rename_per in q; auto.
        autorewrite with rename in *; auto.

      * introv.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep ea; unfold rename_per_fam_fam, rename_per_fam, rename_per; autorewrite with slow; introv.

        pose proof (recb a' b' ep (rename_cterm r a1) (rename_cterm r a2) ea) as q; repeat (autodimp q hyp).
        unfold rename_per in q; auto.
        autorewrite with rename slow in *; auto.

      * introv eb.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep ea eb; unfold rename_per_fam_fam, rename_per_fam, rename_per; autorewrite with slow rename; introv eb.
        eapply eqc; eauto.

      * unfold rename_per; autorewrite with slow; auto.

    + introv.
      split; introv h;[|].

      * unfold rename_per in h.
        apply eqiff in h; exrepnd.
        apply (implies_pweq_rename r) in h; autorewrite with slow in *; auto.

      * unfold rename_per.
        apply eqiff.
        apply (pweq_rename_implies r); autorewrite with slow; auto.

  - Case "CL_pm".
    apply CL_pm.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.

    repeat (autodimp IHcl hyp).

    exists (rename_per r eqp) (rename_per_fam r eqa) (rename_per_fam_fam r eqb).
    exists (rename_cterm r p) (rename_cterm r p') cp cp' ca ca' cb cb'.
    exists (rename_cvterm r C) (rename_cvterm r C').
    dands;[|].

    + unfold type_pfamily.
      eexists; eexists; eexists; eexists; eexists; eexists.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; spcast; eauto;[| | |].

      * introv.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
        pose proof (reca a' b' ep) as q; repeat (autodimp q hyp).
        unfold rename_per in q; auto.
        autorewrite with rename in *; auto.

      * introv.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep ea; unfold rename_per_fam_fam, rename_per_fam, rename_per; autorewrite with slow; introv.

        pose proof (recb a' b' ep (rename_cterm r a1) (rename_cterm r a2) ea) as q; repeat (autodimp q hyp).
        unfold rename_per in q; auto.
        autorewrite with rename slow in *; auto.

      * introv eb.
        dup ep as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        revert ep ea eb; unfold rename_per_fam_fam, rename_per_fam, rename_per; autorewrite with slow rename; introv eb.
        eapply eqc; eauto.

      * unfold rename_per; autorewrite with slow; auto.

    + introv.
      split; introv h;[|].

      * unfold rename_per in h.
        apply eqiff in h; exrepnd.
        apply (implies_pmeq_rename r) in h; autorewrite with slow in *; auto.

      * unfold rename_per.
        apply eqiff.
        apply (pmeq_rename_implies r); autorewrite with slow; auto.

  - Case "CL_texc".
    repeat (autodimp IHcl1 hyp).
    repeat (autodimp IHcl2 hyp).
    apply CL_texc.
    spcast.
    unfold per_texc.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    exists (rename_per r eqn) (rename_per r eqe).
    eexists; eexists; eexists; eexists.
    dands; spcast; eauto; eauto 3 with slow.

    introv; unfold rename_per.
    rw eqiff; tcsp.
    unfold per_texc_eq.
    split; introv h; exrepnd; spcast.

    * apply (rename_computes_to_excc r) in h0.
      apply (rename_computes_to_excc r) in h2.
      autorewrite with slow in *.
      eexists; eexists; eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

    * apply (rename_computes_to_excc r) in h0.
      apply (rename_computes_to_excc r) in h2.
      autorewrite with slow in *.
      eexists; eexists; eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.*)

  - Case "CL_union".
    repeat (autodimp IHcl1 hyp).
    repeat (autodimp IHcl2 hyp).
    apply CL_union.
    spcast.
    unfold per_union.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    exists (rename_lib_per r eqa) (rename_lib_per r eqb).
    eexists; eexists; eexists; eexists.
    dands; spcast; eauto; eauto 3 with slow.

    {
      introv.
      pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *; auto.
    }

    {
      introv.
      pose proof (recb _ (lib_extends_rename_r2l e)) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *; auto.
    }

    introv; unfold rename_per.
    rw eqiff; tcsp.
    eapply tiff_trans; [apply (rename_per_union_eq_bar r)|].
    autorewrite with slow; tcsp.

  - Case "CL_image".
    repeat (autodimp IHcl hyp).
    apply CL_image.
    spcast.
    unfold per_image.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    exists (rename_lib_per r eqa).
    eexists; eexists; eexists; eexists.
    dands; spcast; eauto; eauto 3 with slow.

    {
      introv.
      pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *; auto.
    }

    introv; rw eqiff; tcsp.
    eapply tiff_trans; [apply (rename_per_image_eq_bar r)|].
    autorewrite with slow; tcsp.

(*  - Case "CL_partial".
    repeat (autodimp IHcl hyp).
    apply CL_partial.
    spcast.
    unfold per_partial.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto; eauto 3 with slow.

    + introv h.
      unfold rename_per in h.
      apply hv in h; spcast.
      apply (implies_rename_hasvaluec r) in h; autorewrite with slow in *; auto.

    + introv; unfold rename_per at 1; simpl.
      rw eqiff.
      unfold per_partial_eq.

      repeat (rw (chaltsc_rename_iff r lib)); autorewrite with slow.
      unfold rename_per; tcsp.

  - Case "CL_admiss".
    repeat (autodimp IHcl hyp).
    apply CL_admiss.
    spcast.
    unfold per_admiss.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto; eauto 3 with slow.

    introv; unfold rename_per at 1; simpl.
    rw eqiff.
    unfold per_admiss_eq.

    rw @admissible_equality_rename.
    split; introv h; repnd; spcast; auto.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.

  - Case "CL_mono".
    repeat (autodimp IHcl hyp).
    apply CL_mono.
    spcast.
    unfold per_mono.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto; eauto 3 with slow.

    introv; unfold rename_per at 1; simpl.
    rw eqiff.
    unfold per_mono_eq.
    rw @mono_equality_rename.
    split; introv h; repnd; spcast; auto.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.

  - Case "CL_ffatom".
    repeat (autodimp IHcl hyp).
    apply CL_ffatom.
    spcast.
    unfold per_ffatom.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    apply (computes_to_valc_rename r) in ca1.
    apply (computes_to_valc_rename r) in ca2.
    autorewrite with slow in *.

    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (rename_per r eqa); eexists.
    dands; spcast; eauto; eauto 3 with slow.

    introv; unfold rename_per at 1; simpl.
    rw eqiff.
    unfold per_ffatom_eq.

    split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.
      exists (rename_cterm r y); dands; autorewrite with slow; eauto 3 with slow.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.
      unfold rename_per in *; autorewrite with slow in *.
      exists (rename_cterm r y); dands; autorewrite with slow; eauto 3 with slow.

  - Case "CL_effatom".
    repeat (autodimp IHcl hyp).
    apply CL_effatom.
    spcast.
    unfold per_effatom.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto; eauto 3 with slow; tcsp.

    + repeat (rw @rename_name_not_in_upto); auto.

    + introv; unfold rename_per at 1; simpl.
      rw eqiff.
      unfold per_effatom_eq.

      split; introv h; exrepnd; spcast.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto.
        repeat (rw @rename_name_not_in_upto); auto.

      * apply (computes_to_valc_rename r) in h0.
        apply (computes_to_valc_rename r) in h1.
        autorewrite with slow in *.
        dands; spcast; auto.
        repeat (rw @rename_name_not_in_upto in h); auto.

  - Case "CL_ffatoms".
    repeat (autodimp IHcl hyp).
    apply CL_ffatoms.
    spcast.
    unfold per_ffatoms.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    eexists; eexists; eexists; eexists.
    exists (rename_per r eqa).
    dands; spcast; eauto; eauto 3 with slow; tcsp.

    introv; unfold rename_per at 1; simpl.
    rw eqiff.
    unfold per_ffatoms_eq.

    split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.
      exists (rename_cterm r y); dands; eauto 3 with slow.

    + apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h1.
      autorewrite with slow in *.
      dands; spcast; auto.
      unfold rename_per in *; simpl in *; autorewrite with slow in *.
      exists (rename_cterm r y); dands; eauto 3 with slow.*)

  - Case "CL_ffdefs".
    repeat (autodimp IHcl hyp).
    apply CL_ffdefs.
    spcast.
    unfold per_ffdefs.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists.
    exists (rename_lib_per r eqa).
    dands; spcast; eauto; eauto 3 with slow; tcsp.

    { introv.
      pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
      repeat (autodimp reca hyp);[].
      autorewrite with slow in *; auto. }

    { introv; simpl.
      unfold rename_per.
      autorewrite with slow; eauto. }

    introv; unfold rename_per at 1; simpl.
    rw eqiff.
    eapply tiff_trans; [apply (rename_per_ffdefs_eq_bar r)|].
    autorewrite with slow; tcsp.

  - Case "CL_set".
    apply CL_set.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_lib_per r eqa) (rename_lib_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

      {
        introv.
        pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
        repeat (autodimp reca hyp);[].
        autorewrite with slow in *; auto.
      }

      {
        introv; simpl.
        unfold rename_lib_per in e0; simpl in e0.
        unfold rename_per in e0; simpl in e0.
        pose proof (recb _ (lib_extends_rename_r2l e) (rename_cterm r a) (rename_cterm r a') e0) as recb; simpl in recb.
        repeat (autodimp recb hyp);[].
        autorewrite with rename slow in *; auto.
      }

    + introv.
      unfold rename_per; simpl.
      rw eqiff.
      eapply tiff_trans; [apply (rename_per_set_eq_bar r)|].
      autorewrite with slow; tcsp.

(*  - Case "CL_tunion".
    apply CL_tunion.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_per r eqa) (rename_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.
      introv.

      dup e as q.
      apply rename_per_iff in q.
      unfold rename_per1 in q; exrepnd; subst.
      revert e; unfold rename_per_fam, rename_per; autorewrite with slow; introv.
      pose proof (recb a'0 b' e) as q; repeat (autodimp q hyp).
      unfold rename_per in q; auto.
      autorewrite with rename in *; auto.

    + introv.
      unfold rename_per at 1.
      rw eqiff.

      split; intro h.

      * apply (implies_rename_per_tunion_eq r) in h.
        autorewrite with slow in *; auto.

      * apply (rename_per_tunion_eq_implies r).
        autorewrite with slow in *; auto.*)

  - Case "CL_product".
    apply CL_product.
    spcast.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow rename in *.
    repeat (autodimp IHcl hyp).

    exists (rename_lib_per r eqa) (rename_lib_per_fam r eqb).
    dands.

    + unfold type_family.
      eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

      {
        introv.
        pose proof (reca _ (lib_extends_rename_r2l e)) as reca; simpl in reca.
        repeat (autodimp reca hyp);[].
        autorewrite with slow in *; auto.
      }

      {
        introv; simpl.
        unfold rename_lib_per in e0; simpl in e0.
        unfold rename_per in e0; simpl in e0.
        pose proof (recb _ (lib_extends_rename_r2l e) (rename_cterm r a) (rename_cterm r a') e0) as recb; simpl in recb.
        repeat (autodimp recb hyp);[].
        autorewrite with rename slow in *; auto.
      }

    + introv.
      unfold rename_per; simpl.
      rw eqiff.
      eapply tiff_trans; [apply (rename_per_product_eq_bar r)|].
      autorewrite with slow; tcsp.
Qed.

Lemma implies_univi_bar_rename {o} :
  forall i lib r (t1 t2 : @CTerm o) e,
    (forall lib r t1 t2 (eq : per(o)),
        univi i lib t1 t2 eq
        -> univi i (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq))
    -> univi_bar i lib t1 t2 e
    -> univi_bar i (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r e).
Proof.
  introv imp u.
  unfold univi_bar in *.
  unfold per_bar in *; exrepnd.
  exists (bar2bar_ren_lib r bar) (rename_lib_per r eqa).
  dands.

  + introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (u0 _ br _ ext (lib_extends_rename_r2l x)) as u0; simpl in u0.
    apply (imp _ r) in u0; revert u0.
    autorewrite with slow in *; tcsp.

  + eapply eq_term_equals_trans;
      [apply implies_eq_term_equals_rename_per;eauto|].
    apply eq_term_equals_rename_per_per_bar_eq.
Qed.

Lemma implies_univi_rename {o} :
  forall i lib r (t1 t2 : @CTerm o) eq,
    univi i lib t1 t2 eq
    -> univi i (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv u; simpl in *.
  allrw @univi_exists_iff.
  exrepnd; spcast.

  exists j.
  dands; auto; spcast.

  - apply (computes_to_valc_rename r) in u2; autorewrite with slow in *; auto.

  - apply (computes_to_valc_rename r) in u3; autorewrite with slow in *; auto.

  - introv; simpl.
    clear u2 u3.
    unfold rename_per.
    rw u0; clear u0.
    unfold univi_eq; split; introv h; exrepnd.

    + pose proof (implies_close_rename r (univi_bar j) lib (rename_cterm r t0) (rename_cterm r t3) eqa) as q.
      simpl in q; autorewrite with slow in q.
      repeat (autodimp q hyp); try (complete (eexists; eauto)).
      introv h; eapply implies_univi_bar_rename; eauto.

    + pose proof (implies_close_rename r (univi_bar j) (rename_lib r lib) t0 t3 eqa) as q.
      simpl in q; autorewrite with slow in q.
      repeat (autodimp q hyp); try (complete (eexists; eauto)).
      introv h; eapply implies_univi_bar_rename; eauto.
Qed.

Lemma implies_univ_rename {o} :
  forall lib r (t1 t2 : @CTerm o) eq,
    univ lib t1 t2 eq
    -> univ (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
Proof.
  introv u; unfold univ in *; exrepnd.
  unfold per_bar in *; exrepnd.
  exists (bar2bar_ren_lib r bar) (rename_lib_per r eqa).
  dands.

  + introv br ext; introv; simpl in *.
    apply (implies_lib_extends_rename_lib r) in ext.
    pose proof (u0 _ br _ ext (lib_extends_rename_r2l x)) as u0; simpl in u0.
    unfold univ_ex in *; exrepnd.
    exists i.
    apply (implies_univi_rename _ _ r) in u2; auto.
    autorewrite with slow in *; tcsp.

  + eapply eq_term_equals_trans;
      [apply implies_eq_term_equals_rename_per;eauto|].
    apply eq_term_equals_rename_per_per_bar_eq.
Qed.

Lemma implies_close_univ_rename {o} :
  forall r lib (t1 t2 : @CTerm o) e,
    close univ lib t1 t2 e
    -> close
         univ
         (rename_lib r lib)
         (rename_cterm r t1)
         (rename_cterm r t2)
         (rename_per r e).
Proof.
  introv cl.
  apply implies_close_rename; auto.
  introv u; apply implies_univ_rename; auto.
Qed.

Lemma implies_equality_rename {o} :
  forall r lib (t1 t2 T : @CTerm o),
    equality lib t1 t2 T
    -> equality
         (rename_lib r lib)
         (rename_cterm r t1)
         (rename_cterm r t2)
         (rename_cterm r T).
Proof.
  introv equ.
  unfold equality, nuprl in *; exrepnd.
  exists (rename_per r eq).
  unfold rename_per; autorewrite with slow in *.
  dands; auto;[].
  fold (rename_per r eq).
  apply implies_close_univ_rename; auto.
Qed.

Lemma rename_cterm_lsubstc {o} :
  forall r (t : @NTerm o) w s c w' c',
    rename_cterm r (lsubstc t w s c)
    = lsubstc (rename_term r t) w' (rename_csub r s) c'.
Proof.
  introv; apply cterm_eq; simpl.
  apply rename_csubst.
Qed.

Lemma implies_similarity_rename {o} :
  forall r lib (H : @bhyps o) s1 s2,
    similarity lib s1 s2 H
    -> similarity
         (rename_lib r lib)
         (rename_csub r s1)
         (rename_csub r s2)
         (rename_barehypotheses r H).
Proof.
  induction H using rev_list_indT; simpl; introv sim; auto.

  - inversion sim; subst; simpl in *; ginv;
      try constructor; try (complete (destruct hs; ginv)).

  - apply similarity_snoc in sim; exrepnd; subst; simpl in *.
    repeat (rewrite rename_csub_snoc in * ).
    rewrite rename_barehypotheses_snoc in *.

    sim_snoc3; dands; autorewrite with slow in *; auto; eauto 3 with slow.
    destruct a; simpl in *.
    apply (implies_equality_rename r) in sim1.
    erewrite rename_cterm_lsubstc in sim1; eauto.
Qed.

Lemma rename_csub_idem {o} :
  forall r (s : @CSub o),
    rename_csub r (rename_csub r s) = s.
Proof.
  introv; unfold rename_csub; allrw map_map; unfold compose.
  apply eq_map_l; introv i; repnd; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_csub_idem : slow.

Lemma rename_hypothesis_idem {o} :
  forall r (h : @hypothesis o),
    rename_hypothesis r (rename_hypothesis r h) = h.
Proof.
  introv; destruct h; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_hypothesis_idem : slow.

Lemma rename_barehypotheses_idem {o} :
  forall r (H : @bhyps o),
    rename_barehypotheses r (rename_barehypotheses r H) = H.
Proof.
  introv; unfold rename_barehypotheses; allrw map_map; unfold compose.
  apply eq_map_l; introv i; repnd; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_barehypotheses_idem : slow.

Ltac eqh_snoc3 :=
  match goal with
  | [ |- eq_hyps _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ ?h) ] =>
    let w  := fresh "w" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    assert (wf_term (htyp h)) as w;
    [ auto
    | assert (cover_vars (htyp h) s1) as c1;
      [ auto
      | assert (cover_vars (htyp h) s2) as c2;
        [ auto
        | apply eq_hyps_snoc; simpl;
          exists s1 s2 t1 t2 w c1 c2
        ]
      ]
    ]
  end.

Lemma implies_tequality_rename {o} :
  forall r lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> tequality
         (rename_lib r lib)
         (rename_cterm r t1)
         (rename_cterm r t2).
Proof.
  introv equ.
  unfold tequality, nuprl in *; exrepnd.
  exists (rename_per r eq).
  apply implies_close_univ_rename; auto.
Qed.

Lemma implies_tequalityi_rename {o} :
  forall r lib i (t1 t2 : @CTerm o),
    tequalityi lib i t1 t2
    -> tequalityi
         (rename_lib r lib)
         i
         (rename_cterm r t1)
         (rename_cterm r t2).
Proof.
  introv equ.
  unfold tequalityi, nuprl in *; exrepnd.
  apply (implies_equality_rename r) in equ; autorewrite with slow in *; auto.
Qed.

Lemma implies_eqtypes_rename {o} :
  forall r lib lvl (t1 t2 : @CTerm o),
    eqtypes lib lvl t1 t2
    -> eqtypes
         (rename_lib r lib)
         lvl
         (rename_cterm r t1)
         (rename_cterm r t2).
Proof.
  introv equ.
  destruct lvl; simpl in *.
  - apply implies_tequality_rename; auto.
  - apply implies_tequalityi_rename; auto.
Qed.

Lemma implies_eq_hyps_rename {o} :
  forall r lib (H : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 H
    -> eq_hyps
         (rename_lib r lib)
         (rename_csub r s1)
         (rename_csub r s2)
         (rename_barehypotheses r H).
Proof.
  induction H using rev_list_indT; simpl; introv eqh; auto.

  - inversion eqh; subst; simpl in *; ginv;
      try constructor; try (complete (destruct hs; ginv)).

  - apply eq_hyps_snoc in eqh; exrepnd; subst; simpl in *.
    repeat (rewrite rename_csub_snoc in * ).
    rewrite rename_barehypotheses_snoc in *.
    eqh_snoc3; dands; autorewrite with slow in *; auto; eauto 3 with slow.

    destruct a; simpl in *.
    apply (implies_eqtypes_rename r) in eqh0.
    repeat (erewrite rename_cterm_lsubstc in eqh0); eauto.
Qed.

Lemma implies_hyps_functionality_rename {o} :
  forall r lib s (H : @bhyps o),
    hyps_functionality lib s H
    -> hyps_functionality
         (rename_lib r lib)
         (rename_csub r s)
         (rename_barehypotheses r H).
Proof.
  introv hf sim.
  apply (implies_similarity_rename r) in sim; autorewrite with slow in *.
  apply hf in sim.
  apply (implies_eq_hyps_rename r) in sim; autorewrite with slow in *; auto.
Qed.

Ltac clear_eq_left x :=
  match goal with
  | [ H : x = _ |- _ ] => clear H
  end.

Lemma implies_hyps_functionality_ext_rename {o} :
  forall r lib s (H : @bhyps o),
    hyps_functionality_ext lib s H
    -> hyps_functionality_ext
         (rename_lib r lib)
         (rename_csub r s)
         (rename_barehypotheses r H).
Proof.
  introv hf ext.
  apply lib_extends_rename_r2l in ext.
  apply hf in ext; clear hf.
  apply (implies_hyps_functionality_rename r) in ext.
  autorewrite with slow in *; auto.
Qed.

Lemma renaming_preserves_VR_sequent_true {o} :
  forall r lib (s : @csequent o),
    VR_sequent_true lib s
    -> VR_sequent_true (rename_lib r lib) (rename_csequent r s).
Proof.
  introv strue.
  apply VR_sequent_true_all.
  introv ext sim hf.

  rw @VR_sequent_true_ex in strue; simpl in strue.

  apply (implies_lib_extends_rename_lib r) in ext; autorewrite with slow in *.
  pose proof (strue (rename_lib r lib')) as q; clear strue.
  autodimp q hyp;[].

  destruct s; simpl in *.
  destruct x; simpl in *.
  destruct x; simpl in *.
  destruct x; simpl in *.
  autorewrite with slow in *.

  apply (implies_similarity_rename r) in sim; autorewrite with slow in *.
  apply (implies_hyps_functionality_ext_rename r) in hf; autorewrite with slow in *.
  apply (q _ (rename_csub r s2)) in hf; auto;[]; clear q.
  exrepnd.

  destruct concl; simpl in *.

  - exrepnd.
    introv.

    apply (implies_tequality_rename r) in hf0.
    apply (implies_equality_rename r) in hf1.
    autorewrite with slow in *.

    dands.

    + match goal with
      | [ H : tequality ?a ?b ?c |- tequality ?d ?e ?f] =>
        assert (tequality a b c = tequality d e f) as xx;[|rewrite <- xx; auto]
      end.
      f_equal; apply cterm_eq; simpl;
        rewrite rename_csubst; autorewrite with slow; auto.

    + match goal with
      | [ H : equality ?a ?b ?c ?d |- equality ?e ?f ?g ?h] =>
        assert (equality a b c d = equality e f g h) as xx;[|rewrite <- xx; auto]
      end.
      f_equal; apply cterm_eq; simpl;
        rewrite rename_csubst; autorewrite with slow; auto.

  - apply (implies_tequality_rename r) in hf0.
    autorewrite with slow in *.

    match goal with
    | [ H : tequality ?a ?b ?c |- tequality ?d ?e ?f] =>
      assert (tequality a b c = tequality d e f) as xx;[|rewrite <- xx; auto]
    end.
    f_equal; apply cterm_eq; simpl;
      rewrite rename_csubst; autorewrite with slow; auto.
Qed.

Lemma renaming_preserves_sequent_true {o} :
  forall r lib (s : @csequent o),
    sequent_true lib s
    -> sequent_true (rename_lib r lib) (rename_csequent r s).
Proof.
  introv strue.
  rw @sequent_true_eq_VR in strue.
  rw @sequent_true_eq_VR.
  apply renaming_preserves_VR_sequent_true; auto.
Qed.
