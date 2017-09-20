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

Require Export sequents_lib.


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
  | sterm s => sterm (fun n => rename_term r (s n))
  | oterm op bs => oterm (rename_op r op) (map (rename_bterm r) bs)
  end
with rename_bterm {o} (r : renaming) (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (rename_term r t)
       end.

Fixpoint rename_soterm {o} (r : renaming) (t : @SOTerm o) : SOTerm :=
  match t with
  | sovar v ts => sovar v (map (rename_soterm r) ts)
  | soseq s => soseq (fun n => rename_term r (s n))
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
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv; simpl in *; tcsp.

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
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; tcsp;[].
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  apply ind in i.
  rewrite i; auto.
Qed.
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
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; tcsp;[].
  allrw flat_map_map; unfold compose; autorewrite with slow in *.
  f_equal.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  apply ind in i.
  rewrite i; auto.
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
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "sterm".
    allrw @wf_sterm_iff.
    introv.
    pose proof (ind n) as q; clear ind.
    pose proof (wf n) as h; clear wf.
    allrw @computation_seq.isprog_nout_iff.
    repnd.
    allrw @nt_wf_eq.
    dands; eauto 3 with slow.

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
  soterm_ind t as [v ts ind|f ind|op bs ind] Case; introv; simpl; tcsp.

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
  soterm_ind t as [v ts ind|f ind|op bs ind] Case; introv; simpl; tcsp.

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

Definition rename_library_entry {o} (r : renaming) (e : @library_entry o) : library_entry :=
  match e with
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
  induction H; introv; simpl; tcsp.
  f_equal; tcsp.
Qed.

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
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sterm".
    f_equal.
    apply functional_extensionality; tcsp.

  - Case "oterm".
    autorewrite with slow in *; allrw map_map; unfold compose.
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    erewrite ind; eauto.
Qed.
Hint Rewrite @rename_term_idem : slow.

Lemma rename_soterm_idem {o} :
  forall r (t : @SOTerm o),
    rename_soterm r (rename_soterm r t) = t.
Proof.
  soterm_ind t as [v ts ind|f ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; tcsp.

  - Case "soseq".
    f_equal.
    apply functional_extensionality; introv; autorewrite with slow; auto.

  - Case "soterm".
    autorewrite with slow; allrw map_map; unfold compose.
    f_equal.
    apply eq_map_l; introv i; destruct x; simpl.
    erewrite ind; eauto.
Qed.
Hint Rewrite @rename_soterm_idem : slow.

Lemma rename_library_entry_idem {o} :
  forall r (e : @library_entry o),
    rename_library_entry r (rename_library_entry r e) = e.
Proof.
  introv; destruct e; simpl.

  remember (rename_correct r (rename_correct r correct)) as cor; clear Heqcor.
  revert cor.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
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
  destruct e, a; simpl in *.
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

Lemma implies_lib_extends_rename_lib {o} :
  forall r (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> lib_extends (rename_lib r lib1) (rename_lib r lib2).
Proof.
  introv ext i.
  apply (implies_entry_in_library_rename r) in i; autorewrite with slow in *.
  apply ext in i.
  apply (implies_entry_in_library_rename r) in i; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_lib_extends_rename_lib : slow.

Lemma renaming_preserves_sequent_true_ext_lib {o} :
  forall r lib (s : @csequent o),
    sequent_true_ext_lib lib s
    -> sequent_true_ext_lib (rename_lib r lib) (rename_csequent r s).
Proof.
  introv strue.
  apply sequent_true_ext_lib_all.
  introv ext sim hf.

  apply (implies_lib_extends_rename_lib r) in ext; autorewrite with slow in *.
  pose proof (strue (rename_lib r lib0)) as q; clear strue.
  autodimp q hyp;[].

  rw @VR_sequent_true_ex in q; simpl in q.

  destruct s; simpl in *.
  destruct x; simpl in *.
  destruct x; simpl in *.
  destruct x; simpl in *.
  autorewrite with slow in *.

Qed.