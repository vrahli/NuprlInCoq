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
Require Export sequents_tacs2.


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

Definition rename_cterm {o} r (ct : @CTerm o) : CTerm :=
  let (t,isp) := ct in
  mk_ct (rename_term r t) (implies_isprog_rename_term r t isp).

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

Lemma rename_cterm_idem {o} :
  forall r (t : @CTerm o),
    rename_cterm r (rename_cterm r t) = t.
Proof.
  introv; destruct t; simpl.
  apply cterm_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @rename_cterm_idem : slow.

Lemma implies_isnoncan_like_rename_term {o} :
  forall r (t : @NTerm o),
    isnoncan_like t
    -> isnoncan_like (rename_term r t).
Proof.
  introv isn.
  unfold isnoncan_like in *; repndors;[left|right].

  - unfold isnoncan in *.
    destruct t as [|f|op bs]; simpl in *; auto.
    destruct op; simpl; auto.

  - unfold isabs in *.
    destruct t as [|f|op bs]; simpl in *; auto.
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
  destruct t as [|f|op bs]; simpl in *; auto.
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
  destruct t as [|f|op bs]; simpl in *; auto.
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
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "vterm".

    rewrite sub_find_rename_sub.
    remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    erewrite ind;[|eauto].
    rewrite rename_sub_sub_filter; auto.
Defined.

Lemma bound_vars_rename_term {o} :
  forall (r : renaming) (t : @NTerm o),
    bound_vars (rename_term r t) = bound_vars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; tcsp;[].
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  apply ind in i.
  rewrite i; auto.
Qed.
Hint Rewrite @bound_vars_rename_term : slow.

Lemma flat_map_free_vars_range_rename_sub {o} :
  forall r (s : @Sub o),
    flat_map free_vars (range (rename_sub r s))
    = flat_map free_vars (range s).
Proof.
  unfold rename_sub; introv.
  unfold range.
  allrw map_map.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; repnd; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_range_rename_sub : slow.

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
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; tcsp.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  erewrite <- ind; eauto 3 with slow;[].
  autorewrite with slow; f_equal.
  rewrite rename_term_lsubst_aux; autorewrite with slow; auto.
Defined.

Lemma rename_term_lsubst {o} :
  forall r (t : @NTerm o) s,
    rename_term r (lsubst t s) = lsubst (rename_term r t) (rename_sub r s).
Proof.
  introv.
  unfold lsubst; autorewrite with slow.
  boolvar; auto.

  - rewrite rename_term_lsubst_aux; auto.

  - rewrite rename_term_lsubst_aux; auto.
    f_equal.
    apply rename_term_change_bvars_alpha.
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
  - left; eexists; eauto.
  - unfold mk_nseq; right; left; eexists; eauto.
  - unfold mk_lam; right; right; eexists; eexists; eauto.
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
  destruct t as [z|f|op bs]; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; autorewrite with slow; auto.
Qed.

Lemma get_fresh_atom_rename_term {o} :
  forall r (t : @NTerm o),
    get_fresh_atom (rename_term r t) = get_fresh_atom t.
Proof.
  introv; unfold get_fresh_atom; autorewrite with slow; auto.
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
  nterm_ind t as [v|f|op bs ind] Case; introv; tcsp;[].
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
  soterm_ind t as [v ts ind|f ind|op bs ind] Case ; introv; simpl in *; tcsp.

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
  soterm_ind t as [v ts ind|f ind|op bs ind] Case; introv; simpl; tcsp.

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
  soterm_ind t as [v ts ind|f ind|op bs ind] Case; introv; simpl; tcsp;
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
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv; simpl in *; tcsp.

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
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv; simpl in *; tcsp.

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
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl; tcsp.
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
  destruct a; simpl in *.
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

Lemma compute_step_rename {o} :
  forall r lib (a b : @NTerm o),
    compute_step lib a = csuccess b
    -> compute_step (rename_lib r lib) (rename_term r a) = csuccess (rename_term r b).
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv comp; simpl in *.

  - Case "vterm".

    csunf comp; simpl in *; ginv.

  - Case "sterm".

    csunf comp; simpl in *; ginv.
    simpl in *.
    csunf; simpl; auto.

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
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv)); [|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          + SSCase "NApply".

            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl; tcsp.

          + SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl; tcsp.
            repndors; repnd; subst; tcsp.

            * apply compute_step_eapply2_success in comp1; repnd.
              subst; simpl in *.
              repndors; exrepnd; ginv.
              csunf; simpl.
              unfold compute_step_eapply; simpl; boolvar; try omega.
              allrw @Znat.Nat2Z.id; auto.

            * csunf; simpl.
              applydup @isexc_implies2 in comp0; exrepnd; subst.
              unfold compute_step_eapply; simpl; auto.

            * exrepnd; subst; simpl in *.
              fold_terms.
              rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow;[].
              pose proof (ind arg2 arg2 []) as q; clear ind.
              repeat (autodimp q hyp); eauto 3 with slow;[].
              apply q in comp1; clear q.
              rewrite comp1; auto.

          + SSCase "NFix".

            apply compute_step_fix_success in comp; repnd; subst; simpl in *.
            csunf; simpl; auto.

          + SSCase "NCbv".

            apply compute_step_cbv_success in comp; exrepnd; subst; simpl in *.
            csunf; simpl.
            unfold apply_bterm; simpl.
            rewrite rename_term_subst; auto.

          + SSCase "NTryCatch".

            apply compute_step_try_success in comp; exrepnd; subst; tcsp.

          + SSCase "NCanTest".

            apply compute_step_seq_can_test_success in comp; exrepnd; subst; tcsp.

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

                + unfold mk_nseq in *; ginv; simpl.
                  fold_terms; unfold mk_eapply.
                  csunf; simpl.
                  unfold compute_step_eapply; simpl; boolvar; try omega.
                  allrw @Znat.Nat2Z.id; auto.

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

        - pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto with slow;
            try (complete (rewrite simple_osize_subst; simpl; auto; eauto 3 with slow)).
          apply q in comp2; clear q.
          rewrite computation3.compute_step_fresh_if_isnoncan_like; eauto 3 with slow.
          rewrite rename_term_subst in comp2; simpl in *; autorewrite with slow in *.
          fold_terms; rewrite comp2; simpl; auto.
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
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; simpl in *; auto.

  - Case "sterm".
    inversion wf as [|? imp|]; subst; clear wf.
    constructor; introv.
    pose proof (ind n) as q; clear ind.
    pose proof (imp n) as h; clear imp.
    repnd.
    dands; eauto 3 with slow.

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
  nterm_ind1s a as [v|f|op bs ind] Case; introv aeq.

  - Case "vterm".
    inversion aeq; subst; clear aeq; simpl; auto.

  - Case "sterm".
    inversion aeq as [|? ? imp|]; subst; clear aeq; simpl; auto.

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

Lemma computes_to_seq_rename {o} :
  forall r lib (a : @NTerm o) f,
    computes_to_seq lib a f
    -> computes_to_seq (rename_lib r lib) (rename_term r a) (rename_seq r f).
Proof.
  introv comp.
  unfold computes_to_exception in *.
  apply (reduces_to_rename r) in comp; simpl in *; auto.
Qed.
Hint Resolve computes_to_seq_rename : slow.

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

  - clear cl3 cl4 cl.
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

  - clear cl2 cl4 cl.
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

  - clear cl2 cl3 cl.
    unfold close_compute_exc in *.
    introv comp.
    apply (computes_to_seq_rename r) in comp; simpl in *.
    autorewrite with slow in *.

    apply cl4 in comp; clear cl4.
    exrepnd.
    apply (computes_to_seq_rename r) in comp1; simpl in *.
    eexists; dands; eauto.

    introv.
    pose proof (comp0 n) as q; clear comp0; repndors; tcsp.
    left.
    apply (IND r) in q.
    unfold rename_seq in *.
    autorewrite with slow in *.
    auto.
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

Definition rename_cts {o} (r : renaming) (ts : cts(o)) : cts :=
  fun t1 t2 e => ts (rename_cterm r t1) (rename_cterm r t2) (rename_per r e).

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
  rewrite (rename_cterm_idem r a) in w.
  rewrite (rename_cterm_idem r a') in w.
  unfold eq_ind_r in w; simpl in w.
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
  rewrite (rename_cterm_idem r a) in w.
  rewrite (rename_cterm_idem r a') in w.
  unfold eq_ind_r in w; simpl in w.
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

    + spcast.
      apply (implies_cequivc_rename r) in h1.
      apply (implies_cequivc_rename r) in h2.
      autorewrite with slow in *.
      eapply image_eq_eq; spcast; eauto.

  - induction h as [|? ? ? ? ? h1 h2].

    + econstructor; eauto.

    + spcast.
      apply (implies_cequivc_rename r) in h1.
      apply (implies_cequivc_rename r) in h2.
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

  remember (rename_cterm_idem r a) as w; clear Heqw.
  revert w; autorewrite with slow; introv.
  rewrite (UIP_refl _ _ w); auto; clear w.

  remember (rename_cterm_idem r a') as w; clear Heqw.
  revert w; autorewrite with slow; introv.
  rewrite (UIP_refl _ _ w); auto; clear w.
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
  repeat introv; unfold rename_per; autorewrite with slow; auto.
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
    rewrite (UIP_refl _ _ w); auto.

  - unfold rename_per_fam, rename_per.
    unfold eq_ind, eq_rect; simpl.
    remember (eq_rename_per_idem2 r ea a1 a2) as w; clear Heqw.
    revert e1 w.
    unfold rename_per.
    autorewrite with slow; introv.
    rewrite (UIP_refl _ _ w); auto.
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
  rewrite (UIP_refl _ _ w); auto.
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
  rewrite (UIP_refl _ _ w); auto.
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
  rewrite (rename_cterm_idem r p) in w.
  rewrite (rename_cterm_idem r a1) in w.
  rewrite (rename_cterm_idem r a2) in w.
  unfold eq_ind_r in w; simpl in w.
  unfold eq_ind, eq_rect, eq_sym in w.
  rewrite Equality.UIP_refl_refl in w.
  apply hb in w; autorewrite with rename slow in *; auto.
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
  rewrite (rename_cterm_idem r p) in w.
  rewrite (rename_cterm_idem r a1) in w.
  rewrite (rename_cterm_idem r a2) in w.
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

Lemma implies_close_rename {o} :
  forall r (u : library -> cts(o)) lib (t1 t2 : @CTerm o) e,
    (forall lib t1 t2 e,
        u lib t1 t2 e
        -> u (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r e))
    -> close lib (u lib) t1 t2 e
    -> close
         (rename_lib r lib)
         (u (rename_lib r lib))
         (rename_cterm r t1)
         (rename_cterm r t2)
         (rename_per r e).
Proof.
  introv imp cl.
  remember (u lib) as ts.
  revert Heqts.
  close_cases (induction cl using @close_ind') Case; introv eqts; subst.

  - Case "CL_init".
    apply CL_init.
    apply imp; auto.

  - Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
    unfold equality_of_int; split; introv h; exrepnd; spcast.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists k; dands; spcast; auto.

    + apply (computes_to_valc_rename r) in h1.
      apply (computes_to_valc_rename r) in h0.
      autorewrite with slow in *.
      exists k; dands; spcast; auto.

  - Case "CL_atom".
    apply CL_atom.
    unfold per_atom in *; repnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per1.
    autorewrite with slow in *.
    dands; spcast; auto.
    unfold rename_per; introv; rw per.
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
    split; introv h; exrepnd; spcast;
      apply (implies_cequivc_rename r) in h; autorewrite with slow in *; auto.

  - Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd; spcast.
    apply (computes_to_valc_rename r) in per0.
    apply (computes_to_valc_rename r) in per2.
    autorewrite with slow rename in *.
    eexists; eexists; eexists; eexists; dands; spcast; eauto.

    + split; intro h;
        apply (implies_capproxc_rename r) in h; autorewrite with slow in *;
          apply per3 in h; apply (implies_capproxc_rename r) in h; auto.

    + introv; unfold rename_per; simpl.
      rw per1; clear per1.
      split; intro h; repnd; spcast.

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

    + split; intro h;
        apply (implies_ccequivc_rename r) in h; autorewrite with slow in *;
          apply per3 in h; apply (implies_ccequivc_rename r) in h; auto.

    + introv; unfold rename_per; simpl.
      rw per1; clear per1.
      split; intro h; repnd; spcast.

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
    exists (rename_per r eqa).
    dands; spcast; eauto;[| |].

    + destruct eos1 as [eos1|eos1];[left|right]; spcast; eauto 3 with slow.

    + destruct eos2 as [eos2|eos2];[left|right]; spcast; eauto 3 with slow.

    + introv; unfold rename_per.
      rw eqiff; autorewrite with slow; tcsp.
      split; introv h; repnd; dands; tcsp; spcast;
        try (complete (apply (computes_to_valc_rename r) in h0; autorewrite with slow in *; auto));
        try (complete (apply (computes_to_valc_rename r) in h1; autorewrite with slow in *; auto)).

  - Case "CL_req".
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
        introv; tcsp.

  - Case "CL_func".
    apply CL_func.
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
        introv; tcsp.

  - Case "CL_disect".
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
      eexists; eexists; eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

  - Case "CL_union".
    repeat (autodimp IHcl1 hyp).
    repeat (autodimp IHcl2 hyp).
    apply CL_union.
    spcast.
    unfold per_union.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    exists (rename_per r eqa) (rename_per r eqb).
    eexists; eexists; eexists; eexists.
    dands; spcast; eauto; eauto 3 with slow.

    introv; unfold rename_per.
    rw eqiff; tcsp.
    unfold per_union_eq.
    unfold per_union_eq_L, per_union_eq_R.
    split; introv h; repndors; exrepnd; spcast.

    * apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h2.
      autorewrite with slow in *.
      left.
      eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

    * apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h2.
      autorewrite with slow in *.
      right.
      eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

    * apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h2.
      autorewrite with slow in *.
      left.
      eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

    * apply (computes_to_valc_rename r) in h0.
      apply (computes_to_valc_rename r) in h2.
      autorewrite with slow in *.
      right.
      eexists; eexists; dands; spcast; eauto; autorewrite with slow; auto.

  - Case "CL_image".
    repeat (autodimp IHcl hyp).
    apply CL_image.
    spcast.
    unfold per_image.
    apply (computes_to_valc_rename r) in c1.
    apply (computes_to_valc_rename r) in c2.
    autorewrite with slow in *.

    exists (rename_per r eqa).
    eexists; eexists; eexists; eexists.
    dands; spcast; eauto; eauto 3 with slow.

    introv; rw eqiff; tcsp.
    rw <- (rename_per_image_eq r lib); autorewrite with slow; tcsp.

  - Case "CL_partial".
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
      exists (rename_cterm r y); dands; eauto 3 with slow.

  - Case "CL_set".
    apply CL_set.
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

      * dup h as q.
        apply rename_per_iff in q.
        unfold rename_per1 in q; exrepnd; subst.
        apply eqiff in h; exrepnd.
        apply implies_inhabited_rename_per_fam in h0.
        eexists; eauto.

      * exrepnd.
        unfold rename_per.
        apply eqiff.
        apply inhabited_rename_per_fam_implies in h0.
        eexists; eauto.

  - Case "CL_tunion".
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
        autorewrite with slow in *; auto.

  - Case "CL_product".
    apply CL_product.
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

      * unfold per_product_eq in *; exrepnd; spcast.
        apply (computes_to_valc_rename r) in h1.
        apply (computes_to_valc_rename r) in h2.
        autorewrite with slow in *.
        eexists; eexists; eexists; eexists.
        exists (implies_rename_per r eqa a a' e).
        dands; spcast; eauto.

        { unfold rename_per; autorewrite with slow; auto. }

        apply implies_rename_per_fam; auto.

      * unfold per_product_eq in *; exrepnd; spcast.
        apply (computes_to_valc_rename r) in h1.
        apply (computes_to_valc_rename r) in h2.
        autorewrite with slow in *.
        clear h3.
        unfold rename_per_fam, rename_per in *.

        eexists; eexists; eexists; eexists.
        exists (implies_rename_per2 r eqa a a' e).
        dands; spcast; eauto.
Qed.

Lemma implies_univi_rename {o} :
  forall i lib r (t1 t2 : @CTerm o) eq,
    univi lib i t1 t2 eq
    -> univi (rename_lib r lib) i (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
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
    split; introv h; exrepnd.

    + pose proof (implies_close_rename r (fun lib => univi lib j) lib (rename_cterm r A) (rename_cterm r A') eqa) as q.
      simpl in q; autorewrite with slow in q.
      repeat (autodimp q hyp).
      eexists; eauto.

    + pose proof (implies_close_rename r (fun lib => univi lib j) (rename_lib r lib) A A' eqa) as q.
      simpl in q; autorewrite with slow in q.
      repeat (autodimp q hyp).
      eexists; eauto.
Qed.

Lemma implies_univ_rename {o} :
  forall lib r (t1 t2 : @CTerm o) eq,
    univ lib t1 t2 eq
    -> univ (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
Proof.
  introv u; unfold univ in *; exrepnd.
  exists i.
  apply implies_univi_rename; auto.
Qed.

Lemma implies_close_univ_rename {o} :
  forall r lib (t1 t2 : @CTerm o) e,
    close lib (univ lib) t1 t2 e
    -> close
         (rename_lib r lib)
         (univ (rename_lib r lib))
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

  apply (implies_similarity_rename r) in sim; autorewrite with slow in *.
  apply (implies_hyps_functionality_rename r) in hf; autorewrite with slow in *.
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
