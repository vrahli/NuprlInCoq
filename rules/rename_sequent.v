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

Definition rename_per {o} (r : renaming) (e : per(o)) : per :=
  fun a b => e (rename_cterm r a) (rename_cterm r b).

Definition rename_cts {o} (r : renaming) (ts : cts(o)) : cts :=
  fun t1 t2 e => ts (rename_cterm r t1) (rename_cterm r t2) (rename_per r e).

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
Qed.

Lemma rename_sub_sub_filter {o} :
  forall r (s : @Sub o) l,
    rename_sub r (sub_filter s l)
    = sub_filter (rename_sub r s) l.
Proof.
  induction s; introv; simpl; tcsp.
  repnd; simpl; boolvar; tcsp.
  simpl; rewrite IHs; auto.
Qed.

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
Qed.

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
Qed.

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
Qed.

Lemma rename_term_subst {o} :
  forall r (t : @NTerm o) v u,
    rename_term r (subst t v u) = subst (rename_term r t) v (rename_term r u).
Proof.
  introv; unfold subst.
  rewrite rename_term_lsubst; auto.
Qed.

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

    + SCase "Abs".

      csunf comp; simpl in comp.
      apply compute_step_lib_success in comp; exrepnd; subst.
      csunf; simpl.

      apply (implies_found_entry_rename r) in comp0.
      apply found_entry_implies_compute_step_lib_success in comp0.
      rewrite comp0.
      unfold mk_instance; simpl.

Qed.

Lemma computes_to_valc_rename {o} :
  forall r lib (a b : @CTerm o),
    computes_to_valc lib a b
    -> computes_to_valc (rename_lib r lib) (rename_cterm r a) (rename_cterm r b).
Proof.
Qed.

Lemma implies_univi_rename {o} :
  forall i lib r (t1 t2 : @CTerm o) eq,
    univi lib i t1 t2 eq
    -> univi (rename_lib r lib) i (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
Proof.
  induction i using comp_ind_type; introv u; simpl in *.
  allrw @univi_exists_iff.
  exrepnd; spcast.
  exists j.
  dands; auto; spcast.

  -
Qed.

Lemma implies_univ_rename {o} :
  forall lib r (t1 t2 : @CTerm o) eq,
    univ lib t1 t2 eq
    -> univ (rename_lib r lib) (rename_cterm r t1) (rename_cterm r t2) (rename_per r eq).
Proof.
  introv u; unfold univ in *; exrepnd.
  exists i.
Qed.

Lemma implies_close_rename {o} :
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
  remember (univ lib) as ts.
  revert Heqts.
  close_cases (induction cl using @close_ind') Case; introv eqts; subst.

  - Case "CL_init".
    apply CL_init.

Abort.

Lemma implies_equality_rename {o} :
  forall lib r (t1 t2 T : @CTerm o),
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

Qed.

Lemma implies_similarity_rename {o} :
  forall r lib (H : @bhyps o) s1 s2,
    similarity lib s1 s2 H
    -> similarity
         (rename_lib r lib)
         (rename_sub r s1)
         (rename_sub r s2)
         (rename_barehypotheses r H).
Proof.
  induction H using rev_list_indT; simpl; introv sim; auto.

  - inversion sim; subst; simpl in *; ginv;
      try constructor; try (complete (destruct hs; ginv)).

  - apply similarity_snoc in sim; exrepnd; subst; simpl in *.
    repeat (rewrite rename_sub_snoc in * ).
    rewrite rename_barehypotheses_snoc in *.

    sim_snoc3; dands; autorewrite with slow in *; auto; eauto 3 with slow.
    destruct a; simpl in *.

Qed.

Lemma implies_hyps_functionality_rename {o} :
  forall r lib s (H : @bhyps o),
    hyps_functionality lib s H
    -> hyps_functionality
         (rename_lib r lib)
         (rename_sub r s)
         (rename_barehypotheses r H).
Proof.
  introv hf sim.
Qed.

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
