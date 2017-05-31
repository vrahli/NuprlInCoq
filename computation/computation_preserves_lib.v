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


Require Export computation4.
Require Export computation10.


Lemma eq_opabs_implies :
  forall x y : opabs,
    x = y -> (opabs_name x = opabs_name y
              # opabs_params x = opabs_params y
              # opabs_sign x = opabs_sign y).
Proof.
  introv xx; subst; auto.
Qed.

Lemma opabs_deq : Deq opabs.
Proof.
  introv.
  destruct (decidable_eq_opabs_name x y);
    destruct (decidable_eq_opabs_sign x y);
    destruct (parameters_dec (opabs_params x) (opabs_params y));
    destruct x, y; simpl in *; subst; tcsp;
    try (complete (right; intro xx; apply eq_opabs_implies in xx; tcsp)).
Defined.

Lemma sovar_sig_deq : Deq sovar_sig.
Proof.
  introv.
  destruct x, y.
  destruct (deq_nat n0 n2); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
  destruct (deq_nvar n n1); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
Defined.

Definition same_opabs (oa1 oa2 : opabs) := matching_entry_sign oa1 oa2.

Lemma matching_entry_sign_is_same_opabs :
  forall opabs1 opabs2,
    matching_entry_sign opabs1 opabs2
    = same_opabs opabs1 opabs2.
Proof.
  sp.
Qed.

Definition same_opabs_dec :
  forall oa1 oa2, decidable (same_opabs oa1 oa2).
Proof.
  introv.
  destruct (decidable_eq_opabs_name oa1 oa2) as [n|n];
    try (complete (right; intro xx; inversion xx; tcsp)).
  destruct (decidable_eq_opabs_sign oa1 oa2) as [s|s];
    try (complete (right; intro xx; inversion xx; tcsp)).

  unfold same_opabs, matching_entry_sign.
  unfold matching_parameters, assert.
  destruct (matching_parametersb (opabs_params oa1) (opabs_params oa2)); simpl;
    try (complete (right; intro xx; inversion xx; tcsp)).
  left; dands; auto.
Defined.

Inductive EntryName :=
| entry_name_cs (name : choice_sequence_name)
| entry_name_abs (name : opabs).

Definition entry2name {o} (e : @library_entry o) : EntryName :=
  match e with
  | lib_cs name _ => entry_name_cs name
  | lib_abs opabs _ _ _ => entry_name_abs opabs
  end.

Definition same_entry_name (n1 n2 : EntryName) :=
  match n1, n2 with
  | entry_name_cs name1, entry_name_cs name2 => name1 = name2
  | entry_name_abs opabs1, entry_name_abs opabs2 => same_opabs opabs1 opabs2
  | _, _ => False
  end.

Definition same_entry_name_dec :
  forall n1 n2, decidable (same_entry_name n1 n2).
Proof.
  introv; destruct n1, n2; simpl; try (complete (right; tcsp)).
  - destruct (choice_sequence_name_deq name name0);[left|right];tcsp.
  - destruct (same_opabs_dec name name0);[left|right]; tcsp.
Defined.

Definition in_lib {o}
           (name : EntryName)
           (lib  : @library o) :=
  exists (e : library_entry),
    List.In e lib
    /\ same_entry_name name (entry2name e).

Lemma in_lib_dec {o} :
  forall (name : EntryName)
         (lib  : @library o),
    decidable (in_lib name lib).
Proof.
  unfold in_lib; induction lib; simpl.
  - right; intro xx; exrepnd; auto.
  - destruct a.

    { destruct name.
      - destruct (choice_sequence_name_deq name name0); subst.
        + left; exists (lib_cs name0 entry); simpl; dands; auto.
        + destruct IHlib as [k|k].
          * left; exrepnd; exists e; dands; auto.
          * right; intro zz; exrepnd; destruct k.
            exists e; dands; auto.
            repndors; subst; simpl in *; tcsp.
      - destruct IHlib as [k|k].
        + left; exrepnd; exists e; dands; auto.
        + right; intro z; destruct k; exrepnd; exists e; dands; auto.
          repndors; subst; simpl in *; tcsp. }

    { destruct name.
      - destruct IHlib as [k|k]; exrepnd.
        + left; exrepnd; eexists; eexists; eauto.
        + right; intro xx; destruct k; exrepnd; exists e; dands; auto.
          repndors; subst; simpl in *; tcsp.
      - destruct (same_opabs_dec name opabs) as [d|d]; ginv.
        + left; eexists; eexists; eauto.
        + destruct IHlib as [k|k]; exrepnd.
          * left; exrepnd; eexists; eexists; eauto.
          * right; intro xx; exrepnd; repndors; subst; allsimpl; tcsp.
            destruct k; eexists; eexists; eauto. }
Defined.

Lemma found_entry_in {o} :
  forall lib oa0 (bs : list (@BTerm o)) oa vars rhs correct,
    found_entry lib oa0 bs oa vars rhs correct
    -> LIn (lib_abs oa vars rhs correct) lib.
Proof.
  unfold found_entry.
  induction lib; introv fe; allsimpl; ginv.
  destruct a.

  { right.
    eapply IHlib; eauto. }

  boolvar; ginv; tcsp.
  - apply some_inj in fe; tcsp.
  - right.
    eapply IHlib; eauto.
Qed.

Lemma matching_paramsb_sym :
  forall p1 p2,
    matching_paramsb p1 p2 = true
    -> matching_paramsb p2 p1 = true.
Proof.
  introv m.
  destruct p1; allsimpl; tcsp.
  destruct pt; allsimpl; tcsp.
Qed.

Lemma matching_paramsb_trans :
  forall p1 p2 p3,
    matching_paramsb p1 p2 = true
    -> matching_paramsb p2 p3 = true
    -> matching_paramsb p1 p3 = true.
Proof.
  introv m1 m2.
  destruct p1; allsimpl; tcsp.
  destruct pt; allsimpl; tcsp.
  - destruct p2; allsimpl; tcsp.
    destruct pt; allsimpl; tcsp.
  - destruct p2; allsimpl; tcsp.
    destruct pt; allsimpl; tcsp.
Qed.

Lemma matching_parameters_sym :
  forall ps1 ps2,
    matching_parameters ps1 ps2
    -> matching_parameters ps2 ps1.
Proof.
  unfold matching_parameters, assert.
  induction ps1; introv m; simpl in *.
  - destruct ps2; allsimpl; tcsp.
  - destruct ps2; allsimpl; tcsp.
    allrw andb_eq_true; repnd.
    dands; eauto.
    eapply matching_paramsb_sym; eauto.
Qed.

Lemma matching_parameters_trans :
  forall ps1 ps2 ps3,
    matching_parameters ps1 ps2
    -> matching_parameters ps2 ps3
    -> matching_parameters ps1 ps3.
Proof.
  unfold matching_parameters, assert.
  induction ps1; introv m1 m2; simpl in *.
  - destruct ps2; allsimpl; tcsp.
  - destruct ps2; allsimpl; tcsp.
    destruct ps3; allsimpl; tcsp.
    allrw andb_eq_true; repnd.
    dands; eauto.
    eapply matching_paramsb_trans; eauto.
Qed.

Lemma LIn_implies_In :
  forall {A} (l : list A) a,
    LIn a l -> List.In a l.
Proof.
  induction l; simpl; tcsp.
Qed.

Lemma found_entry_add_new_abs {o} :
  forall lib abs (bs : list (@BTerm o)) oa2 vars0 rhs0 correct0 opabs vars rhs correct,
    !in_lib (entry_name_abs opabs) lib
    -> found_entry lib abs bs oa2 vars0 rhs0 correct0
    -> found_entry
         (lib_abs opabs vars rhs correct :: lib)
         abs bs oa2 vars0 rhs0 correct0.
Proof.
  introv nilib fe.
  applydup @found_entry_implies_matching_entry in fe.
  applydup @found_entry_in in fe.

  apply LIn_implies_In in fe1.

  allunfold @found_entry; simpl.
  boolvar; auto.
  assert False; tcsp.

  unfold matching_entry in *; repnd.
  destruct nilib; unfold in_lib, same_opabs.
  eexists; dands; eauto; simpl; tcsp.
  split; dands; tcsp.

  apply matching_parameters_sym.
  eapply matching_parameters_trans; eauto.
  apply matching_parameters_sym; auto.
Qed.

Lemma implies_in_lib_cons {o} :
  forall e e' (lib : @library o),
    in_lib e lib
    -> in_lib e (e' :: lib).
Proof.
  introv i; unfold in_lib in *; exrepnd; simpl.
  eexists; dands; eauto.
Qed.
Hint Resolve implies_in_lib_cons : slow.

Lemma find_cs_value_at_some_implies_in_lib {o} :
  forall name n v (lib : @library o),
    find_cs_value_at lib name n = Some v
    -> in_lib (entry_name_cs name) lib.
Proof.
  induction lib; introv fc; simpl in *.

  - unfold find_cs_value_at in fc; simpl in *; ginv.

  - unfold find_cs_value_at in fc; simpl in *.
    destruct a.

    + boolvar; subst.

      * unfold in_lib; simpl.
        exists (lib_cs name0 entry); simpl; tcsp.

      * remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
        autodimp IHlib hyp; eauto 2 with slow.
        unfold find_cs_value_at; allrw; auto.

    + remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
      autodimp IHlib hyp; eauto 2 with slow.
      unfold find_cs_value_at; allrw; auto.
Qed.

Lemma matching_entry_sign_trans :
  forall abs1 abs2 abs3,
    matching_entry_sign abs1 abs2
    -> matching_entry_sign abs2 abs3
    -> matching_entry_sign abs1 abs3.
Proof.
  introv m1 m2.
  allunfold @matching_entry_sign; repnd; dands; allrw; tcsp.
  eapply matching_parameters_trans; eauto.
Qed.

Lemma same_opabs_trans :
  forall opabs1 opabs2 opabs3,
    same_opabs opabs1 opabs2
    -> same_opabs opabs2 opabs3
    -> same_opabs opabs1 opabs3.
Proof.
  introv same1 same2.
  allrw <- matching_entry_sign_is_same_opabs.
  eapply matching_entry_sign_trans; eauto.
Qed.

Lemma matching_entry_sign_sym :
  forall abs1 abs2,
    matching_entry_sign abs1 abs2
    -> matching_entry_sign abs2 abs1.
Proof.
  introv m.
  allunfold @matching_entry_sign; repnd; dands; allrw; tcsp.
  eapply matching_parameters_sym; eauto.
Qed.

Lemma same_opabs_sym :
  forall opabs1 opabs2,
    same_opabs opabs1 opabs2
    -> same_opabs opabs2 opabs1.
Proof.
  introv same.
  allrw <- matching_entry_sign_is_same_opabs.
  apply matching_entry_sign_sym; auto.
Qed.

Lemma same_entry_name_sym :
  forall name1 name2, same_entry_name name1 name2 -> same_entry_name name2 name1.
Proof.
  introv same.
  unfold same_entry_name in *.
  destruct name1; destruct name2; auto.
  apply same_opabs_sym; auto.
Qed.
Hint Resolve same_entry_name_sym : slow.

Lemma implies_matching_parameters_refl :
  forall params1 params2,
    matching_parameters params1 params2
    -> matching_parameters params1 params1.
Proof.
  introv m.
  unfold matching_parameters in *.
  revert dependent params2.
  induction params1; allsimpl; introv m; destruct params2; allsimpl; tcsp.
  - inversion m.
  - allrw assert_andb; repnd; dands; auto.
    + unfold matching_paramsb in *.
      destruct a.
      destruct pt; tcsp.
    + eapply IHparams1; eauto.
Qed.

Lemma same_entry_name_trans :
  forall name1 name2 name3,
    same_entry_name name1 name2
    -> same_entry_name name2 name3
    -> same_entry_name name1 name3.
Proof.
  introv same1 same2.
  unfold same_entry_name in *.
  destruct name1, name2, name3; subst; tcsp.
  eapply same_opabs_trans; eauto.
Qed.
Hint Resolve same_entry_name_trans : slow.

Lemma same_entry_name_preserves_in_lib {o} :
  forall name1 name2 (lib : @library o),
    same_entry_name name1 name2
    -> in_lib name1 lib
    -> in_lib name2 lib.
Proof.
  introv same i; unfold in_lib in *; exrepnd; exists e; dands; auto.
  eapply same_entry_name_trans;[|eauto].
  apply same_entry_name_sym; auto.
Qed.

Lemma not_same_entry_name_preserves_find_cs_value_at_cons {o} :
  forall (lib : @library o) name n v e,
    find_cs_value_at lib name n = Some v
    -> !same_entry_name (entry2name e) (entry_name_cs name)
    -> find_cs_value_at (e :: lib) name n = Some v.
Proof.
  introv fc ns.
  unfold find_cs_value_at in *; simpl in *.
  destruct e; simpl in *; tcsp.
  boolvar; tcsp.
Qed.

Lemma not_in_lib_preserves_find_cs_value_at_cons {o} :
  forall (lib : @library o) e name n v,
    ! in_lib (entry2name e) lib
    -> find_cs_value_at lib name n = Some v
    -> find_cs_value_at (e :: lib) name n = Some v.
Proof.
  introv ni fcs.
  applydup @find_cs_value_at_some_implies_in_lib in fcs.
  destruct (same_entry_name_dec (entry2name e) (entry_name_cs name)) as [d|d].

  - apply same_entry_name_sym in d; eapply same_entry_name_preserves_in_lib in d;[|eauto]; tcsp.

  - apply not_same_entry_name_preserves_find_cs_value_at_cons; auto.
Qed.

Hint Rewrite @get_utokens_sub_cons : slow.

Lemma wf_term_eapply_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NEApply) bs)
    <=> {a, b : NTerm $ bs = [bterm [] a, bterm [] b] # wf_term a # wf_term b}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1]; destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_eapply_implies_subterm2 {o} :
  forall (a b : @NTerm o) l,
    wf_term (oterm (NCan NEApply) (nobnd a :: nobnd b :: l))
    -> wf_term b.
Proof.
  introv wf; apply wf_term_eapply_iff in wf; exrepnd.
  unfold nobnd in *; destruct l; ginv; auto.
Qed.
Hint Resolve wf_term_eapply_implies_subterm2 : wf.

Lemma wf_term_compop_implies_subterm2 {o} :
  forall c (a b : @NTerm o) l,
    wf_term (oterm (NCan (NCompOp c)) (bterm [] a :: bterm [] b :: l))
    -> wf_term b.
Proof.
  introv wf; apply wf_term_ncompop_iff in wf; exrepnd; ginv; auto.
Qed.
Hint Resolve wf_term_compop_implies_subterm2 : wf.

Lemma wf_term_arithop_implies_subterm2 {o} :
  forall c (a b : @NTerm o) l,
    wf_term (oterm (NCan (NArithOp c)) (bterm [] a :: bterm [] b :: l))
    -> wf_term b.
Proof.
  introv wf; apply wf_term_narithop_iff in wf; exrepnd; ginv; auto.
Qed.
Hint Resolve wf_term_arithop_implies_subterm2 : wf.

Lemma wf_term_ncan_implies_subterm1 {o} :
  forall ncan (t : @NTerm o) l,
    wf_term (oterm (NCan ncan) (bterm [] t :: l))
    -> wf_term t.
Proof.
  introv wf.
  apply wf_oterm_iff in wf; simpl in *; repnd.
  pose proof (wf (nobnd t)) as q; autodimp q hyp.
Qed.
Hint Resolve wf_term_ncan_implies_subterm1 : wf.

Lemma wf_term_fresh_implies_subterm1 {o} :
  forall n (t : @NTerm o),
    wf_term (oterm (NCan NFresh) [bterm [n] t])
    -> wf_term t.
Proof.
  introv wf.
  apply wf_oterm_iff in wf; simpl in *; repnd.
  pose proof (wf (bterm [n] t)) as q; autodimp q hyp.
Qed.
Hint Resolve wf_term_fresh_implies_subterm1 : wf.

Hint Resolve wf_term_implies : wf.
Hint Resolve nt_wf_implies : wf.

Lemma utoken_not_in_get_utokens_lib_cons_implies {o} :
  forall a e (lib : @library o) t,
    !LIn a (get_utokens_lib (e :: lib) t)
    -> !LIn a (get_utokens_lib lib t).
Proof.
  introv ni i; destruct ni.
  allrw in_app_iff; tcsp.
Qed.
Hint Resolve utoken_not_in_get_utokens_lib_cons_implies : slow.

Lemma not_in_get_utokens_lib_implies_nr_ut_sub_cons {o} :
  forall n a (lib : @library o) t,
    !LIn a (get_utokens_lib lib t)
    -> nr_ut_sub lib t [(n, mk_utoken a)].
Proof.
  tcsp.
Qed.
Hint Resolve not_in_get_utokens_lib_implies_nr_ut_sub_cons : slow.

Lemma wf_fresh_implies_wf_subst {o} :
  forall n (t : @NTerm o) a,
    wf_term (mk_fresh n t)
    -> wf_term (subst t n (mk_utoken a)).
Proof.
  introv wf.
  allrw @wf_fresh_iff.
  apply wf_term_subst; eauto 2 with slow.
Qed.
Hint Resolve wf_fresh_implies_wf_subst : wf.

Hint Rewrite Znat.Nat2Z.id : slow.

Lemma not_in_get_utokens_lib_implies_not_in_get_utokens {o} :
  forall a (lib : @library o) t,
    !LIn a (get_utokens_lib lib t)
    -> !LIn a (get_utokens t).
Proof.
  introv ni i; destruct ni; apply in_app_iff; tcsp.
Qed.
Hint Resolve not_in_get_utokens_lib_implies_not_in_get_utokens : slow.

Lemma not_in_subset :
  forall {A} (l1 l2 : list A) x,
    !LIn x l1
    -> subset l2 l1
    -> !LIn x l2.
Proof.
  introv ni ss i; apply ss in i; tcsp.
Qed.
Hint Resolve not_in_subset : slow.

(* we should be able to prove that b = b'.  For that we would need something
   like what I started to prove in computation_preserves_utok.  That one there
   is not exactly right, but we should be able to prove that s and w only differ
   at those names that we put in.  We might need more constraints on the substitutions
   saying that if one maps v|->a and w|->a then the other one cannot map those variables
   to different names... *)
Lemma compute_step_consistent_with_new_definition {o} {lib} :
  forall (e    : library_entry)
         (p    : !in_lib (entry2name e) lib)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : compute_step lib a = csuccess b),
    {b' : NTerm & compute_step (e :: lib) a = csuccess b' # alpha_eq b b'}.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv wf comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    csunf; simpl.
    eexists; dands; eauto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl.
      eexists; dands; eauto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv;
            try (complete (csunf; simpl; allrw; eexists; dands; eauto));[].

          SSCase "NEApply".

          apply compute_step_eapply_success in comp; exrepnd; subst.
          repndors; exrepnd; allsimpl; subst.

          + apply compute_step_eapply2_success in comp1; repnd; subst.
            repndors; exrepnd; subst; ginv.
            csunf; simpl.
            dcwf h; simpl.
            boolvar; try omega.
            autorewrite with slow; eexists; dands; eauto.

          + csunf; simpl.
            apply isexc_implies2 in comp0; exrepnd; subst.
            dcwf h; simpl; auto.
            eexists; dands; eauto.

          + fold_terms.
            rewrite compute_step_eapply_iscan_isnoncan_like; auto.
            pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            apply h in comp1; clear h; eauto 3 with wf.
            exrepnd.
            allrw; simpl.
            eexists; dands; eauto.
            repeat prove_alpha_eq4.

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto;
                try (complete (csunf; simpl; eexists; dands; eauto)).
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto;
                    try (complete (eexists; dands; eauto)).

                + unfold mk_nseq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  autorewrite with slow.
                  eexists; dands; eauto.

                + unfold mk_choice_seq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  autorewrite with slow.
                  erewrite not_in_lib_preserves_find_cs_value_at_cons; eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.
                eexists; dands; eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q; eauto 2 with wf.
                exrepnd; allrw.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto;
                try (complete (csunf; simpl; eexists; dands; eauto)).
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
              unfold compute_step_sleep; simpl; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              autorewrite with slow.
              eexists; dands; eauto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; unfold compute_step_minus; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
              compute; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h; simpl.
                allrw; eexists; dands; eauto.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with wf.
                exrepnd; allrw; eexists; dands; eauto.
                repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h; simpl.
                allrw; eexists; dands; eauto.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with wf.
                exrepnd; allrw.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              eexists; dands; eauto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 2 with wf.
            csunf; simpl.
            exrepnd; allrw; simpl.
            eexists; dands; eauto.
            repeat prove_alpha_eq4.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.
              eexists; dands; eauto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.
              eexists; dands; eauto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 2 with wf.
            csunf; simpl.
            exrepnd; allrw; simpl.
            eexists; dands; eauto.
            repeat prove_alpha_eq4.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.
          eexists; dands; eauto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.
          eexists; dands; eauto.

        - rewrite compute_step_fresh_if_isnoncan_like; auto.

          remember (get_fresh_atom lib t) as a.
          pose proof (get_fresh_atom_prop_and_lib lib t) as prop; rewrite <- Heqa in prop.
          clear Heqa.

          remember (get_fresh_atom (e :: lib) t) as a'.
          pose proof (get_fresh_atom_prop_and_lib (e :: lib) t) as prop'; rewrite <- Heqa' in prop'.
          clear Heqa'.

          pose proof (compute_step_subst_utoken lib t x [(n,mk_utoken a)]) as q.
          repeat (autodimp q hyp); eauto 3 with wf;
            [autorewrite with slow; simpl; apply disjoint_singleton_l; auto|];[].
          exrepnd.
          autorewrite with slow in *; simpl in *; allrw disjoint_singleton_l.

          pose proof (q0 [(n,mk_utoken a')]) as z.
          autorewrite with slow in z; simpl in z; allrw disjoint_singleton_l.
          repeat (autodimp z hyp); eauto 3 with slow;[].
          exrepnd.

          pose proof (ind t (subst t n (mk_utoken a')) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          fold_terms.
          apply q in z1; clear q; eauto 2 with wf;[].

          exrepnd.
          allrw; simpl.
          eexists; dands; eauto.
          unfold mk_fresh.
          repeat prove_alpha_eq4.
          apply alpha_eq_bterm_congr.

          eapply alpha_eq_trans in z0;[|apply alpha_eq_sym;exact z2].
          eapply alpha_eq_trans;
            [apply alpha_eq_subst_utokens;
             [eauto|apply alphaeq_utok_sub_refl] |].
          eapply alpha_eq_trans;
            [|apply alpha_eq_sym;apply alpha_eq_subst_utokens;
              [eauto|apply alphaeq_utok_sub_refl] ].

          eapply alpha_eq_trans;[apply simple_alphaeq_subst_utokens_subst;eauto 3 with slow|].
          eapply alpha_eq_trans;[|apply alpha_eq_sym;apply simple_alphaeq_subst_utokens_subst;eauto 4 with slow].
          auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.
      destruct e.

      * simpl.
        eapply found_entry_implies_compute_step_lib_success in comp0.
        unfold compute_step_lib in *; simpl; rewrite comp0.
        eexists; dands; eauto.

      * eexists; dands;
          [eapply found_entry_implies_compute_step_lib_success;
           apply found_entry_add_new_abs; eauto|].
        auto.
Qed.

Lemma reduces_to_consistent_with_new_definition {o} {lib} :
  forall (a b : @NTerm o)
         (wf  : wf_term a)
         (r   : reduces_to lib a b)
         (e   : library_entry)
         (p   : !in_lib (entry2name e) lib),
    {b' : NTerm & reduces_to (e :: lib) a b' # alpha_eq b b'}.
Proof.
  introv wf r p.
  allunfold @reduces_to; exrepnd.

  assert {k : nat
          & {b' : NTerm
          & reduces_in_atmost_k_steps (e :: lib) a b' k # alpha_eq b b'}};
    [|exrepnd; eauto];[].

  exists k.

  revert dependent a.
  induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists b; allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @compute_step_preserves_wf in comp1; auto.
    apply IHk in comp0; exrepnd; auto; clear IHk.
    apply (compute_step_consistent_with_new_definition e) in comp1; auto; exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha (e :: lib) u b'0) as w.
    repeat (autodimp w hyp); eauto 2 with wf.
    applydup w in comp0; clear w; exrepnd.

    eexists; dands;[rw @reduces_in_atmost_k_steps_S;eexists; dands; eauto|].
    eauto 2 with slow.
Qed.

Lemma matching_entry_sign_deq :
  forall oa1 oa2, decidable (matching_entry_sign oa1 oa2).
Proof.
  introv.
  unfold matching_entry_sign.
  destruct (String.string_dec (opabs_name oa1) (opabs_name oa2));
  try (complete (right; auto));
  destruct (opsign_dec (opabs_sign oa1) (opabs_sign oa2));
  try (complete (right; auto));
  remember (matching_parametersb (opabs_params oa1) (opabs_params oa2)) as m;
  destruct m;
  try (complete (right; intro k; repnd; tcsp;
                 unfold matching_parameters in k;
                 rw <- Heqm in k; inversion k));
  try (complete (right; auto)).
  left; dands; auto.
  unfold matching_parameters.
  rewrite <- Heqm; sp.
Defined.

Fixpoint found_entry_b {o} (lib : @library o) opabs (bs : list (@BTerm o)) : bool :=
  match lib with
  | [] => false
  | lib_cs _ _ :: l => found_entry_b l opabs bs
  | lib_abs oa vars rhs correct :: l =>
    if matching_entry_deq opabs oa vars bs
    then true
    else found_entry_b l opabs bs
  end.

Fixpoint found_entry_sign {o} (lib : @library o) name : bool :=
  match lib with
  | [] => false
  | entry :: entries =>
    if same_entry_name_dec name (entry2name entry) then true
    else found_entry_sign entries name
  end.

Definition get_all_abs_opid {o} (op : @Opid o) : OList opabs :=
  match op with
  | Abs abs => OLO abs
  | _ => onil
  end.

Fixpoint get_all_abs {o} (t : @NTerm o) : OList opabs :=
  match t with
  | vterm _ => onil
  | sterm f => OLS (fun n => get_all_abs (f n))
  | oterm op bs => oapp (get_all_abs_opid op) (OLL (map get_all_abs_b bs))
  end
with get_all_abs_b {o} (b : @BTerm o) : OList opabs :=
       match b with
       | bterm vs t => get_all_abs t
       end.

Definition all_abs_are_defined {o} (lib : @library o) (t : @NTerm o) : Prop :=
  forall opabs,
    in_olist opabs (get_all_abs t)
    -> found_entry_sign lib (entry_name_abs opabs) = true.

Definition all_abs_are_defined_cterm {o} lib (t : @CTerm o) : Prop :=
  all_abs_are_defined lib (get_cterm t).

(*
Inductive all_abstractions_are_defined {o} lib : @NTerm o -> Type :=
| all_abs_vterm : forall v, all_abstractions_are_defined lib (vterm v)
| all_abs_sterm :
    forall f,
      (forall n, all_abstractions_are_defined lib (f n))
      -> all_abstractions_are_defined lib (sterm f)
| all_abs_oterm :
    forall op bs,
      found_opid_in_library lib op bs = true
      -> (forall b, LIn b bs -> all_abstractions_are_defined_b lib b)
      -> all_abstractions_are_defined lib (oterm op bs)
with all_abstractions_are_defined_b {o} lib : @BTerm o -> Type :=
| all_abs_bterm :
    forall vs t,
      all_abstractions_are_defined lib t
      -> all_abstractions_are_defined_b lib (bterm vs t).
*)

Definition found_opid_in_library_sign {o} (lib : @library o) (op : @Opid o) : bool :=
  match op with
  | Abs abs => found_entry_sign lib (entry_name_abs abs)
  | _ => true
  end.

Fixpoint all_abstractions_are_defined {o} lib (t : @NTerm o) : obool :=
  match t with
  | vterm _ => otrue
  | sterm f => obseq (fun n => all_abstractions_are_defined lib (f n))
  | oterm op bs =>
    oband
      (bool2obool (found_opid_in_library_sign lib op))
      (oball (map (all_abstractions_are_defined_b lib) bs))
  end
with all_abstractions_are_defined_b {o} lib (b : @BTerm o) : obool :=
       match b with
       | bterm vs t => all_abstractions_are_defined lib t
       end.

Lemma all_abs_are_defined_eq {o} :
  forall lib (t : @NTerm o),
    all_abs_are_defined lib t
    <=> isotrue (all_abstractions_are_defined lib t).
Proof.
  nterm_ind t as [|f ind|op bs ind] Case; unfold all_abs_are_defined; simpl;
  split; introv h; auto.

  - Case "vterm".
    introv i.
    inversion i; subst; exrepnd; allsimpl; tcsp.

  - Case "sterm".
    introv.
    pose proof (ind n) as q; clear ind.
    apply q; auto.
    unfold all_abs_are_defined; introv i.
    apply h.
    constructor; eexists; eauto.

  - Case "sterm".
    introv i.
    inversion i as [| |F j]; subst; clear i; exrepnd.
    pose proof (h n) as q; clear h.
    apply ind in q; apply q; auto.

  - Case "oterm".
    apply isotrue_oband; dands.

    + apply isotrue_bool2obool_iff.
      dopid op as [can|ncan|exc|abs] SCase; allsimpl; auto.
      SCase "Abs".
      apply h.
      apply in_olist_oapp; left; eauto.

    + apply isotrue_oball_map; introv i.
      destruct x as [vs t]; allsimpl.
      pose proof (ind t vs) as q; clear ind.
      apply q; auto.
      introv j.
      apply h.
      apply in_olist_oapp.
      right.
      apply in_olist_OLL_map.
      eexists; dands; eauto.

  - Case "oterm".
    introv i.
    allrw isotrue_oband; repnd.
    allrw isotrue_oball_map.
    allrw isotrue_bool2obool_iff.
    apply in_olist_oapp in i.
    repndors.

    + destruct op; allsimpl; try (complete (inversion i; subst; tcsp)).

    + apply in_olist_OLL_map in i; exrepnd.
      destruct a as [l t]; allsimpl.
      applydup h in i1; allsimpl.
      pose proof (ind t l i1) as q.
      apply q in i2.
      apply i2; auto.
Qed.

Lemma isotrue_all_abstractions_are_defined_implies_eq_term2otrue {o} :
  forall lib (t : @NTerm o),
    isotrue (all_abstractions_are_defined lib t)
    -> all_abstractions_are_defined lib t = term2otrue t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; intro h; allsimpl; auto.

  - Case "sterm".
    f_equal.
    apply functional_extensionality.
    introv.
    pose proof (h x) as q.
    apply ind in q; auto.

  - Case "oterm".
    allrw isotrue_oband; repnd.
    allrw isotrue_oball_map.
    apply isotrue_bool2obool in h0.
    rewrite h0; simpl.
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    applydup h in i; allsimpl.
    pose proof (ind t l i) as q; apply q in i0; auto.
Qed.

Lemma oball_map_all_abstractions_are_defined_eq_implies {o} :
  forall lib (bs : list (@BTerm o)) b,
    oball (map (all_abstractions_are_defined_b lib) bs) = oball (map bterm2otrue bs)
    -> LIn b bs
    -> all_abstractions_are_defined_b lib b = bterm2otrue b.
Proof.
  introv e i.
  pose proof (isotrue_oball_map_bterm2otrue bs) as h.
  rewrite <- e in h; clear e.
  rw @isotrue_oball_map in h.
  applydup h in i.
  destruct b as [l t]; allsimpl.
  apply isotrue_all_abstractions_are_defined_implies_eq_term2otrue; auto.
Qed.

Lemma isotrue_all_abstractions_are_defined_if_eq_term2otrue {o} :
  forall lib (t : @NTerm o),
    all_abstractions_are_defined lib t = term2otrue t
    -> isotrue (all_abstractions_are_defined lib t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; intro h; allsimpl; auto.

  - Case "sterm".
    introv; apply ind.
    inversion h as [e]; clear h.
    eapply equal_f in e; eauto.

  - Case "oterm".
    remember (found_opid_in_library_sign lib op) as b; destruct b; allsimpl; auto;
    try (complete (symmetry in h; apply oball_map_bterm2otrue_not_ofalse in h; sp)).
    apply isotrue_oball_map; introv i.
    destruct x as [l t]; allsimpl.
    pose proof (ind t l i) as q; clear ind; apply q.
    eapply oball_map_all_abstractions_are_defined_eq_implies in h;[|eauto]; allsimpl; auto.
Qed.

Lemma isotrue_all_abstractions_are_defined_iff_eq_term2otrue {o} :
  forall lib (t : @NTerm o),
    isotrue (all_abstractions_are_defined lib t)
    <=>
    all_abstractions_are_defined lib t = term2otrue t.
Proof.
  introv; split; intro h.
  - apply isotrue_all_abstractions_are_defined_implies_eq_term2otrue; auto.
  - apply isotrue_all_abstractions_are_defined_if_eq_term2otrue; auto.
Qed.

Definition all_abstractions_are_defined_cterm {o} lib (t : @CTerm o) : obool :=
  all_abstractions_are_defined lib (get_cterm t).

Definition all_abstractions_are_defined_sub {o} lib (sub : @Sub o) : obool :=
  oball (map (all_abstractions_are_defined lib) (range sub)).

Lemma isotrue_all_abstractions_are_defined_sub_iff {o} :
  forall lib (sub : @Sub o),
    isotrue (all_abstractions_are_defined_sub lib sub)
    <=> (forall v t, LIn (v,t) sub -> isotrue (all_abstractions_are_defined lib t)).
Proof.
  introv.
  unfold all_abstractions_are_defined_sub.
  rw isotrue_oball_map; split; introv h; introv i.
  - apply h.
    apply in_sub_eta in i; tcsp.
  - apply in_range in i; exrepnd; eauto.
Qed.

Definition all_abstractions_are_defined_utok_sub {o} lib (sub : @utok_sub o) : obool :=
  oball (map (all_abstractions_are_defined lib) (utok_sub_range sub)).

Lemma isotrue_all_abstractions_are_defined_utok_sub_iff {o} :
  forall lib (sub : @utok_sub o),
    isotrue (all_abstractions_are_defined_utok_sub lib sub)
    <=> (forall a t, LIn (a,t) sub -> isotrue (all_abstractions_are_defined lib t)).
Proof.
  introv.
  unfold all_abstractions_are_defined_utok_sub.
  rw isotrue_oball_map; split; introv h; introv i.
  - apply h.
    apply in_utok_sub_eta in i; tcsp.
  - unfold utok_sub_range in i; apply in_map_iff in i; exrepnd; allsimpl; subst.
    eapply h; eauto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_sub_sub_filter {o} :
  forall lib (sub : @Sub o) l,
    isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined_sub lib (sub_filter sub l)).
Proof.
  introv i.
  allrw @isotrue_all_abstractions_are_defined_sub_iff.
  introv j.
  apply in_sub_filter in j; repnd.
  eapply i; eauto.
Qed.
Hint Resolve implies_isotrue_all_abstractions_are_defined_sub_sub_filter : slow.

Lemma implies_isotrue_all_abstractions_are_defined_lsubst_aux {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (lsubst_aux t sub)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv isot isos; allsimpl; tcsp.

  - Case "vterm".
    remember (sub_find sub v) as p; destruct p; symmetry in Heqp; simpl; auto.

    apply sub_find_some in Heqp.
    rw @isotrue_all_abstractions_are_defined_sub_iff in isos.
    eapply isos; eauto.

  - Case "oterm".
    allrw isotrue_oband.
    rw isotrue_oball_map in isot; repnd.
    rw isotrue_oball_map.
    dands; auto.
    introv i.
    allrw in_map_iff; exrepnd; subst.
    destruct a as [l t]; allsimpl.
    pose proof (ind t t l) as q; clear ind.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q (sub_filter sub l)) as h; clear q.
    repeat (autodimp h hyp); eauto 3 with slow;[].
    apply isot in i1; allsimpl; auto.
Qed.

Hint Rewrite @osize_cswap : slow.
Hint Rewrite @sosize_so_swap : slow.
Hint Rewrite oband_otrue : slow.

Lemma oband_assoc :
  forall (o1 o2 o3 : obool),
    oband (oband o1 o2) o3 = oband o1 (oband o2 o3).
Proof.
  induction o1 as [|?|? ind]; introv; simpl; auto;[].
  destruct o2; simpl; auto;[].
  destruct o3; simpl; auto.
  f_equal.
  apply functional_extensionality.
  introv; auto.
Qed.

Lemma all_abstractions_are_defined_preserves_cswap {o} :
  forall lib (t : @NTerm o) sw,
    all_abstractions_are_defined lib (cswap sw t)
    = all_abstractions_are_defined lib t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; allsimpl; introv; tcsp.

  Case "oterm".
  f_equal.
  f_equal.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t]; allsimpl.
  eapply ind; eauto 3 with slow.
Qed.
Hint Rewrite @all_abstractions_are_defined_preserves_cswap : slow.

Lemma all_abstractions_are_defined_apply_list {o} :
  forall lib ts (t : @NTerm o),
    all_abstractions_are_defined lib (apply_list t ts)
    = oband (all_abstractions_are_defined lib t)
            (oball (map (all_abstractions_are_defined lib) ts)).
Proof.
  induction ts; simpl; introv; autorewrite with slow; auto.
  rewrite IHts; simpl.
  rewrite oband_assoc; autorewrite with slow; auto.
Qed.

Definition all_abstractions_are_defined_so {o} lib (t : @SOTerm o) :=
  all_abstractions_are_defined lib (soterm2nterm t).

Lemma all_abstractions_are_defined_so_preserves_so_swap {o} :
  forall lib (t : @SOTerm o) sw,
    all_abstractions_are_defined_so lib (so_swap sw t)
    = all_abstractions_are_defined_so lib t.
Proof.
  soterm_ind1s t as [v ts ind|f ind|op bs ind] Case; allsimpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; unfold all_abstractions_are_defined_so; simpl; auto.
    repeat (rewrite all_abstractions_are_defined_apply_list); simpl.
    repeat (rewrite map_map); unfold compose; simpl.
    f_equal.
    apply eq_maps; introv i; simpl.
    apply ind; auto.

  - Case "soterm".
    unfold all_abstractions_are_defined_so; simpl.
    f_equal; f_equal.
    repeat (rewrite map_map); unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    eapply ind; eauto 3 with slow.
Qed.
Hint Rewrite @all_abstractions_are_defined_so_preserves_so_swap : slow.

Lemma all_abstractions_are_defined_preserves_alphaeq {o} :
  forall lib (t u : @NTerm o),
    alphaeq t u
    -> all_abstractions_are_defined lib t = all_abstractions_are_defined lib u.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; allsimpl; introv aeq.

  - Case "vterm".
    inversion aeq; subst; simpl; auto.

  - Case "sterm".
    inversion aeq as [|? g q|]; subst; simpl.
    f_equal.
    apply functional_extensionality; introv.
    apply ind; auto; clear ind.
    apply q.

  - Case "oterm".
    apply alphaeq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    f_equal.
    f_equal.
    apply eq_maps3; auto.
    introv i.
    applydup aeq0 in i.
    destruct a as [l1 t1].
    destruct c as [l2 t2].
    allsimpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep aeq]; allsimpl; subst; clear i0.
    applydup in_combine in i; repnd.
    pose proof (ind t1 (cswap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    autorewrite with slow in *.
    repeat (autodimp h hyp); eauto 3 with slow.
    apply h in aeq.
    autorewrite with slow in *; auto.
Qed.

Lemma all_abstractions_are_defined_so_preserves_so_alphaeq {o} :
  forall lib (t u : @SOTerm o),
    so_alphaeq t u
    -> all_abstractions_are_defined_so lib t = all_abstractions_are_defined_so lib u.
Proof.
  soterm_ind1s t as [v ts ind|f ind|op bs ind] Case; allsimpl; introv aeq.

  - Case "sovar".
    inversion aeq as [? ? ? len imp| |]; subst; simpl; auto; clear aeq.
    unfold all_abstractions_are_defined_so; simpl; auto.
    allrw @all_abstractions_are_defined_apply_list.
    f_equal; f_equal.
    allrw map_map; unfold compose.
    apply eq_maps3; auto.
    introv i.
    applydup imp in i.
    apply ind; auto.
    apply in_combine in i; sp.

  - Case "soseq".
    inversion aeq as [|? g q|]; subst; simpl.
    unfold all_abstractions_are_defined_so; simpl.
    f_equal.
    apply functional_extensionality; introv.
    apply all_abstractions_are_defined_preserves_alphaeq.
    apply q.

  - Case "soterm".
    inversion aeq as [| |? ? ? len imp]; subst; clear aeq.
    unfold all_abstractions_are_defined_so; simpl.
    f_equal; f_equal.
    repeat (rewrite map_map); unfold compose.
    apply eq_maps3; auto.
    introv i.
    applydup imp in i.
    destruct a as [l1 t1].
    destruct c as [l2 t2].
    allsimpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep aeq]; allsimpl; subst; clear i0.
    applydup in_combine in i; repnd.
    pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    autorewrite with slow in *.
    repeat (autodimp h hyp); eauto 3 with slow.
    apply h in aeq.
    autorewrite with slow in *; auto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_lsubst {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (lsubst t sub)).
Proof.
  introv isot isos.
  pose proof (unfold_lsubst sub t) as q; exrepnd.
  rewrite q0.
  apply implies_isotrue_all_abstractions_are_defined_lsubst_aux; auto.
  erewrite all_abstractions_are_defined_preserves_alphaeq; eauto.
  apply alphaeq_sym; auto.
  apply alphaeq_eq; auto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_subst {o} :
  forall lib (t : @NTerm o) x u,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined lib u)
    -> isotrue (all_abstractions_are_defined lib (subst t x u)).
Proof.
  introv isot isou.
  apply implies_isotrue_all_abstractions_are_defined_lsubst; auto.
  apply isotrue_all_abstractions_are_defined_sub_iff; simpl; introv i.
  repndors; ginv; tcsp.
Qed.

Lemma isotrue_all_abstractions_are_defined_oterm {o} :
  forall lib op (bs : list (@BTerm o)),
    isotrue (all_abstractions_are_defined lib (oterm op bs))
    <=> (found_opid_in_library_sign lib op = true
         # forall b, LIn b bs -> isotrue (all_abstractions_are_defined_b lib b)).
Proof.
  introv; simpl.
  rw isotrue_oband.
  rw isotrue_oball_map.
  remember (found_opid_in_library_sign lib op) as b; destruct b; simpl; split; tcsp.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_subst_utokens_aux {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_utok_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (subst_utokens_aux t sub)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
  introv isot isos; tcsp.
  Case "oterm".
  rewrite subst_utokens_aux_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

  - apply get_utok_some in Heqguo; subst; allsimpl.
    unfold subst_utok; simpl.
    remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf.

    + rw @isotrue_all_abstractions_are_defined_utok_sub_iff in isos.
      apply utok_sub_find_some in Heqsf; auto.
      eapply isos; eauto.

    + simpl.
      rewrite map_map; unfold compose.
      apply isotrue_oball_map; introv i.
      destruct x as [l t]; simpl.
      pose proof (ind t t l) as q; clear ind.
      repeat (autodimp q hyp); eauto 2 with slow.
      apply q; auto.
      rw isotrue_oball_map in isot.
      apply isot in i; auto.

  - allrw @isotrue_all_abstractions_are_defined_oterm; repnd; dands; auto.
    introv i.
    allrw in_map_iff; exrepnd; subst; allsimpl.
    destruct a as [l t]; allsimpl.
    pose proof (ind t t l) as q; clear ind.
    repeat (autodimp q hyp); eauto 2 with slow.
    apply q; auto.
    apply isot in i1; auto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_subst_utokens {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_utok_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (subst_utokens t sub)).
Proof.
  introv isot isos.
  pose proof (unfold_subst_utokens sub t) as q; exrepnd.
  rewrite q0.
  apply implies_isotrue_all_abstractions_are_defined_subst_utokens_aux; auto.
  erewrite all_abstractions_are_defined_preserves_alphaeq; eauto.
  apply alphaeq_sym; auto.
  apply alphaeq_eq; auto.
Qed.

Lemma implies_osubset_OLL_cons {T} :
  forall x1 x2 (l1 l2 : list (OList T)),
    osubset x1 x2
    -> osubset (OLL l1) (OLL l2)
    -> osubset (OLL (x1 :: l1)) (OLL (x2 :: l2)).
Proof.
  introv o1 o2 i.
  allrw @in_olist_OLL_cons; repndors; tcsp.
Qed.

Lemma osubset_OLL_singleton_r {T} :
  forall (s1 s2 : OList T),
    osubset s1 (OLL [s2]) <=> osubset s1 s2.
Proof.
  introv; split; introv h i; apply h in i; clear h.
  - inversion i; subst; clear i; exrepnd; allsimpl; repndors; tcsp; subst; auto.
  - constructor; simpl; eexists; dands; eauto.
Qed.

Lemma osubset_OLL_singleton_l {T} :
  forall (s1 s2 : OList T),
    osubset (OLL [s1]) s2 <=> osubset s1 s2.
Proof.
  introv; split; introv h i; apply h; clear h.
  - constructor; simpl; eexists; dands; eauto.
  - inversion i; subst; clear i; exrepnd; allsimpl; repndors; tcsp; subst; auto.
Qed.

(*Lemma compute_step_preseves_get_all_abs {o} :
  forall lib (t : @NTerm o) u,
    compute_step lib t = csuccess u
    -> osubset (get_all_abs u) (get_all_abs t).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; eauto 2 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; eauto 2 with slow.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [v|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst.
            allsimpl; eauto 2 with slow.
          }

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst; auto.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv; auto.
              allsimpl; autorewrite with slow.
              apply implies_osubset_oapp_right.
              eapply osubset_in_trans; simpl;[|left;eauto].
              eapply implies_osubset_singleton_OLS_r; eauto 2 with slow.

            + apply implies_osubset_oapp_right.
              eapply osubset_in_trans; simpl;[apply osubset_refl|]; tcsp.

            + allsimpl.
              apply osubset_oapp_if; eauto 3 with slow.
              apply implies_osubset_OLL_cons; eauto 3 with slow.
              apply implies_osubset_OLL_cons; eauto 3 with slow.
              eapply ind;[right;left;reflexivity| |]; eauto 2 with slow.
          }

          {
            SSCase "NFix".
            apply compute_step_fix_success in comp; exrepnd; subst.
            allsimpl.
            apply osubset_oapp_if; eauto 3 with slow.
            rw @osubset_OLL_singleton_r.
            apply osubset_singleton_OLL_l; simpl; introv i;
            repndors; tcsp; subst; eauto 3 with slow.
          }

          {
            SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl; auto.
            apply implies_isotrue_all_abstraction_are_defined_subst.
            - apply (allabs (bterm [v] x)); tcsp.
            - apply (allabs (nobnd (sterm f))); tcsp.
          }

          {
            SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            introv i; repndors; subst; tcsp; try (complete (apply allabs; tcsp)).
          }

          {
            SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst.
            apply (allabs (nobnd b)); tcsp.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.

              - apply implies_isotrue_all_abstraction_are_defined_subst;
                try (apply (allabs (nobnd arg)); tcsp).
                pose proof (allabs (nobnd (mk_lam v b))) as q.
                autodimp q hyp.
                allsimpl; autorewrite with slow in *; auto.

              - apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto.

                + unfold mk_nseq in *; allsimpl; ginv.@136
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q.
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - rewrite compute_step_fresh_if_isnoncan_like; auto.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.
          rewrite comp2; simpl; auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.
      destruct e.
      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).

      apply found_entry_add_new_abs; auto.
Qed.*)

Lemma matching_entry_implies_sign {o} :
  forall abs oa vars (bts : list (@BTerm o)),
    matching_entry abs oa vars bts
    -> matching_entry_sign abs oa.
Proof.
  introv m.
  unfold matching_entry in m.
  unfold matching_entry_sign; sp.
Qed.
Hint Resolve matching_entry_implies_sign : slow.

Lemma found_entry_implies_sign {o} :
  forall lib abs bts oa vars (rhs : @SOTerm o) correct,
    found_entry lib abs bts oa vars rhs correct
    -> found_entry_sign lib (entry_name_abs abs) = true.
Proof.
  introv fe.
  unfold found_entry in fe.
  unfold find_entry.
  induction lib; allsimpl; tcsp.
  destruct a; simpl in *; tcsp;[].

  boolvar; tcsp; ginv.
  inversion fe; clear fe; subst.
  destruct (matching_entry_sign_deq abs oa); auto.
  apply matching_entry_implies_sign in m; tcsp.
Qed.
Hint Resolve found_entry_implies_sign : slow.

Lemma all_abstractions_are_defined_pushdown_fresh {o} :
  forall lib n (t : @NTerm o),
    all_abstractions_are_defined lib (pushdown_fresh n t)
    = all_abstractions_are_defined lib t.
Proof.
  introv.
  destruct t; allsimpl; auto.
  f_equal; f_equal.
  unfold mk_fresh_bterms.
  rw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [vs t].
  simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @all_abstractions_are_defined_pushdown_fresh : slow.

Definition all_abstractions_are_defined_sosub {o} lib (sub : @SOSub o) : obool :=
  oball (map (fun x => all_abstractions_are_defined lib (sosk_t (snd x))) sub).

Lemma isotrue_all_abstractions_are_defined_sosub_iff {o} :
  forall lib (sub : @SOSub o),
    isotrue (all_abstractions_are_defined_sosub lib sub)
    <=> (forall v t, LIn (v,t) sub -> isotrue (all_abstractions_are_defined lib (sosk_t t))).
Proof.
  introv.
  unfold all_abstractions_are_defined_sosub.
  rw isotrue_oball_map; split; introv h; introv i.
  - pose proof (h (v,t)) as q; allsimpl; tcsp.
  - destruct x; simpl.
    eapply h; eauto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_sosub_sub_filter {o} :
  forall lib (sub : @SOSub o) l,
    isotrue (all_abstractions_are_defined_sosub lib sub)
    -> isotrue (all_abstractions_are_defined_sosub lib (sosub_filter sub l)).
Proof.
  introv i.
  allrw @isotrue_all_abstractions_are_defined_sosub_iff.
  introv j.
  destruct t.
  apply in_sosub_filter in j; repnd.
  eapply i; eauto.
Qed.
Hint Resolve implies_isotrue_all_abstractions_are_defined_sosub_sub_filter : slow.

Lemma implies_isotrue_all_abstractions_are_defined_sosub_aux {o} :
  forall lib (t : @SOTerm o) sub,
    isotrue (all_abstractions_are_defined_so lib t)
    -> isotrue (all_abstractions_are_defined_sosub lib sub)
    -> isotrue (all_abstractions_are_defined lib (sosub_aux sub t)).
Proof.
  soterm_ind1s t as [v ts ind|f ind|op bs ind] Case;
  introv isot isos; allsimpl; auto.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as sf; symmetry in Heqsf; destruct sf; allsimpl.

    + destruct s.
      apply implies_isotrue_all_abstractions_are_defined_lsubst_aux; auto.

      * apply sosub_find_some in Heqsf; repnd.
        rw @isotrue_all_abstractions_are_defined_sosub_iff in isos.
        pose proof (isos v (sosk l n)) as h; autodimp h hyp.

      * apply isotrue_all_abstractions_are_defined_sub_iff; introv i.
        apply in_combine in i; repnd.
        apply in_map_iff in i; exrepnd; subst.
        eapply ind in i2; eauto.
        unfold all_abstractions_are_defined_so in isot; allsimpl.
        rewrite all_abstractions_are_defined_apply_list in isot.
        allrw isotrue_oband; repnd.
        allrw isotrue_oball_map; allsimpl.
        apply isot.
        apply in_map_iff; eexists; dands; eauto.

    + unfold all_abstractions_are_defined_so in isot; allsimpl.
      allrw @all_abstractions_are_defined_apply_list.
      allrw isotrue_oband; repnd; dands; auto.
      rewrite map_map; unfold compose.
      apply isotrue_oball_map; introv i.
      rw @isotrue_oball_map in isot.
      eapply ind in i; eauto.
      apply isot.
      apply in_map_iff; eexists; dands; eauto.

  - Case "soterm".
    allrw isotrue_oband; repnd; dands; auto.
    rewrite map_map; unfold compose; simpl.
    apply isotrue_oball_map; introv i.
    rw @isotrue_oball_map in isot.
    destruct x as [l t]; allsimpl.
    eapply ind; eauto 3 with slow.
    apply (isot (bterm l (soterm2nterm t))).
    apply in_map_iff; eexists; dands; eauto.
Qed.

Hint Rewrite @sosize_so_swap : slow.

Lemma cswap_apply_list {o} :
  forall sw ts (t : @NTerm o),
    cswap sw (apply_list t ts)
    = apply_list (cswap sw t) (map (cswap sw) ts).
Proof.
  induction ts; introv; allsimpl; auto.
  rewrite IHts; simpl; fold_terms; auto.
Qed.

Lemma all_abstractions_are_defined_sosub_preserves_alphaeq_sosub {o} :
  forall lib (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> all_abstractions_are_defined_sosub lib sub1
       = all_abstractions_are_defined_sosub lib sub2.
Proof.
  induction sub1; introv aeq.
  - inversion aeq; subst; auto.
  - inversion aeq as [|? ? ? ? ? aeq1 aeq2]; subst; clear aeq.
    unfold all_abstractions_are_defined_sosub; simpl.
    f_equal.
    + destruct sk1, sk2; simpl.
      apply alphaeq_sk_iff_alphaeq_bterm in aeq1.
      inversion aeq1 as [? ? ? ? ? len1 len2 disj norep aeq]; allsimpl; subst; clear aeq1.
      apply (all_abstractions_are_defined_preserves_alphaeq lib) in aeq.
      autorewrite with slow in *; auto.
    + apply IHsub1; auto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_sosub {o} :
  forall lib (t : @SOTerm o) sub,
    isotrue (all_abstractions_are_defined_so lib t)
    -> isotrue (all_abstractions_are_defined_sosub lib sub)
    -> isotrue (all_abstractions_are_defined lib (sosub sub t)).
Proof.
  introv isot isos.
  pose proof (unfold_sosub sub t) as q; exrepnd.
  rewrite q1; clear q1.
  apply implies_isotrue_all_abstractions_are_defined_sosub_aux; auto.
  - erewrite all_abstractions_are_defined_so_preserves_so_alphaeq;[eauto|].
    apply so_alphaeq_sym; auto.
  - apply (all_abstractions_are_defined_sosub_preserves_alphaeq_sosub lib) in q0.
    rewrite <- q0; auto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_mk_instance {o} :
  forall lib vars bs (t : @SOTerm o),
    isotrue (all_abstractions_are_defined_so lib t)
    -> (forall b : BTerm, LIn b bs -> isotrue (all_abstractions_are_defined_b lib b))
    -> isotrue (all_abstractions_are_defined lib (mk_instance vars bs t)).
Proof.
  introv isot isobs.
  unfold mk_instance.
  apply implies_isotrue_all_abstractions_are_defined_sosub; auto.
  unfold all_abstractions_are_defined_sosub.
  apply isotrue_oball_map; introv i.
  destruct x as [v sk]; allsimpl.
  destruct sk as [l u]; allsimpl.
  apply (isobs (bterm l u)).
  apply mk_abs_subst_some_prop1 in i; auto.
Qed.

Definition no_undefined_abs_in_entry {o} lib (entry : @library_entry o) :=
  match entry with
  | lib_cs _ _ => False
  | lib_abs opabs vars rhs correct =>
    isotrue (all_abstractions_are_defined_so lib rhs)
  end.

(* entries can only depend on earlier abstractions, i.e., on the right in the list *)
Fixpoint no_undefined_abs_in_lib {o} (lib : @library o) :=
  match lib with
  | [] => True
  | entry :: entries =>
    no_undefined_abs_in_lib entries
    # no_undefined_abs_in_entry entries entry
  end.

(*
Definition entry2soterm {o} (entry : @library_entry o) : @SOTerm o :=
  match entry with
  | lib_abs opabs vars rhs correct => rhs
  end.

Definition simple_no_undefined_abs_in_lib {o} (lib : @library o) :=
  forall entry,
    LIn entry lib
    -> isotrue (all_abstractions_are_defined_so lib (entry2soterm entry)).

Lemma compute_step_preserves_all_abstractions_are_defined {o} :
  forall lib,
    simple_no_undefined_abs_in_lib lib
    -> forall (t : @NTerm o) u,
      compute_step lib t = csuccess u
      -> isotrue (all_abstractions_are_defined lib t)
      -> isotrue (all_abstractions_are_defined lib u).
Proof.
  introv undef; nterm_ind1s t as [v|f ind|op bs ind] Case; introv comp allabs.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; auto.

  - Case "oterm".
    apply isotrue_all_abstractions_are_defined_oterm in allabs; repnd.
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; auto.
      apply isotrue_all_abstractions_are_defined_oterm; auto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; auto.
          }

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst; auto.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv; auto.
              apply (allabs (nobnd (sterm f0))); tcsp.

            + apply (allabs (nobnd arg2)); tcsp.

            + fold_terms.
              apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
              introv i; repndors; subst; try (complete (apply allabs; tcsp)).
              allsimpl.
              pose proof (ind arg2 arg2 []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              apply h in comp1; auto; try (complete (apply (allabs (nobnd arg2)); tcsp)).
          }

          {
            SSCase "NFix".
            apply compute_step_fix_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            introv i; repndors; subst; try (complete (apply allabs; tcsp)).
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
          }

          {
            SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl; auto.
            apply implies_isotrue_all_abstractions_are_defined_subst.
            - apply (allabs (bterm [v] x)); tcsp.
            - apply (allabs (nobnd (sterm f))); tcsp.
          }

          {
            SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            introv i; repndors; subst; tcsp; try (complete (apply allabs; tcsp)).
          }

          {
            SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst.
            apply (allabs (nobnd b)); tcsp.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.

              - apply implies_isotrue_all_abstractions_are_defined_subst;
                try (apply (allabs (nobnd arg)); tcsp).
                pose proof (allabs (nobnd (mk_lam v b))) as q.
                autodimp q hyp.
                allsimpl; autorewrite with slow in *; auto.

              - apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.
                unfold mk_lam in *; ginv; fold_terms.
                apply implies_isotrue_all_abstractions_are_defined_subst; auto; simpl;
                try (apply (allabs (nobnd arg2)); tcsp).
                pose proof (allabs (nobnd (mk_lam v b))) as q.
                autodimp q hyp.
                allsimpl; autorewrite with slow in *; auto.

              - apply (allabs (nobnd arg2)); auto.

              - allrw isotrue_oband.
                dands; auto.

                + apply (allabs (nobnd (oterm (Can can2) bts))); tcsp.

                + pose proof (ind arg2 arg2 []) as q; clear ind.
                  repeat (autodimp q hyp); eauto 2 with slow.
                  apply q in comp1; clear q; auto.
                  apply (allabs (nobnd arg2)); auto.

                + apply isotrue_oball_map; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl; GC.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
              simpl.
              allrw isotrue_oband.
              dands; simpl; auto; apply (allabs (nobnd (oterm (Can can2) bts))); tcsp.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
              apply implies_isotrue_all_abstractions_are_defined_lsubst; auto; simpl.
              try (apply (allabs (bterm [va,vb] arg)); tcsp).
              apply isotrue_all_abstractions_are_defined_sub_iff.

              simpl; introv i; repndors; ginv; tcsp.

              - pose proof (allabs (nobnd (mk_pair t b))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.

              - pose proof (allabs (nobnd (mk_pair a t))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto; GC.
              apply implies_isotrue_all_abstractions_are_defined_lsubst; auto; simpl.
              try (apply (allabs (bterm [va,vb] arg)); tcsp).
              apply isotrue_all_abstractions_are_defined_sub_iff.

              simpl; introv i; repndors; ginv; tcsp.

              - pose proof (allabs (nobnd (mk_sup t b))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.

              - pose proof (allabs (nobnd (mk_sup a t))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto; GC.

              repndors; exrepnd; subst; auto;
              apply implies_isotrue_all_abstractions_are_defined_subst; auto; simpl;
              try (apply (allabs (bterm [v1] t1)); tcsp);
              try (apply (allabs (bterm [v2] t2)); tcsp).

              - pose proof (allabs (nobnd (mk_inl d))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.

              - pose proof (allabs (nobnd (mk_inr d))) as q; autodimp q hyp.
                allsimpl.
                allrw isotrue_oband; tcsp.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto; GC.
              apply implies_isotrue_all_abstractions_are_defined_subst; auto; simpl;
              try (apply (allabs (bterm [v] x)); tcsp).

              pose proof (allabs (nobnd (oterm (Can can2) bts))) as q.
              autodimp q hyp.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; simpl; auto.
              allrw isotrue_oband; allsimpl; dands; tcsp;
              try (apply (allabs (bterm [] a)); tcsp).

              pose proof (allabs (nobnd (oterm (Can can2) bts))) as q.
              autodimp q hyp.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; GC.

              - apply compute_step_compop_success_can_can in comp1;
                repndors; exrepnd; subst; ginv;
                repndors; exrepnd; subst; allsimpl; boolvar;
                try (apply (allabs (nobnd t0)); tcsp);
                try (apply (allabs (nobnd t3)); tcsp).

              - pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allsimpl.
                apply q in comp4; clear q;
                try (apply (allabs (nobnd t)); tcsp).
                allrw isotrue_oband; dands; auto.

                + pose proof (allabs (nobnd (oterm (Can can2) bts))) as q.
                  autodimp q hyp.

                + apply isotrue_oball_map; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; allsimpl.
                pose proof (allabs (nobnd (oterm Exc l))) as q; autodimp q hyp.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - apply compute_step_arithop_success_can_can in comp1;
                repndors; exrepnd; subst; ginv; simpl; auto.

              - pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allsimpl.
                apply q in comp4; clear q;
                try (apply (allabs (nobnd t)); tcsp).
                allrw isotrue_oband; dands; auto.

                + pose proof (allabs (nobnd (oterm (Can can2) bts))) as q.
                  autodimp q hyp.

                + apply isotrue_oball_map; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; allsimpl.
                pose proof (allabs (nobnd (oterm Exc l))) as q; autodimp q hyp.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto; GC.
              allsimpl.
              destruct (canonical_form_test_for c can2) as [d|d];
                try (apply (allabs (nobnd arg2nt)); tcsp);
                try (apply (allabs (nobnd arg3nt)); tcsp).
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q;
            try (apply (allabs (nobnd (oterm (NCan ncan2) bts))); tcsp).
            simpl.
            allrw isotrue_oband; dands; tcsp.
            apply isotrue_oball_map; auto.

          + SSCase "Exc".

            csunf comp; allsimpl; GC.
            apply compute_step_catch_success in comp.

            pose proof (allabs (nobnd (oterm Exc bts))) as q.
            autodimp q hyp; allsimpl.

            repndors; exrepnd; subst; allsimpl; ginv;
            allrw isotrue_oband; allsimpl; repnd; dands; auto;
            try (apply (allabs (nobnd a)); tcsp).

            apply implies_isotrue_all_abstractions_are_defined_subst; simpl; auto;
            try (apply (allabs (bterm [v] b)); tcsp).

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; allsimpl; allrw isotrue_oband; dands; auto.

            * apply isotrue_oball_map; auto.

            * apply isotrue_bool2obool_iff.
              csunf Heqc.
              unfold compute_step_unfold in Heqc.
              apply compute_step_lib_success in Heqc; exrepnd; subst; eauto 2 with slow.

            * pose proof (allabs (nobnd (oterm (Abs abs2) bts))) as q; autodimp q hyp.
              allsimpl; allrw isotrue_oband; tcsp.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; allsimpl; ginv;
        autorewrite with slow in *.

        - apply (allabs (bterm [n] t)); auto.

        - pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.

          + apply implies_isotrue_all_abstractions_are_defined_subst_utokens; simpl; auto.

          + apply implies_isotrue_all_abstractions_are_defined_subst; simpl; auto.
            apply (allabs (bterm [n] t)); auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.
      simpl.
      apply isotrue_oball_map; auto.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      apply implies_isotrue_all_abstractions_are_defined_mk_instance; auto.

      pose proof (undef (lib_abs oa2 vars rhs correct)) as q; allsimpl; apply q; clear q.
      eapply found_entry_in; eauto.
Qed.

Lemma reduces_to_preserves_all_abstractions_are_defined {o} :
  forall lib,
    simple_no_undefined_abs_in_lib lib
    -> forall (t : @NTerm o) u,
      reduces_to lib t u
      -> isotrue (all_abstractions_are_defined lib t)
      -> isotrue (all_abstractions_are_defined lib u).
Proof.
  introv undef r iso.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv r iso.

  - rw @reduces_in_atmost_k_steps_0 in r; subst; auto.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    apply compute_step_preserves_all_abstractions_are_defined in r1; auto.
    apply IHk in r0; auto.
Qed.

Lemma computes_to_value_preserves_all_abstractions_are_defined {o} :
  forall lib,
    simple_no_undefined_abs_in_lib lib
    -> forall (t : @NTerm o) u,
      computes_to_value lib t u
      -> isotrue (all_abstractions_are_defined lib t)
      -> isotrue (all_abstractions_are_defined lib u).
Proof.
  introv undef comp iso.
  unfold computes_to_value in comp; repnd.
  apply reduces_to_preserves_all_abstractions_are_defined in comp0; auto.
Qed.

Lemma computes_to_valc_preserves_all_abstractions_are_defined {o} :
  forall lib,
    simple_no_undefined_abs_in_lib lib
    -> forall (t : @CTerm o) u,
      computes_to_valc lib t u
      -> isotrue (all_abstractions_are_defined_cterm lib t)
      -> isotrue (all_abstractions_are_defined_cterm lib u).
Proof.
  introv undef comp iso.
  destruct_cterms.
  unfold computes_to_valc in comp; allsimpl.
  allunfold @all_abstractions_are_defined_cterm; allsimpl.
  apply computes_to_value_preserves_all_abstractions_are_defined in comp; auto.
Qed.
 *)

Fixpoint find_entry_sign {o} (lib : @library o) name : option library_entry :=
  match lib with
  | [] => None
  | entry :: entries =>
    if same_entry_name_dec name (entry2name entry) then Some entry
    else find_entry_sign entries name
  end.

Definition libraries_agree_on_intersection {o} (lib1 lib2 : @library o) : Type :=
  forall name,
    match find_entry_sign lib1 name, find_entry_sign lib2 name with
    | Some (lib_abs opabs1 vars1 rhs1 correct1),
      Some (lib_abs opabs2 vars2 rhs2 correct2) =>
      opabs1 = opabs2 # vars1 = vars2 # rhs1 = rhs2 (* could use alpha_eq_entry instead *)

    | Some (lib_cs name1 entry1), Some (lib_cs name2 entry2) =>
      name1 = name2 # entry1 = entry2

    | Some _, Some _ => False

    | _, _ => True
    end.

Lemma matching_sign_dec :
  forall (vars : list sovar_sig) (sign : opsign),
    decidable (matching_sign vars sign).
Proof.
  introv.
  unfold matching_sign, decidable.
  destruct (opsign_dec (map (fun v : NVar # nat => snd v) vars) sign); tcsp.
Defined.

Definition wf_entry {o} (e : @library_entry o) : bool :=
  match e with
  | lib_cs _ _ => true
  | lib_abs opabs vars rhs correct =>
    if matching_sign_dec vars (opabs_sign opabs) then true else false
  end.

Definition wf_library {o} (lib : @library o) : bool :=
  ball (map wf_entry lib).

Lemma matching_bterms_as_matching_sign {o} :
  forall vars (bs : list (@BTerm o)),
    matching_bterms vars bs
    <=> matching_sign vars (map num_bvars bs).
Proof.
  sp.
Qed.

Lemma wf_abs_implies {o} :
  forall abs (bs : list (@BTerm o)),
    wf_term (oterm (Abs abs) bs)
    -> opabs_sign abs = map num_bvars bs.
Proof.
  introv wf.
  apply wf_term_eq in wf.
  inversion wf; auto.
Qed.

(*Lemma found_entry_iff_sign {o} :
  forall (lib : @library o) opabs bs oa vars rhs correct,
    opabs_sign opabs = map num_bvars bs (* i.e., wf_term (oterm (Abs opabs) bs) *)
    -> assert (wf_library lib)
    -> (found_entry lib opabs bs oa vars rhs correct
        <=> find_entry_sign lib opabs = Some (lib_abs oa vars rhs correct)).
Proof.
  induction lib; introv wfa wfl; unfold found_entry; introv; simpl; split; intro h; ginv.

  - destruct a; tcsp.

    { eapply IHlib; eauto. }

    unfold wf_library in wfl; allsimpl; allrw assert_andb; repnd.
    boolvar; auto; try (complete (allunfold assert; ginv)).

    + unfold not_matching_entry in n.
      unfold matching_entry_sign in m; repnd.
      repndors; tcsp.
      rw @matching_bterms_as_matching_sign in n.
      destruct n.
      allunfold matching_sign; rewrite m0.
      rewrite <- m2; auto.

    + inversion h; clear h; subst.
      apply matching_entry_implies_sign in m; sp.

    + pose proof (IHlib opabs bs oa vars rhs correct wfa wfl) as q; clear IHlib.
      apply q; auto.

  - destruct a.

    { eapply IHlib; eauto. }

    unfold wf_library in wfl; allsimpl; allrw assert_andb; repnd.
    boolvar; auto; try (complete (allunfold assert; ginv)).

    + apply matching_entry_implies_sign in m; sp.

    + inversion h; clear h; subst.
      unfold not_matching_entry in n.
      unfold matching_entry_sign in m; repnd.
      repndors; tcsp.
      rw @matching_bterms_as_matching_sign in n.
      destruct n.
      allunfold matching_sign; rewrite m0.
      rewrite <- m2; auto.

    + pose proof (IHlib opabs bs oa vars rhs correct wfa wfl) as q; clear IHlib.
      apply q; auto.
Qed.*)

Inductive no_repeats_lib {o} : @library o -> Type :=
| no_rep_lib_em : no_repeats_lib []
| no_rep_lib_cons :
    forall e l,
      !in_lib (entry2name e) l
      -> no_repeats_lib l
      -> no_repeats_lib (e :: l).

Lemma implies_matching_entry_sign_refl :
  forall abs1 abs2,
    matching_entry_sign abs1 abs2
    -> matching_entry_sign abs1 abs1.
Proof.
  introv m.
  allunfold matching_entry_sign; repnd; dands; auto.
  eapply implies_matching_parameters_refl; eauto.
Qed.

Lemma same_entry_name_preserves_find_entry {o} :
  forall (lib : @library o) name1 name2 e,
    find_entry_sign lib name1 = Some e
    -> same_entry_name name1 name2
    -> find_entry_sign lib name2 = Some e.
Proof.
  induction lib; introv fe me; allsimpl; ginv.
  destruct a; boolvar; simpl in *; ginv; tcsp;
    try (complete (destruct n; eauto 3 with slow)).

  - eapply IHlib; eauto.

  - pose proof (IHlib name1 name2 e) as q; repeat (autodimp q hyp).
Qed.

Lemma find_entry_sign_implies_in_lib {o} :
  forall (lib : @library o) opabs e,
    find_entry_sign lib opabs = Some e
    -> in_lib opabs lib.
Proof.
  induction lib; introv fe; allsimpl; ginv.
  destruct a; allsimpl; boolvar; ginv; allsimpl.

  - unfold in_lib; simpl.
    eexists; dands;[left;eauto|].
    simpl; auto.

  - apply IHlib in fe.
    unfold in_lib in *; exrepnd.
    exists e0; simpl; tcsp.

  - unfold in_lib; simpl.
    eexists; dands;[left;eauto|].
    simpl; auto.

  - apply IHlib in fe.
    unfold in_lib in *; exrepnd.
    exists e0; simpl; tcsp.
Qed.

Lemma find_entry_sign_implies_same_entry_name {o} :
  forall (lib : @library o) (name : EntryName) (e : library_entry),
    find_entry_sign lib name = Some e
    -> same_entry_name name (entry2name e).
Proof.
  induction lib; simpl in *; introv h; tcsp; boolvar; ginv; auto.
Qed.

Lemma agreeing_libraries_cons_right_implies {o} :
  forall (lib1 lib2 : @library o) e,
    !in_lib (entry2name e) lib2
    -> libraries_agree_on_intersection lib1 (e :: lib2)
    -> libraries_agree_on_intersection lib1 lib2.
Proof.
  introv norep agree; introv.
  pose proof (agree name) as h; clear agree.
  remember (find_entry_sign lib1 name) as fe1; destruct fe1 as [e1|]; allsimpl; auto.
  destruct e1; allsimpl; auto; destruct e; allsimpl; auto; boolvar; repnd; subst; tcsp.

  - remember (find_entry_sign lib2 name) as fe2; destruct fe2 as [e2|]; allsimpl; auto.
    destruct e2; auto.

    + destruct name; simpl in *; subst; tcsp.
      symmetry in Heqfe2.
      apply find_entry_sign_implies_in_lib in Heqfe2; tcsp.

    + symmetry in Heqfe2.
      apply find_entry_sign_implies_in_lib in Heqfe2.
      eapply same_entry_name_preserves_in_lib in Heqfe2; [|eauto]; tcsp.

  - remember (find_entry_sign lib2 name) as fe2; destruct fe2 as [e2|]; allsimpl; auto.
    destruct e2; tcsp.

    + destruct name; simpl in *; tcsp.
      symmetry in Heqfe2; apply find_entry_sign_implies_same_entry_name in Heqfe2; simpl in *; tcsp.

    + destruct name; simpl in *; tcsp.
      symmetry in Heqfe2.
      apply find_entry_sign_implies_in_lib in Heqfe2.
      eapply same_entry_name_preserves_in_lib in Heqfe2; [|eauto]; tcsp.
Qed.

(*Lemma agreeing_libraries_no_rep_find_entry_sign {o} :
  forall (lib1 lib2 : @library o) abs entry,
    libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> find_entry_sign lib1 abs = Some entry
    -> found_entry_sign lib2 abs = true
    -> find_entry_sign lib2 abs = Some entry.
Proof.
  induction lib2; introv agree norep fe1 fe2; allsimpl; ginv.
  destruct a; boolvar; GC.

  - pose proof (agree opabs) as h.
    eapply matching_entry_preserves_find_entry in fe1;[|exact m].
    rewrite fe1 in h.
    simpl in h.
    boolvar; repnd; subst; tcsp.

    + eauto with pi.

    + destruct n; eapply implies_matching_entry_sign_refl;
      apply matching_entry_sign_sym; eauto.

  - inversion norep; clear norep; subst; allsimpl.
    apply IHlib2; auto.
    allsimpl.
    eapply agreeing_libraries_cons_right_implies; eauto.
    simpl; auto.
Qed.

Lemma compute_step_preserves_agreeing_libraries {o} :
  forall lib1 lib2,
    assert (wf_library lib1)
    -> assert (wf_library lib2)
    -> libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> forall (t : @NTerm o) u,
        wf_term t
        -> isotrue (all_abstractions_are_defined lib1 t)
        -> isotrue (all_abstractions_are_defined lib2 t)
        -> compute_step lib1 t = csuccess u
        -> compute_step lib2 t = csuccess u.
Proof.
  introv wflib1 wflib2 agree norep; nterm_ind1s t as [v|f ind|op bs ind] Case; introv wft allabs1 allabs2 comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; auto.

  - Case "oterm".
    apply isotrue_all_abstractions_are_defined_oterm in allabs1; repnd.
    apply isotrue_all_abstractions_are_defined_oterm in allabs2; repnd.
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; auto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst; auto.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv; auto.
              csunf; simpl; auto;dcwf h; simpl; auto.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.

            + csunf; simpl; dcwf h; simpl.
              apply isexc_implies2 in comp0; exrepnd; subst; auto.

            + fold_terms.
              rewrite compute_step_eapply_iscan_isnoncan_like; auto.
              apply wf_term_eapply_iff in wft; exrepnd; allunfold @nobnd; ginv.
              pose proof (ind b b []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              apply h in comp1; auto; clear h;
              try (complete (apply (allabs1 (nobnd b)); tcsp));
              try (complete (apply (allabs2 (nobnd b)); tcsp)).
              rewrite comp1; auto.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto; GC.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv; fold_terms.
                  unfold mk_eapply.
                  rewrite compute_step_eapply_lam_iscan; auto.

                + inversion comp3; subst.
                  csunf; simpl; dcwf h; simpl; boolvar; try omega.
                  rewrite Znat.Nat2Z.id; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.
                apply wf_term_eapply_iff in wft; exrepnd; allunfold @nobnd; ginv.
                pose proof (ind b b []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q; auto;
                try (complete (apply (allabs1 (nobnd b)); tcsp));
                try (complete (apply (allabs2 (nobnd b)); tcsp)).
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl; GC.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto; GC.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto; GC.

              repndors; exrepnd; subst; auto;
              apply implies_isotrue_all_abstractions_are_defined_subst; auto; simpl;
              try (apply (allabs (bterm [v1] t1)); tcsp);
              try (apply (allabs (bterm [v2] t2)); tcsp).
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto; GC.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; simpl; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl; boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; simpl; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; GC.

              - apply compute_step_compop_success_can_can in comp1;
                repndors; exrepnd; subst; ginv;
                repndors; exrepnd; subst; allsimpl; boolvar;
                try (complete (subst; csunf; simpl; dcwf h; simpl;
                               unfold compute_step_comp; simpl;
                               allrw; boolvar; tcsp; try omega)).

              - pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allsimpl.
                apply wf_term_ncompop_iff in wft; exrepnd; ginv.
                apply q in comp4; clear q; auto;
                try (apply (allabs1 (nobnd b)); tcsp);
                try (apply (allabs2 (nobnd b)); tcsp).
                rewrite compute_step_ncompop_ncanlike2; auto; dcwf h.
                rewrite comp4; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; allsimpl.
                csunf; simpl; dcwf h; simpl; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - apply compute_step_arithop_success_can_can in comp1;
                repndors; exrepnd; subst; ginv; simpl; auto.
                csunf; simpl; dcwf h; simpl; allrw; auto.

              - pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allsimpl.
                apply wf_term_narithop_iff in wft; exrepnd; ginv.
                apply q in comp4; clear q; auto;
                try (apply (allabs1 (nobnd b)); tcsp);
                try (apply (allabs2 (nobnd b)); tcsp).
                rewrite compute_step_narithop_ncanlike2; auto; dcwf h.
                allrw; auto.

              - apply isexc_implies2 in comp1; exrepnd; subst; allsimpl.
                csunf; simpl; dcwf h; simpl; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto; GC.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.

            apply wf_oterm_iff in wft; repnd; allsimpl.
            pose proof (wft (nobnd (oterm (NCan ncan2) bts))) as wf2; autodimp wf2 hyp.
            allrw @wf_bterm_iff.

            apply q in Heqc; clear q; auto;
            try (apply (allabs1 (nobnd (oterm (NCan ncan2) bts))); tcsp);
            try (apply (allabs2 (nobnd (oterm (NCan ncan2) bts))); tcsp).
            csunf; simpl; allrw; simpl; auto.

          + SSCase "Exc".

            csunf comp; allsimpl; GC.
            apply compute_step_catch_success in comp.

            repndors; exrepnd; subst; allsimpl; ginv; auto.
            csunf; simpl.
            rewrite compute_step_catch_non_trycatch; auto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.

            apply wf_oterm_iff in wft; repnd; allsimpl.
            pose proof (wft (nobnd (oterm (Abs abs2) bts))) as wf2; autodimp wf2 hyp.
            allrw @wf_bterm_iff.

            apply q in Heqc; clear q; allsimpl;
            allrw isotrue_oband; dands; auto.

            * csunf; simpl; allrw; simpl; auto.

            * apply isotrue_bool2obool_iff.
              pose proof (allabs1 (nobnd (oterm (Abs abs2) bts))) as q; autodimp q hyp.
              allsimpl.
              allrw isotrue_oband; repnd.
              allrw isotrue_bool2obool_iff; auto.

            * pose proof (allabs1 (nobnd (oterm (Abs abs2) bts))) as q; autodimp q hyp.
              allsimpl; allrw isotrue_oband; tcsp.

            * apply isotrue_bool2obool_iff.
              pose proof (allabs2 (nobnd (oterm (Abs abs2) bts))) as q; autodimp q hyp.
              allsimpl.
              allrw isotrue_oband; repnd.
              allrw isotrue_bool2obool_iff; auto.

            * pose proof (allabs2 (nobnd (oterm (Abs abs2) bts))) as q; autodimp q hyp.
              allsimpl; allrw isotrue_oband; tcsp.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; allsimpl; ginv;
        autorewrite with slow in *.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          rewrite compute_step_fresh_if_isnoncan_like; auto.
          allrw @wf_fresh_iff.
          apply q in comp2; auto; allrw; simpl; auto.

          + apply wf_term_subst; eauto 3 with slow.

          + apply implies_isotrue_all_abstractions_are_defined_subst; simpl; auto.
            try (apply (allabs1 (bterm [n] t)); tcsp).

          + apply implies_isotrue_all_abstractions_are_defined_subst; simpl; auto.
            try (apply (allabs2 (bterm [n] t)); tcsp).
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.
      apply (found_entry_implies_compute_step_lib_success lib2 abs oa2 bs vars rhs correct).
      apply wf_abs_implies in wft.

      pose proof (found_entry_iff_sign lib1 abs bs oa2 vars rhs correct) as h1.
      repeat (autodimp h1 hyp).

      pose proof (found_entry_iff_sign lib2 abs bs oa2 vars rhs correct) as h2.
      repeat (autodimp h2 hyp).

      apply h1 in comp0; clear h1.
      apply h2; clear h2.
      eapply agreeing_libraries_no_rep_find_entry_sign; eauto.
Qed.

Lemma reduces_to_preserves_agreeing_libraries {o} :
  forall lib1 lib2,
    assert (wf_library lib1)
    -> assert (wf_library lib2)
    -> libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> simple_no_undefined_abs_in_lib lib1
    -> simple_no_undefined_abs_in_lib lib2
    -> forall (t : @NTerm o) u,
        wf_term t
        -> isotrue (all_abstractions_are_defined lib1 t)
        -> isotrue (all_abstractions_are_defined lib2 t)
        -> reduces_to lib1 t u
        -> reduces_to lib2 t u.
Proof.
  introv wflib1 wflib2 agree norep undef1 undef2 wft allabs1 allabs2 comp.
  allunfold @reduces_to; exrepnd; exists k.
  revert dependent t.
  induction k; introv wf iso1 iso2 comp.

  - allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    pose proof (compute_step_preserves_agreeing_libraries
                  lib1 lib2 wflib1 wflib2 agree norep
                  t u0 wf iso1 iso2 comp1) as q.
    pose proof (IHk u0) as h.
    repeat (autodimp h hyp).
    { eapply compute_step_preserves_wf; eauto. }
    { eapply compute_step_preserves_all_abstractions_are_defined; eauto. }
    { eapply compute_step_preserves_all_abstractions_are_defined; eauto. }
    eexists; dands; eauto.
Qed.

Lemma computes_to_value_preserves_agreeing_libraries {o} :
  forall lib1 lib2,
    assert (wf_library lib1)
    -> assert (wf_library lib2)
    -> libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> simple_no_undefined_abs_in_lib lib1
    -> simple_no_undefined_abs_in_lib lib2
    -> forall (t : @NTerm o) u,
        wf_term t
        -> isotrue (all_abstractions_are_defined lib1 t)
        -> isotrue (all_abstractions_are_defined lib2 t)
        -> computes_to_value lib1 t u
        -> computes_to_value lib2 t u.
Proof.
  introv wflib1 wflib2 agree norep undef1 undef2 wft iso1 iso2 comp.
  allunfold @computes_to_value; repnd; dands; auto.
  apply (reduces_to_preserves_agreeing_libraries lib1 lib2); auto.
Qed.

Lemma computes_to_valc_preserves_agreeing_libraries {o} :
  forall lib1 lib2,
    assert (wf_library lib1)
    -> assert (wf_library lib2)
    -> libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> simple_no_undefined_abs_in_lib lib1
    -> simple_no_undefined_abs_in_lib lib2
    -> forall (t : @CTerm o) u,
        isotrue (all_abstractions_are_defined_cterm lib1 t)
        -> isotrue (all_abstractions_are_defined_cterm lib2 t)
        -> computes_to_valc lib1 t u
        -> computes_to_valc lib2 t u.
Proof.
  introv wflib1 wflib2 agree norep undef1 undef2 iso1 iso2 comp.
  destruct_cterms.
  allunfold @all_abstractions_are_defined_cterm; allsimpl.
  allunfold @computes_to_valc; allsimpl.
  apply (computes_to_value_preserves_agreeing_libraries lib1 lib2); eauto 2 with slow.
Qed.
 *)
