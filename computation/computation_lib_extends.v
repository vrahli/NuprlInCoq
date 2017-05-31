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


Require Export computation_preserves_lib.


(* This is entry2name *)

(*Definition opabs_of_lib_entry {o} (e : @library_entry o) : opabs :=
  match e with
  | lib_abs oa _ _ _ => oa
  end.*)

Definition matching_entries {o} (entry1 entry2 : @library_entry o) : Prop :=
  same_entry_name (entry2name entry1) (entry2name entry2).
(*  matching_entry_sign (opabs_of_lib_entry entry1) (opabs_of_lib_entry entry2).*)

Fixpoint entry_in_library {o} (entry : @library_entry o) (lib : library) : Prop :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry = entry'
    \/
    (~ matching_entries entry entry'
       # entry_in_library entry entries)
  end.


(*

   TODO: We have to make sure that extensions satisfy the choice sequence
   restrictions!

 *)


(* [vals1] extends [vals2] is [vals2] is an initial segment of [vals1] *)
Definition choice_sequence_vals_extend {o} (vals1 vals2 : @ChoiceSeqVals o) : Prop :=
  exists vals, vals1 = vals2 ++ vals.

(* [entry1] extends [entry2] *)
Definition entry_extends {o} (entry1 entry2 : @library_entry o) : Prop :=
  match entry1, entry2 with
  | lib_cs name1 entry1, lib_cs name2 entry2 =>
    name1 = name2
    /\
    choice_sequence_vals_extend entry1 entry2
  | _, _ => entry1 = entry2
  end.

(* true if there is an extended version of [entry] in [lib] *)
Fixpoint entry_in_library_extends {o} (entry : @library_entry o) (lib : library) : Prop :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry_extends entry' entry
    \/
    (~ matching_entries entry entry'
       # entry_in_library_extends entry entries)
  end.

(* I used to have only the lib_extends_ext part but then it
   complicated some stuff such as, there might some names in lib0
   that are not in lib1... *)

Definition lsubset {A} (l1 l2 : list A) : Prop :=
  forall a, List.In a l1 -> List.In a l2.

(* [lib1] extends [lib0] *)
Record lib_extends {o} (lib1 lib0 : @library o) : Prop :=
  MkLibExtends
    {
      lib_extends_ext :
        forall entry,
          entry_in_library entry lib0
          -> entry_in_library_extends entry lib1;

      lib_extends_sub : lsubset lib0 lib1;
    }.

(*Definition in_lib {o}
           (opabs : opabs)
           (lib   : @library o) :=
  exists (e : library_entry),
    List.In e lib
    /\ matching_entry_sign opabs (opabs_of_lib_entry e).*)

Definition entry_not_in_lib {o} (e : @library_entry o) (l : @library o) :=
  !in_lib (entry2name e) l.

Hint Resolve matching_entry_sign_sym : slow.

Lemma entry_in_library_implies_in {o} :
  forall (entry : @library_entry o) lib,
    entry_in_library entry lib -> List.In entry lib.
Proof.
  induction lib; auto; introv h; simpl in *.
  repndors; subst; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in : slow.

Lemma matching_entries_implies_same_entry_name {o} :
  forall (entry1 entry2 : @library_entry o),
    matching_entries entry1 entry2
    -> same_entry_name (entry2name entry1) (entry2name entry2).
Proof.
  introv m; destruct entry1, entry2; simpl in *; tcsp.
Qed.
Hint Resolve matching_entries_implies_same_entry_name : slow.

Hint Resolve same_entry_name_sym : slow.

Lemma lsubset_cons_left_implies_lsubset :
  forall {A} (a : A) l1 l2,
    lsubset (a :: l1) l2
    -> lsubset l1 l2.
Proof.
  introv ss i; apply ss; simpl; tcsp.
Qed.
Hint Resolve lsubset_cons_left_implies_lsubset : slow.

Lemma lsubset_refl :
  forall {A} (l : list A), lsubset l l.
Proof.
  introv i; auto.
Qed.
Hint Resolve lsubset_refl : slow.

Lemma lib_extends_cons_implies {o} :
  forall (e : @library_entry o) (lib lib0 : library),
    entry_not_in_lib e lib0
    -> lib_extends lib (e :: lib0)
    -> lib_extends lib lib0.
Proof.
  introv ni ext.
  destruct ext as [ext ss].
  split; eauto 4 with slow.
  introv i.
  apply ext; simpl; clear ext.
  right; dands; auto; intro m.
  destruct ni.

  exists entry.
  dands; eauto 3 with slow.
Qed.

Lemma choice_sequence_vals_extend_refl {o} :
  forall (vals : @ChoiceSeqVals o), choice_sequence_vals_extend vals vals.
Proof.
  introv; exists ([] : @ChoiceSeqVals o); autorewrite with slow; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_refl : slow.

Lemma entry_extends_refl {o} :
  forall (entry : @library_entry o), entry_extends entry entry.
Proof.
  destruct entry; simpl in *; tcsp.
  dands; eauto 2 with slow.
Qed.
Hint Resolve entry_extends_refl : slow.

Lemma entry_in_library_implies_entry_in_library_extends {o} :
  forall entry (lib : @library o),
    entry_in_library entry lib
    -> entry_in_library_extends entry lib.
Proof.
  induction lib; introv e; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  left; eauto 2 with slow.
Qed.
Hint Resolve entry_in_library_implies_entry_in_library_extends : slow.

Lemma lib_extends_refl {o} :
  forall (lib : @library o), lib_extends lib lib.
Proof.
  introv; split; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_refl : slow.

Lemma entry_in_library_implies_find_entry {o} :
  forall (lib : @library o) abs opabs vars bs rhs correct,
    matching_entry abs opabs vars bs
    -> entry_in_library (lib_abs opabs vars rhs correct) lib
    -> find_entry lib abs bs = Some (lib_abs opabs vars rhs correct).
Proof.
  induction lib; introv m e; simpl in *; tcsp.
  destruct a.

  { repndors; repnd; tcsp; ginv. }

  repndors; repnd.

  - inversion e; subst; clear e.
    boolvar; tcsp.

    + pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.

    + apply not_matching_entry_iff in n; tcsp.

  - boolvar; tcsp.
    apply matching_entry_implies_sign in m.
    apply matching_entry_implies_sign in m0.
    destruct e0.
    unfold matching_entries; simpl.

    eapply matching_entry_sign_trans;[|eauto].
    eapply matching_entry_sign_sym;auto.
Qed.

Lemma find_entry_some_decomp {o} :
  forall (lib : @library o) abs bs e,
    find_entry lib abs bs = Some e
    <=> {lib1 : library
         & {lib2 : library
         & {oa : opabs
         & {vars : list sovar_sig
         & {rhs : SOTerm
         & {correct : correct_abs oa vars rhs
         & lib = lib1 ++ e :: lib2
         # e = lib_abs oa vars rhs correct
         # matching_entry abs oa vars bs
         # find_entry lib1 abs bs = None }}}}}}.
Proof.
  induction lib; introv; split; introv h; simpl in *; ginv.

  - exrepnd.
    destruct lib1; ginv.

  - destruct a.

    {
      apply IHlib in h; exrepnd; subst; clear IHlib.
      exists (lib_cs name entry :: lib1) lib2 oa vars rhs correct.
      dands; auto.
    }

    boolvar; ginv.

    + exists ([] : @library o) lib opabs vars rhs correct; simpl.
      dands; auto.

    + apply IHlib in h; exrepnd; subst; clear IHlib.
      exists (lib_abs opabs vars rhs correct :: lib1) lib2 oa vars0 rhs0 correct0.
      dands; auto.
      simpl; boolvar; auto.
      apply not_matching_entry_iff in n; tcsp.

  - exrepnd; subst.
    destruct a.

    {
      destruct lib1; simpl in *; ginv.
      apply IHlib.
      exists lib1 lib2 oa vars rhs correct.
      dands; auto.
    }

    destruct lib1; simpl in *; ginv.

    + inversion h0; subst; clear h0.
      pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.
      boolvar; auto.
      apply not_matching_entry_iff in n; tcsp.

    + boolvar; ginv.
      apply IHlib.
      exists lib1 lib2 oa vars rhs correct; dands; auto.
Qed.

Lemma implies_entry_in_library_app_right {o} :
  forall (lib1 lib2 : @library o) e,
    entry_in_library e lib2
    -> (forall e', LIn e' lib1 -> ~ matching_entries e e')
    -> entry_in_library e (lib1 ++ lib2).
Proof.
  induction lib1; introv h q; simpl in *; auto.
  right; dands; auto.
Qed.

Lemma matching_entry_trans_right {o} :
  forall abs1 abs2 abs3 vars1 vars2 (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars1 bs
    -> matching_entry abs2 abs3 vars2 bs
    -> matching_entry abs1 abs3 vars2 bs.
Proof.
  introv m1 m2; unfold matching_entry in *; repnd; dands; tcsp;
    try (complete (allrw; auto)).
  eapply matching_parameters_trans; eauto.
Qed.

Lemma matching_entry_sym {o} :
  forall abs1 abs2 vars (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> matching_entry abs2 abs1 vars bs.
Proof.
  introv m; unfold matching_entry in *; repnd; dands; tcsp;
    try (complete (allrw; auto)).
  apply matching_parameters_sym; auto.
Qed.

Lemma matching_entry_preserves_find_entry {o} :
  forall (lib : @library o) abs1 abs2 vars bs,
    matching_entry abs1 abs2 vars bs
    -> find_entry lib abs1 bs = find_entry lib abs2 bs.
Proof.
  induction lib; introv m; simpl in *; auto.
  destruct a; eauto;[].

  boolvar; auto.
  - apply not_matching_entry_iff in n.
    apply matching_entry_sym in m.
    eapply matching_entry_trans_right in m0;[|exact m]; tcsp.
  - apply not_matching_entry_iff in n.
    eapply matching_entry_trans_right in m0;[|exact m]; tcsp.
  - eapply IHlib; eauto.
Qed.

Lemma matching_entry_sign_implies_matching_entry {o} :
  forall (abs1 abs2 : opabs) (vars : list sovar_sig) (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> matching_entry_sign abs1 abs2
    -> matching_entry abs1 abs2 vars bs.
Proof.
  introv h m; unfold matching_entry_sign in m; unfold matching_entry.
  repnd; dands; auto.
Qed.

Lemma matching_entry_implies_matching_bterms {o} :
  forall (abs1 abs2 : opabs) (vars : list sovar_sig) (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> matching_bterms vars bs.
Proof.
  introv m; unfold matching_entry in m; tcsp.
Qed.

Lemma correct_abs_implies_matching_sign {o} :
  forall abs vars (t : @SOTerm o),
    correct_abs abs vars t
    -> matching_sign vars (opabs_sign abs).
Proof.
  introv cor.
  unfold correct_abs in cor; tcsp.
Qed.

Lemma matching_entry_sign_implies_eq_opabs_signs :
  forall abs1 abs2,
    matching_entry_sign abs1 abs2
    -> opabs_sign abs1 = opabs_sign abs2.
Proof.
  introv m; unfold matching_entry_sign in m; tcsp.
Qed.

Lemma find_entry_none_implies {o} :
  forall (lib : @library o) abs bs e vars rhs correct,
    matching_sign vars (opabs_sign abs)
    -> matching_sign vars (map num_bvars bs)
    -> find_entry lib abs bs = None
    -> LIn e lib
    -> ~ matching_entries (lib_abs abs vars rhs correct) e.
Proof.
  induction lib; introv ms1 ms2 fe i; simpl in *; tcsp.
  destruct a; repndors; subst; boolvar; tcsp; eauto;[].

  unfold matching_entries; simpl; intro h.
  apply not_matching_entry_iff in n.
  destruct n.
  apply matching_entry_sign_implies_matching_entry; auto.
  apply matching_bterms_as_matching_sign.
  apply correct_abs_implies_matching_sign in correct0.
  unfold matching_sign in *.

  apply matching_entry_sign_implies_eq_opabs_signs in h.
  rewrite correct0.
  rewrite <- h.
  rewrite <- ms1; rewrite <- ms2; auto.
Qed.

Lemma entry_in_libray_implies_find_entry_some {o} :
  forall lib abs oa vars (t : @SOTerm o) bs correct,
    matching_entry abs oa vars bs
    -> entry_in_library (lib_abs oa vars t correct) lib
    -> find_entry lib abs bs = Some (lib_abs oa vars t correct).
Proof.
  induction lib; introv m i; simpl in *; tcsp.
  destruct a; simpl in *.

  { repndors; tcsp; ginv. }

  repndors; repnd.

  - inversion i; subst; clear i.
    pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.
    boolvar; auto.
    apply not_matching_entry_iff in n; tcsp.

  - unfold matching_entries in i0; simpl in i0.
    boolvar; ginv.

    + destruct i0.
      eapply matching_entry_implies_sign.
      eapply matching_entry_trans_right;[|exact m0].
      apply matching_entry_sym;eauto.

    + apply IHlib; auto.
Qed.
Hint Resolve entry_in_libray_implies_find_entry_some : slow.

Lemma entry_abs_in_library_extends_implies_entry_in_library {o} :
  forall oa vars rhs correct (lib : @library o),
    entry_in_library_extends (lib_abs oa vars rhs correct) lib
    -> entry_in_library (lib_abs oa vars rhs correct) lib.
Proof.
  induction lib; introv e; simpl in *; tcsp.
  repndors; repnd; tcsp.
  destruct a; simpl in *; tcsp.
Qed.
Hint Resolve entry_abs_in_library_extends_implies_entry_in_library : slow.

Lemma lib_extends_preserves_find_entry {o} :
  forall (lib1 lib2 : @library o) abs bs (e : library_entry),
    lib_extends lib2 lib1
    -> find_entry lib1 abs bs = Some e
    -> find_entry lib2 abs bs = Some e.
Proof.
  introv ext fe.
  apply find_entry_some_decomp in fe; exrepnd; subst.

  pose proof (lib_extends_ext _ _ ext (lib_abs oa vars rhs correct)) as h.
  simpl in h; autodimp h hyp; eauto 3 with slow;[].

  apply implies_entry_in_library_app_right;[simpl; tcsp|].
  pose proof (matching_entry_preserves_find_entry lib0 abs oa vars bs) as q.
  autodimp q hyp.
  rewrite q in fe1; clear q.
  applydup @matching_entry_implies_matching_bterms in fe3.
  dup correct as ms.
  apply correct_abs_implies_matching_sign in ms.
  rw @matching_bterms_as_matching_sign in fe0.
  introv i; eapply find_entry_none_implies; eauto.
Qed.

Lemma in_get_utokens_library_iff {o} :
  forall (lib : @library o) a,
    LIn a (get_utokens_library lib)
    <=> {entry : library_entry & LIn entry lib # LIn a (get_utokens_library_entry entry) }.
Proof.
  introv; unfold get_utokens_library.
  rw lin_flat_map; tcsp.
Qed.

Lemma list_in_get_utokens_library_iff {o} :
  forall (lib : @library o) a,
    List.In a (get_utokens_library lib)
    <-> exists (entry : library_entry), List.In entry lib /\ List.In a (get_utokens_library_entry entry).
Proof.
  introv; unfold get_utokens_library.
  rewrite in_flat_map; tcsp.
Qed.

Definition LIn_iff_In :
  forall {A} (deq : Deq A) (a : A) (l : list A),
    LIn a l <=> List.In a l.
Proof.
  induction l; simpl in *; split; intro h; tcsp; repndors; tcsp.

  - apply IHl in h; tcsp.

  - destruct (deq a0 a) as [d|d]; subst; tcsp.
    right; apply IHl.
    repndors; tcsp.
Qed.

Definition LIn_iff_In_name {o} :
  forall (a : get_patom_set o) l,
    LIn a l <=> List.In a l.
Proof.
  introv; apply LIn_iff_In.
  apply get_patom_deq.
Qed.

Lemma lib_extends_implies_subset_get_utokens_library {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> subset (get_utokens_library lib1) (get_utokens_library lib2).
Proof.
  introv ext i.
  allrw @LIn_iff_In_name.
  allrw @list_in_get_utokens_library_iff; exrepnd.
  apply (lib_extends_sub _ _ ext) in i1.
  exists entry; dands; auto.
Qed.
Hint Resolve lib_extends_implies_subset_get_utokens_library : slow.

(*
(*

  We should be able to prove equality!

 *)
Lemma compute_step_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (comp : compute_step lib1 a = csuccess b),
    compute_step lib2 a = csuccess b.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          SSCase "NEApply".

          apply compute_step_eapply_success in comp; exrepnd; subst.
          repndors; exrepnd; allsimpl; subst.

          + apply compute_step_eapply2_success in comp1; repnd; subst.
            repndors; exrepnd; subst; ginv.
            csunf; simpl.
            dcwf h; simpl.
            boolvar; try omega.
            rewrite Znat.Nat2Z.id; auto.

          + csunf; simpl.
            apply isexc_implies2 in comp0; exrepnd; subst.
            dcwf h; simpl; auto.

          + fold_terms.
            rewrite compute_step_eapply_iscan_isnoncan_like; auto.
            pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            apply h in comp1; clear h.
            rewrite comp1; auto.

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
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto.

                + unfold mk_nseq in *; allsimpl; ginv.
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
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
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
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
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

        - fold (mk_fresh n t).
          rewrite compute_step_fresh_if_isnoncan_like; auto.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.
          remember (get_fresh_atom t) as a; simpl.
          rewrite comp2; simpl; auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.

      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).
      eapply lib_extends_preserves_find_entry; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (n : nat)
         (comp : reduces_in_atmost_k_steps lib1 a b n),
    reduces_in_atmost_k_steps lib2 a b n.
Proof.
  introv ext r.
  revert dependent a.
  induction n; introv r.

  - allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    exists u; dands; auto.
    eapply compute_step_preserves_lib_extends; eauto.
Qed.

Lemma reduces_to_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (comp : reduces_to lib1 a b),
    reduces_to lib2 a b.
Proof.
  introv ext r.
  unfold reduces_to in *; exrepnd.
  exists k.
  eapply reduces_in_atmost_k_steps_preserves_lib_extends; eauto.
Qed.
 *)

Lemma lib_cs_in_library_extends_implies {o} :
  forall (lib : @library o) name entry,
    entry_in_library_extends (lib_cs name entry) lib
    ->
    exists (entry' : ChoiceSeqEntry),
      find_cs lib name = Some entry'
      /\ choice_sequence_vals_extend entry' entry.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; repndors; repnd; subst; tcsp; boolvar; tcsp; GC; ginv;
    try (complete (eapply IHlib; eauto)).
  exists entry0; dands; auto.
Qed.
Hint Resolve lib_cs_in_library_extends_implies : slow.

Lemma find_cs_some_implies_entry_in_library {o} :
  forall (lib : @library o) name vals,
    find_cs lib name = Some vals
    -> entry_in_library (lib_cs name vals) lib.
Proof.
  induction lib; simpl; introv fcs; tcsp.
  destruct a; simpl in *; boolvar; ginv; GC; tcsp.
Qed.
Hint Resolve find_cs_some_implies_entry_in_library : slow.

Lemma lib_extends_preserves_find_cs {o} :
  forall (lib1 lib2 : @library o) name entry1,
    lib_extends lib2 lib1
    -> find_cs lib1 name = Some entry1
    ->
    exists (entry2 : ChoiceSeqEntry),
      find_cs lib2 name = Some entry2
      /\ choice_sequence_vals_extend entry2 entry1.
Proof.
  introv ext fcs.
  apply find_cs_some_implies_entry_in_library in fcs.
  apply ext in fcs; eauto 2 with slow.
Qed.

Hint Rewrite minus0 : num.

Lemma find_value_of_cs_at_app {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) n,
    find_value_of_cs_at (vals1 ++ vals2) n
    = match find_value_of_cs_at vals1 n with
      | Some v => Some v
      | None => find_value_of_cs_at vals2 (n - length vals1)
      end.
Proof.
  induction vals1; introv; simpl; autorewrite with num in *; tcsp.
  destruct n; simpl in *; auto.
Qed.

Lemma choice_sequence_vals_extend_preserves_find_value_of_cs_at {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) n v,
    choice_sequence_vals_extend vals2 vals1
    -> find_value_of_cs_at vals1 n = Some v
    -> find_value_of_cs_at vals2 n = Some v.
Proof.
  introv h fcs.
  unfold choice_sequence_vals_extend in h; exrepnd; subst.
  rewrite find_value_of_cs_at_app.
  allrw; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_preserves_find_value_of_cs_at : slow.

Lemma lib_extends_preserves_find_cs_value_at {o} :
  forall (lib1 lib2 : @library o) name n v,
    lib_extends lib2 lib1
    -> find_cs_value_at lib1 name n = Some v
    -> find_cs_value_at lib2 name n = Some v.
Proof.
  introv ext find.
  unfold find_cs_value_at in *.
  remember (find_cs lib1 name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
  eapply lib_extends_preserves_find_cs in Heqfcs;[|eauto].
  exrepnd; allrw; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_preserves_find_cs_value_at : slow.

Lemma subset_get_utokens_library_implies_subset_get_utokens_lib {o} :
  forall (lib1 lib2 : @library o) t,
    subset (get_utokens_library lib1) (get_utokens_library lib2)
    -> subset (get_utokens_lib lib1 t) (get_utokens_lib lib2 t).
Proof.
  introv ss i; allrw in_app_iff; repndors; tcsp.
Qed.
Hint Resolve subset_get_utokens_library_implies_subset_get_utokens_lib : slow.

Lemma unfold_abs_iff_find_entry {o} :
  forall (lib : @library o) oa bs t,
    unfold_abs lib oa bs = Some t
    <=> {oa' : opabs
         & {vars : list sovar_sig
         & {rhs : SOTerm
         & {correct : correct_abs oa' vars rhs
         & find_entry lib oa bs = Some (lib_abs oa' vars rhs correct)
         # matching_entry oa oa' vars bs
         # t = mk_instance vars bs rhs}}}}.
Proof.
  induction lib; simpl in *; introv; split; intro h; exrepnd; ginv.

  - remember (unfold_abs_entry a oa bs) as ua; symmetry in Hequa; destruct ua; ginv.

    + destruct a; simpl in *; ginv.
      boolvar; ginv.
      eexists; eexists; eexists; eexists; dands; eauto.

    + apply IHlib in h; exrepnd; subst.
      destruct a; simpl in *; boolvar; tcsp; GC;
        eexists; eexists; eexists; eexists; dands; eauto.

  - destruct a; subst; simpl in *; tcsp.

    + apply IHlib.
      eexists; eexists; eexists; eexists; dands; eauto.

    + boolvar; tcsp; auto.

      * inversion h0; subst; clear h0; auto.

      * apply IHlib.
        eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma lib_extends_preserves_unfold_abs {o} :
  forall (lib1 lib2 : @library o) abs bs t,
    lib_extends lib2 lib1
    -> unfold_abs lib1 abs bs = Some t
    -> unfold_abs lib2 abs bs = Some t.
Proof.
  introv ext ua.
  allrw @unfold_abs_iff_find_entry.
  exrepnd; subst.

  eapply lib_extends_preserves_find_entry in ua0;[|eauto].
  eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma lib_extends_preserves_compute_step_lib {o} :
  forall (lib1 lib2 : @library o) abs bs t,
    lib_extends lib2 lib1
    -> compute_step_lib lib1 abs bs = csuccess t
    -> compute_step_lib lib2 abs bs = csuccess t.
Proof.
  introv ext comp.
  unfold compute_step_lib in *.
  remember (unfold_abs lib1 abs bs) as ua; symmetry in Hequa; destruct ua; ginv.
  erewrite lib_extends_preserves_unfold_abs;[|eauto|eauto]; auto.
Qed.

(*

  We should be able to prove equality!
  I left the lemma above.
  See computation_preserves_utok.v

 *)
Lemma compute_step_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : compute_step lib1 a = csuccess b),
    {b' : NTerm & compute_step lib2 a = csuccess b' # alpha_eq b' b}.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv wfa comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    csunf; simpl; eexists; dands; eauto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv;
            try (complete (csunf; simpl; eexists; dands; eauto));[].

          SSCase "NEApply".

          apply compute_step_eapply_success in comp; exrepnd; subst.
          repndors; exrepnd; allsimpl; subst.

          + apply compute_step_eapply2_success in comp1; repnd; subst.
            repndors; exrepnd; subst; ginv.
            csunf; simpl.
            dcwf h; simpl.
            boolvar; try omega.
            rewrite Znat.Nat2Z.id; auto.
            eexists; dands; eauto.

          + csunf; simpl.
            apply isexc_implies2 in comp0; exrepnd; subst.
            dcwf h; simpl; auto.
            eexists; dands; eauto.

          + fold_terms.
            rewrite compute_step_eapply_iscan_isnoncan_like; auto.
            pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            apply h in comp1; clear h; eauto 2 with slow wf.
            exrepnd; allrw; simpl.
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
                csunf; simpl; eexists; dands; eauto.
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
                    eexists; dands; eauto.

                + unfold mk_nseq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.
                  eexists; dands; eauto.

                + unfold mk_choice_seq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.
                  erewrite lib_extends_preserves_find_cs_value_at;eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.
                eexists; dands; eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q; eauto 2 with slow wf.
                exrepnd; allrw; simpl.
                eexists; dands; eauto; repeat prove_alpha_eq4.
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
                csunf; simpl; eexists; dands; eauto.
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
              csunf; simpl; eexists; dands; eauto; tcsp.
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
              eexists; dands; eauto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
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
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.
                simpl; allrw; eexists; dands; eauto.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with slow wf.
                exrepnd; allrw; eexists; dands; eauto; repeat prove_alpha_eq4.

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
                dcwf h.
                simpl; allrw; eexists; dands; eauto.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 3 with wf slow.
                exrepnd; allrw; eexists; dands; eauto; repeat prove_alpha_eq4.

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
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 3 with slow wf.
            csunf; simpl.
            exrepnd; allrw; simpl; eexists; dands; eauto; tcsp; repeat prove_alpha_eq4.

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
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 3 with wf slow.
            csunf; simpl.
            exrepnd; allrw; simpl; eexists; dands; eauto; repeat prove_alpha_eq4.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.
          eexists; dands; eauto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.
          eexists; dands; eauto.

        - fold (mk_fresh n t).
          rewrite compute_step_fresh_if_isnoncan_like; auto.

          remember (get_fresh_atom lib1 t) as a.
          pose proof (get_fresh_atom_prop_and_lib lib1 t) as prop; rewrite <- Heqa in prop.
          clear Heqa.

          remember (get_fresh_atom lib2 t) as a'.
          pose proof (get_fresh_atom_prop_and_lib lib2 t) as prop'; rewrite <- Heqa' in prop'.
          clear Heqa'.

          simpl.

          pose proof (compute_step_subst_utoken lib1 t x [(n,mk_utoken a)]) as q.
          repeat (autodimp q hyp); eauto 3 with wf;
            [autorewrite with slow; simpl; apply disjoint_singleton_l; auto|];[].
          exrepnd.
          autorewrite with slow in *; simpl in *; allrw disjoint_singleton_l.

          pose proof (q0 [(n,mk_utoken a')]) as z.
          autorewrite with slow in z; simpl in z; allrw disjoint_singleton_l.
          repeat (autodimp z hyp); eauto 5 with slow;[].
          exrepnd.

          pose proof (ind t (subst t n (mk_utoken a')) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow;[|].
          { rewrite simple_osize_subst; eauto 2 with slow. }
          fold_terms.
          apply q in z1; clear q; eauto 2 with wf;[].

          exrepnd.
          allrw; simpl.
          eexists; dands; eauto.
          unfold mk_fresh.
          repeat prove_alpha_eq4.
          apply alpha_eq_bterm_congr.

          eapply alpha_eq_trans in z0;[|exact z2].
          eapply alpha_eq_trans;
            [apply alpha_eq_subst_utokens;
             [eauto|apply alphaeq_utok_sub_refl] |].
          eapply alpha_eq_trans;
            [|apply alpha_eq_sym;apply alpha_eq_subst_utokens;
              [eauto|apply alphaeq_utok_sub_refl] ].

          eapply alpha_eq_trans;[apply simple_alphaeq_subst_utokens_subst;eauto 6 with slow|];[].

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

      apply found_entry_implies_compute_step_lib_success in comp0.
      eapply lib_extends_preserves_compute_step_lib in comp0;[|eauto].
      rewrite comp0.
      eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wfa  : wf_term a)
         (n    : nat)
         (comp : reduces_in_atmost_k_steps lib1 a b n),
    {b' : NTerm & reduces_in_atmost_k_steps lib2 a b' n # alpha_eq b b'}.
Proof.
  introv ext wf comp.

  revert dependent a.
  induction n; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists b; allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @compute_step_preserves_wf in comp1; auto.
    apply IHn in comp0; exrepnd; auto; clear IHn.
    apply (compute_step_preserves_lib_extends lib1 lib2) in comp1; auto; exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha lib2 u b'0) as w.
    repeat (autodimp w hyp); eauto 3 with slow wf.
    applydup w in comp0; clear w; exrepnd.

    eexists; dands;[rw @reduces_in_atmost_k_steps_S;eexists; dands; eauto|].
    eauto 2 with slow.
Qed.

Lemma reduces_to_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : reduces_to lib1 a b),
    {b' : NTerm & reduces_to lib2 a b' # alpha_eq b b'}.
Proof.
  introv ext wf r.
  unfold reduces_to in *; exrepnd.
  eapply reduces_in_atmost_k_steps_preserves_lib_extends in r0; eauto.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.
