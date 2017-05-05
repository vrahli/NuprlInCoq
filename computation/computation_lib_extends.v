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


Definition opabs_of_lib_entry {o} (e : @library_entry o) : opabs :=
  match e with
  | lib_abs oa _ _ _ => oa
  end.

Definition matching_entries {o} (entry1 entry2 : @library_entry o) : Prop :=
  matching_entry_sign (opabs_of_lib_entry entry1) (opabs_of_lib_entry entry2).

Fixpoint entry_in_library {o} (entry : @library_entry o) (lib : library) : Type :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry = entry'
    [+]
    (~ matching_entries entry entry'
       # entry_in_library entry entries)
  end.

(* [lib1] extends [lib0] *)
Definition lib_extends {o} (lib1 lib0 : @library o) : Type :=
  forall entry, entry_in_library entry lib0 -> entry_in_library entry lib1.

Definition in_lib {o}
           (opabs : opabs)
           (lib   : @library o) :=
  {e : library_entry
   & LIn e lib
   # matching_entry_sign opabs (opabs_of_lib_entry e)}.

Definition entry_not_in_lib {o} (e : @library_entry o) (l : @library o) :=
  !in_lib (opabs_of_lib_entry e) l.

Hint Resolve matching_entry_sign_sym : slow.

Lemma entry_in_library_implies_in {o} :
  forall (entry : @library_entry o) lib,
    entry_in_library entry lib -> LIn entry lib.
Proof.
  induction lib; auto; introv h; simpl in *.
  repndors; subst; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in : slow.

Lemma lib_extends_cons_implies {o} :
  forall (e : @library_entry o) (lib lib0 : library),
    entry_not_in_lib e lib0
    -> lib_extends lib (e :: lib0)
    -> lib_extends lib lib0.
Proof.
  introv ni ext i.
  apply ext; simpl; clear ext.
  right; dands; auto; intro m.
  destruct ni.

  exists entry.
  dands; eauto 3 with slow.
Qed.

Lemma lib_extends_refl {o} :
  forall (lib : @library o), lib_extends lib lib.
Proof.
  introv i; auto.
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
  destruct a.
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
  destruct a; repndors; subst; boolvar; tcsp.

  - unfold matching_entries; simpl; intro h.
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

  - eapply IHlib; eauto.
Qed.

Lemma entry_in_libray_implies_find_entry_some {o} :
  forall lib abs oa vars (t : @SOTerm o) bs correct,
    matching_entry abs oa vars bs
    -> entry_in_library (lib_abs oa vars t correct) lib
    -> find_entry lib abs bs = Some (lib_abs oa vars t correct).
Proof.
  induction lib; introv m i; simpl in *; tcsp.
  destruct a; simpl in *.
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

Lemma lib_extends_preserves_find_entry {o} :
  forall (lib1 lib2 : @library o) abs bs (e : library_entry),
    lib_extends lib2 lib1
    -> find_entry lib1 abs bs = Some e
    -> find_entry lib2 abs bs = Some e.
Proof.
  introv ext fe.
  apply find_entry_some_decomp in fe; exrepnd; subst.

  pose proof (ext (lib_abs oa vars rhs correct)) as h.
  simpl in h; autodimp h hyp.

  { apply implies_entry_in_library_app_right;[simpl; tcsp|].
    pose proof (matching_entry_preserves_find_entry lib0 abs oa vars bs) as q.
    autodimp q hyp.
    rewrite q in fe1; clear q.
    applydup @matching_entry_implies_matching_bterms in fe3.
    dup correct as ms.
    apply correct_abs_implies_matching_sign in ms.
    rw @matching_bterms_as_matching_sign in fe0.
    introv i; eapply find_entry_none_implies; eauto. }

  apply entry_in_libray_implies_find_entry_some; auto.
Qed.

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
