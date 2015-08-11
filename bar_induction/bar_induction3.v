(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export bar_induction2.



(**

  Bar induction, where
    T is a type
    R is the spread law
    B is the bar
    con stands for consistent with the spread law
    ext(s,n,t) = \m. if m=n then t else s m
<<
   H |- squash (X 0 c)

     By bar_induction B i a s x m n t

     H, n:nat, s: nat_n -> nat |- (B n s) \/ not(B n s)   // B is decidable on consistent sequences in the spread
     H, s: nat -> nat |- squash(exists n:nat. B n s)      // B is a bar
     H, n:nat, s: nat_n -> nat, m: B n s |- X n s         // Base case: the conclusion is true at the bar
     H, n:nat, s: nat_n -> nat, x: (forall m: nat. X (n + 1) (ext(s,n,m))) |- X n s // induction case
>>

*)

Definition rule_bar_induction_nat {o}
           (f X c B d e : @NTerm o)
           (s n m v x : NVar)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_squash (mk_apply2 X mk_zero (mk_seq2kseq c (mk_nat 0) v)))))
    [ mk_bseq (snoc (snoc H (mk_hyp n mk_tnat))
                    (mk_hyp s (mk_natk2nat (mk_var n))))
              (mk_concl (mk_dec (mk_apply2 B (mk_var n) (mk_var s))) d),
      mk_bseq (snoc H (mk_hyp s mk_nat2nat))
              (mk_conclax (mk_squash
                             (mk_exists mk_tnat
                                        n
                                        (mk_apply2 B (mk_var n) (mk_seq2kseq (mk_var s) (mk_var n) v))))),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_natk2nat (mk_var n))))
                    (mk_hyp m (mk_apply2 B (mk_var n) (mk_var s))))
              (mk_concl (mk_apply2 X (mk_var n) (mk_var s)) e),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_natk2nat (mk_var n))))
                    (mk_hyp x (mk_all
                                 mk_tnat
                                 m
                                 (mk_squash (mk_apply2 X (mk_plus1 (mk_var n)) (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))))
              (mk_conclax (mk_apply2 X (mk_var n) (mk_var s)))
    ]
    [].

Lemma rule_bar_induction_nat_true {o} :
  forall lib (f X c B d e : @NTerm o)
         (s n m v x : NVar)
         (H : @barehypotheses o)
         (dxv : x <> v)
         (dsv : s <> v)
         (dnv : n <> v)
         (dnv : m <> v)
         (dnm : n <> m)
         (dsm : s <> m)
         (nvc : !LIn v (free_vars c))
         (nnB : !LIn n (free_vars B))
         (nsB : !LIn s (free_vars B)),
    rule_true lib (rule_bar_induction_nat f X c B d e s n m v x H).
Proof.
  unfold rule_bar_induction_nat, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp_dec].
  destruct Hyp0 as [wf2 hyp_bar].
  destruct Hyp1 as [wf3 hyp_imp].
  destruct Hyp2 as [wf4 hyp_ind].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (s <> n
          # s <> x
          # n <> x
          # !LIn x (free_vars c)
          # !LIn s (free_vars c)
          # !LIn n (free_vars c)
          # !LIn x (free_vars X)
          # !LIn s (free_vars X)
          # !LIn n (free_vars X)
          # !LIn m (free_vars X)
          # !LIn x (vars_hyps H)
          # !LIn s (vars_hyps H)
          # !LIn n (vars_hyps H)) as vhyps.

  clear hyp_dec hyp_bar hyp_ind hyp_imp.
  dwfseq.
  assert (forall x : NVar, LIn x (free_vars c) -> x <> v -> LIn x (vars_hyps H)) as imp.
  { introv h1 h2.
    apply cg.
    repeat (first [rw remove_nvars_cons_r|rw remove_nvars_app_r]).
    allrw memvar_singleton.
    allrw <- beq_var_refl.
    allrw remove_nvars_nil_r; allrw app_nil_r.
    rw in_remove_nvars; rw in_single_iff; sp. }
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nsn vhyps ].
  destruct vhyps as [ nsx vhyps ].
  destruct vhyps as [ nnx vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nsc vhyps ].
  destruct vhyps as [ nnc vhyps ].
  destruct vhyps as [ nxX vhyps ].
  destruct vhyps as [ nsX vhyps ].
  destruct vhyps as [ nnX vhyps ].
  destruct vhyps as [ nmX vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nsH nnH ].
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (lsubstc_mk_seq2kseq c 0 v w3 s1 c3) as sc1.
  repeat (autodimp sc1 hyp).
  exrepnd.
  rw sc1.

  pose proof (lsubstc_mk_seq2kseq c 0 v w3 s2 c7) as sc2.
  autodimp sc2 hyp.
  exrepnd.
  rw sc2.

  clear sc1 sc2.
  clear_irr.
  clear_wf_hyps.

  rw @tequality_mkc_squash.
  rw @member_mkc_squash.

  assert (!LIn n (dom_csub s1)) as nns1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn n (dom_csub s2)) as nns2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (!LIn s (dom_csub s1)) as nss1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn s (dom_csub s2)) as nss2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (!LIn x (dom_csub s1)) as nxs1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn x (dom_csub s2)) as nxs2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (wf_term B) as wB.
  { clear hyp_dec.
    allrw @wf_dec.
    allrw <- @wf_apply2_iff; sp.
  }

  assert (cover_vars B s1 # cover_vars B s2) as cB.
  { clear hyp_dec.
    allrw @covered_dec.
    allrw @covered_apply2; repnd.
    allrw @vars_hyps_snoc; allsimpl.
    apply covered_snoc_implies in ct5; auto.
    apply covered_snoc_implies in ct5; auto.
    dands.
    - eapply s_cover_typ1;[exact ct5|exact sim].
    - eapply s_cover_typ1;[exact ct5|].
      apply similarity_sym in sim;[exact sim|]; auto.
  }
  destruct cB as [cB1 cB2].


  assert (forall k seq1 seq2 s1a s2a cB1 cB2,
            similarity lib s1a s2a H
            -> hyps_functionality lib s1a H
            -> eq_kseq lib seq1 seq2 k
            -> tequality
                 lib
                 (mkc_apply2 (lsubstc B wB s1a cB1) (mkc_nat k) seq1)
                 (mkc_apply2 (lsubstc B wB s2a cB2) (mkc_nat k) seq2)) as Bfunc.
  { introv sim0 hf0 eqk.
    vr_seq_true in hyp_dec.
    pose proof (hyp_dec
                  (snoc (snoc s1a (n,mkc_nat k)) (s,seq1))
                  (snoc (snoc s2a (n,mkc_nat k)) (s,seq2)))
      as h; clear hyp_dec.
    repeat (autodimp h hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto;
           apply similarity_dom in sim'3; repnd; rw sim'0; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto;
           apply similarity_dom in sim'3; repnd; rw sim'3; auto
          |].
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfn.
      { apply wf_term_mk_natk2nat; auto. }
      assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1a (n,mkc_nat k))) as cvn.
      { apply cover_vars_mk_natk2nat.
        apply cover_vars_var.
        rw @dom_csub_snoc.
        rw in_snoc; simpl; sp. }
      sim_snoc.
      dands; auto.

      { pose proof (cover_vars_mk_tnat s1a) as cvs1.
        pose proof (@wf_tnat o) as wftn.
        sim_snoc.
        dands; auto.
        allrw @lsubstc_mkc_tnat.
        apply equality_in_tnat_nat.
      }

      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;
           apply lsubstc_mk_natk2nat_sp2; auto];
        auto.
      apply similarity_dom in sim0; repnd.
      rw sim1; auto.
    }

    exrepnd.
    clear h1.
    unfold mk_dec in h0.
    lsubst_tac.
    apply tequality_mkc_or in h0; repnd; auto.
  }

  pose proof (bar_induction_meta4
                lib
                (fun_sim_eq lib s1 H B wB)
                (fun_sim_eq lib s1 H X w0)
                (lsubstc B wB s1 cB1)
                (lsubstc X w0 s1 c0)
                (lsubstc c wt s1 ct3)
                v)
    as bi.

  repeat (autodimp bi hyp);
    [idtac
    |idtac
    |idtac
    |pose proof (bi (lsubstc X w0 s2 c5) (seq2kseq (lsubstc c wt s2 ct4) 0 v)) as h;
      allrw <- @mkc_zero_eq;
      repeat (autodimp h hyp);[apply eq_kseq_seq2kseq_0|idtac|repnd; dands; complete auto];
      exists s2 c5;
      dands; complete auto].

  - intros seq1 iss.

    vr_seq_true in hyp_bar.
    pose proof (hyp_bar
                  (snoc s1 (s,seq1))
                  (snoc s1 (s,seq1)))
      as hf; clear hyp_bar.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;
          apply lsubstc_mk_nat2nat; auto
        |].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;
          apply lsubstc_mk_nat2nat; auto
        |].
      apply type_nat2nat.
    }

    { assert (@wf_term o mk_nat2nat) as wfn.
      { apply wf_term_mk_nat2nat; auto. }
      assert (cover_vars mk_nat2nat s1) as cvn.
      { apply cover_vars_mk_nat2nat. }
      sim_snoc.
      dands; auto.
      { eapply similarity_refl; eauto. }
      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;
           apply lsubstc_mk_nat2nat; auto].
      auto.
    }

    exrepnd.
    clear hf0.
    lsubst_tac.
    apply equality_in_mkc_squash in hf1; exrepnd.
    clear hf0 hf2.
    allunfold @mk_exists.
    lsubst_tac.
    allrw @lsubstc_mkc_tnat.
    apply inhabited_product in hf1; exrepnd.
    clear hf2.

    apply member_tnat_implies_computes in hf1; exrepnd.

    exists k.
    introv eqs fse.
    unfold fun_sim_eq in fse; exrepnd; subst.

    repeat substc_lsubstc_vars3.
    lsubst_tac.
    clear_wf_hyps.
    proof_irr.

    pose proof (lsubstc_mk_seq2kseq2
                  (mk_var s) (mk_var n) v w6
                  ((n, a) :: snoc s1 (s, seq1)) c10) as ss.
    simpl in ss.
    repeat (autodimp ss hyp); try (complete (intro xx; repndors; tcsp)).
    exrepnd.
    rw ss1 in hf3.
    clear ss1.

    clear_wf_hyps.
    proof_irr.
    lsubst_tac.

    eapply inhabited_type_cequivc in hf3;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |apply computes_to_valc_implies_cequivc;exact hf2
         |apply cequivc_refl]
      ].
    eapply inhabited_type_cequivc in hf3;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |apply cequivc_refl
         |apply implies_cequivc_seq2kseq2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact hf2]
         ]
      ].
    allrw @seq2kseq2_as_seq2kseq2.
    dands; auto.

  - intros k seq1 iss sb C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.
    unfold meta2_fun_on_seq in sb.
    rename fse0 into sim0.

    assert (cover_vars B s0) as cB0.
    { eapply similarity_cover_vars;[exact sim0|]; auto. }

    pose proof (sb (lsubstc B wB s0 cB0) seq2) as h; clear sb.
    repeat (autodimp h hyp).
    { exists s0 cB0; dands; auto. }
    repnd.

    unfold inhabited_type in h0; exrepnd.
    rename h1 into mem.
    rename h into teq.

    vr_seq_true in hyp_imp.
    pose proof (hyp_imp
                  (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (m,t))
                  (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (m,t)))
      as hf.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'2.
        eapply alphaeqc_preserving_equality in sim'1;
          [|apply lsubstc_mk_natk2nat_sp2; auto].
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_apply2;
            [apply cequivc_refl
            |exact sim'2
            |apply cequivc_refl]
          |].
        auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; cpx.
        assert (!LIn n (dom_csub s2a)) as nns2a.
        { apply similarity_dom in sim'3; repnd.
          rw sim'3; auto. }
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        rw @lsubstc_mkc_tnat in sim'1.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (wf_term (mk_apply2 B (mk_var n) (mk_var s))) as wfn.
      { apply wf_apply2; eauto 3 with slow. }
      assert (cover_vars (mk_apply2 B (mk_var n) (mk_var s)) (snoc (snoc s1 (n,mkc_nat k)) (s,seq1))) as cvn.
      { apply cover_vars_apply2.
        repeat (rw @cover_vars_var_iff).
        repeat (rw @dom_csub_snoc); simpl.
        repeat (rw in_snoc).
        dands; tcsp.
        repeat (apply cover_vars_snoc_weak); auto. }
      sim_snoc.
      dands; auto.

      { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfk.
        { apply wf_term_mk_natk2nat; auto. }
        assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n,mkc_nat k))) as cvk.
        { apply cover_vars_mk_natk2nat.
          apply cover_vars_var_iff.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); sp. }
        sim_snoc.
        dands; auto.

        { assert (@wf_term o mk_tnat) as wft.
          { eauto 3 with slow. }
          assert (cover_vars mk_tnat s1) as cvt.
          { apply cover_vars_mk_tnat. }
          sim_snoc.
          dands; auto.
          allrw @lsubstc_mkc_tnat.
          eauto 3 with slow.
        }

        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto].
        auto.
      }

      { lsubst_tac; auto. }
    }

    exrepnd.
    lsubst_tac.
    apply inhabited_type_if_equality in hf1.
    unfold meta_fun_on_seq.
    dands; auto.

  - intros k seq1 iss ind C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.

    vr_seq_true in hyp_ind.

    pose proof (hyp_ind
                  (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (x,lam_axiom))
                  (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (x,lam_axiom)))
      as hf; clear hyp_ind.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        allunfold @mk_all.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'2.
        eapply alphaeqc_preserving_equality in sim'1;
          [|apply lsubstc_mk_natk2nat_sp2; auto].

        apply tequality_function; dands.
        { apply tnat_type. }
        introv en.
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply equality_in_tnat in en.
        unfold equality_of_nat in en; exrepnd; spcast.

        apply tequality_mkc_squash.

        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;
            apply implies_cequivc_apply2;
            [apply cequivc_refl
            |apply cequivc_lsubstc_mk_plus1_sp1;auto
            |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
             exact en1]
          |].

        assert (!LIn n (dom_csub s2a0)) as nin2.
        { apply similarity_dom in sim'4; repnd.
          rw sim'4; auto. }

        assert (!LIn s (dom_csub s2a0)) as nis2.
        { apply similarity_dom in sim'4; repnd.
          rw sim'4; auto. }

        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;
            apply implies_cequivc_apply2;
            [apply cequivc_refl
            |apply cequivc_lsubstc_mk_plus1_sp2; auto;
             apply cequivc_sym;exact sim'2
            |apply cequivc_lsubstc_mk_update_seq_sp2;auto;
             [exact en0
             |apply cequivc_nat_implies_computes_to_valc;
               apply cequivc_sym;exact sim'2]
            ]
          |].

        pose proof (ind k0) as h; clear ind.
        unfold meta2_fun_on_upd_seq in h.
        unfold meta2_fun_on_seq in h; repnd.

        pose proof (h (lsubstc X w0 s2a0 c27) (update_seq t2 k k0 v)) as q; clear h.
        repeat (autodimp q hyp).
        { apply eq_kseq_update; auto. }
        { exists s2a0 c27; dands; auto. }
        repnd; auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        assert (!LIn n (dom_csub s2a)) as nns2a.
        { apply similarity_dom in sim'3; repnd.
          rw sim'3; auto. }
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        rw @lsubstc_mkc_tnat in sim'1.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (wf_term (mk_all mk_tnat m
                              (mk_squash
                                 (mk_apply2 X (mk_plus1 (mk_var n))
                                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))) as wa.
      { apply wf_function; auto.
        apply wf_squash.
        apply wf_apply2; auto. }
      assert (cover_vars (mk_all mk_tnat m
                              (mk_squash
                                 (mk_apply2 X (mk_plus1 (mk_var n))
                                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))
                         (snoc (snoc s1 (n, mkc_nat k)) (s, seq1))) as ca.
      { apply cover_vars_function; dands; auto.
        { apply cover_vars_mk_tnat. }
        apply cover_vars_upto_squash.
        apply cover_vars_upto_apply2; dands; auto.
        { repeat (rw @csub_filter_snoc).
          allrw memvar_singleton.
          boolvar;tcsp;GC;[].
          repeat (apply cover_vars_upto_snoc_weak).
          apply cover_vars_upto_csub_filter_disjoint; auto.
          apply disjoint_singleton_r; auto. }
        { apply cover_vars_upto_add; dands; eauto 3 with slow.
          repeat (rw @csub_filter_snoc).
          allrw memvar_singleton.
          boolvar;tcsp;GC;[].
          apply cover_vars_upto_var; simpl.
          repeat (rw @dom_csub_snoc).
          repeat (rw in_snoc;simpl).
          sp. }
        { unfold mk_update_seq.
          apply cover_vars_upto_lam.
          rw @csub_filter_swap.
          rw <- @csub_filter_app_r; simpl.
          repeat (rw @csub_filter_snoc).
          allrw memvar_cons; simpl.
          boolvar;tcsp;GC;[].
          apply cover_vars_upto_int_eq; dands.
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_apply; dands.
            { apply cover_vars_upto_var; simpl.
              repeat (rw @dom_csub_snoc).
              repeat (rw in_snoc;simpl).
              sp. }
            { apply cover_vars_upto_var; simpl.
              repeat (rw @dom_csub_snoc).
              repeat (rw in_snoc;simpl).
              sp. }
          }
        }
      }
      sim_snoc.
      dands; auto.

      { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfk.
        { apply wf_term_mk_natk2nat; auto. }
        assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n,mkc_nat k))) as cvk.
        { apply cover_vars_mk_natk2nat.
          apply cover_vars_var_iff.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); sp. }
        sim_snoc.
        dands; auto.

        { assert (@wf_term o mk_tnat) as wft.
          { eauto 3 with slow. }
          assert (cover_vars mk_tnat s1) as cvt.
          { apply cover_vars_mk_tnat. }
          sim_snoc.
          dands; auto.
          allrw @lsubstc_mkc_tnat.
          eauto 3 with slow.
        }

        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto].
        auto.
      }

      { unfold mk_all.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_in_function.
        dands; auto.

        { apply tnat_type. }

        { introv en.
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          apply equality_in_tnat in en.
          unfold equality_of_nat in en; exrepnd; spcast.

          apply tequality_mkc_squash.

          eapply tequality_respects_cequivc_left;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp1;auto
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en1]
            |].

          eapply tequality_respects_cequivc_right;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp2; auto;
               apply cequivc_sym;exact sim'2
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en0]
            |].

          pose proof (ind k0) as h; clear ind.
          unfold meta2_fun_on_upd_seq in h.
          unfold meta2_fun_on_seq in h; repnd.

          pose proof (h (lsubstc X w0 s1 c0) (update_seq seq1 k k0 v)) as q; clear h.
          repeat (autodimp q hyp).
          { apply eq_kseq_update; auto.
            eapply eq_kseq_left; eauto. }
          { exists s1 c0; dands; auto.
            eapply similarity_refl; eauto. }
          repnd; auto.
        }

        { introv en.
          repeat substc_lsubstc_vars3.
          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].

          clear_wf_hyps.
          proof_irr.
          lsubst_tac.

          apply equality_in_mkc_squash; dands; spcast;
          try (apply computes_to_valc_refl; eauto 3 with slow).

          apply equality_in_tnat in en.
          unfold equality_of_nat in en; exrepnd; spcast.

          eapply inhabited_type_cequivc;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp1;auto
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en1]
            |].

          pose proof (ind k0) as h; clear ind.
          unfold meta2_fun_on_upd_seq in h.
          unfold meta2_fun_on_seq in h; repnd.

          pose proof (h (lsubstc X w0 s1 c0) (update_seq seq1 k k0 v)) as q; clear h.
          repeat (autodimp q hyp).
          { apply eq_kseq_update; auto.
            eapply eq_kseq_left; eauto. }
          { exists s1 c0; dands; auto.
            eapply similarity_refl; eauto. }
          repnd; auto.
        }
      }
    }

    exrepnd.
    lsubst_tac.
    apply inhabited_type_if_equality in hf1.
    dands; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../close/" "../per/" "../cequiv/" "../terms/" "../computation/" "../continuity/" "../util/")
*** End:
*)
