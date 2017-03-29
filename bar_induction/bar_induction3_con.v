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


Require Export bar_induction2_con.
Require Export subst_tacs.
Require Export sequents_equality.
Require Export per_props_isect.
Require Export lsubstc_vars.


(* !!MOVE *)
Lemma eq_kseq_trans {o} :
  forall lib (s1 s2 s3 : @CTerm o) n,
    eq_kseq lib s1 s2 n
    -> eq_kseq lib s2 s3 n
    -> eq_kseq lib s1 s3 n.
Proof.
  introv eqk1 eqk2.
  unfold eq_kseq in *.
  eapply equality_trans; eauto.
Qed.

(* !!MOVE *)
Lemma type_natk2nat_if_member_nat {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    -> type lib (natk2nat t).
Proof.
  introv mem.
  apply tequality_natk2nat.
  apply member_tnat_implies_computes in mem; exrepnd.
  exists (Z.of_nat k) (Z.of_nat k).
  rewrite <- mkc_nat_eq; dands; spcast; auto.
  introv lek.
  destruct (Z.le_gt_cases (Z.of_nat k) k0) as [d|d]; tcsp.
Qed.

(* !!MOVE *)
Lemma is_seq_implies_is_kseq {o} :
  forall lib (s : @CTerm o) n,
    is_seq lib s
    -> is_kseq lib s n.
Proof.
  introv iss.
  unfold is_seq in iss; unfold is_kseq, eq_kseq.
  apply equality_nat2nat_to_natk2nat; auto.
  apply nat_in_nat.
Qed.


(**

  Bar induction, where
    X is the proposition
    B is the bar
    ext(s,n,t) = \m. if m=n then t else s m
<<
   H |- ↓(X 0 (norm c 0))

     By bar_induction B R i a s x m n con t

     H, n:ℕ, s: ℕn → ℕ |- (B n s) ∈ Type(i)                                   // B is a well-formed predicate on finite sequences
     H, n:ℕ, s: ℕn → ℕ |- (R n s) ∈ Type(i)                                   // R is a well-formed predicate on finite sequences
     H, s:ℕ → ℕ, con:(∩m:ℕ.↓(R m s)) |- ↓(∃n:ℕ. B n s)                       // B is a bar
     H, n:ℕ, s:ℕn → ℕ, con:↓(R n s), m: B n s |- X n s                         // Base case: the conclusion is true at the bar
     H, n:ℕ, s:ℕn → ℕ, x:(∩m:ℕ.↓(R n s) → ↓(X (n + 1) (ext(s,n,m)))) |- X n s   // induction case
>>

*)

Definition rule_bar_induction_nat_con {o}
           (f X c B R e : @NTerm o)
           (s n m v x con : NVar)
           (i : nat)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_squash (mk_apply2 X mk_zero (mk_seq2kseq c (mk_nat 0) v)))))
    [ (* well-formedness of the bar B *)
      mk_bseq (snoc (snoc H (mk_hyp n mk_tnat))
                    (mk_hyp s (mk_natk2nat (mk_var n))))
              (mk_conclax (mk_member (mk_apply2 B (mk_var n) (mk_var s)) (mk_uni i))),

      (* well-formedness of the condition R *)
      mk_bseq (snoc (snoc H (mk_hyp n mk_tnat))
                    (mk_hyp s (mk_natk2nat (mk_var n))))
              (mk_conclax (mk_member (mk_apply2 R (mk_var n) (mk_var s)) (mk_uni i))),

      (* B is a bar *)
      mk_bseq (snoc (snoc H (mk_hyp s mk_nat2nat))
                    (mk_hyp con (mk_isect
                                   mk_tnat
                                   m
                                   (mk_squash (mk_apply2 R (mk_var m) (mk_var s))))))
              (mk_conclax (mk_squash
                             (mk_exists
                                mk_tnat
                                n
                                (mk_apply2 B (mk_var n) (mk_var s))))),

      (* base case *)
      mk_bseq (snoc (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                                (mk_hyp s (mk_natk2nat (mk_var n))))
                          (mk_hyp con (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))))
                    (mk_hyp m (mk_apply2 B (mk_var n) (mk_var s))))
              (mk_concl (mk_apply2 X (mk_var n) (mk_var s)) e),

      (* induction case *)
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_natk2nat (mk_var n))))
                    (mk_hyp x (mk_isect
                                 mk_tnat
                                 m
                                 (mk_ufun
                                    (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))
                                    (mk_squash (mk_apply2 X (mk_plus1 (mk_var n)) (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v)))))))
              (mk_conclax (mk_apply2 X (mk_var n) (mk_var s)))
    ]
    [].

Lemma rule_bar_induction_nat_con_true {o} :
  forall lib (f X c B R d e : @NTerm o)
         (s n m v x con : NVar)
         (i : nat)
         (H : @barehypotheses o)
         (dxv : x <> v)
         (dsv : s <> v)
         (dnv : n <> v)
         (dmv : m <> v)
         (dconv : con <> v)
         (dnm : n <> m)
         (dsm : s <> m)
         (nvc : !LIn v (free_vars c))
         (nnB : !LIn n (free_vars B))
         (nsB : !LIn s (free_vars B))
         (nnR : !LIn n (free_vars R))
         (nsR : !LIn s (free_vars R)),
    rule_true lib (rule_bar_induction_nat_con f X c B R e s n m v x con i H).
Proof.
  unfold rule_bar_induction_nat_con, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp_wfb].
  destruct Hyp0 as [wf2 hyp_wfr].
  destruct Hyp1 as [wf3 hyp_bar].
  destruct Hyp2 as [wf4 hyp_imp].
  destruct Hyp3 as [wf5 hyp_ind].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (s <> n
          # s <> x
          # n <> x
          # con <> n
          # con <> s
          # con <> m
          # !LIn x (free_vars c)
          # !LIn s (free_vars c)
          # !LIn n (free_vars c)
          # !LIn con (free_vars c)
          # !LIn x (free_vars X)
          # !LIn s (free_vars X)
          # !LIn n (free_vars X)
          # !LIn m (free_vars X)
          # !LIn con (free_vars X)
          # !LIn con (free_vars B)
          # !LIn m (free_vars R)
          # !LIn x (vars_hyps H)
          # !LIn s (vars_hyps H)
          # !LIn n (vars_hyps H)
          # !LIn con (vars_hyps H)) as vhyps.

  {
    clear hyp_wfb hyp_wfr hyp_bar hyp_ind hyp_imp.
    dwfseq.
    assert (forall x : NVar, LIn x (free_vars c) -> x <> v -> LIn x (vars_hyps H)) as imp.
    {
      introv h1 h2.
      apply cg.
      repeat (first [rw remove_nvars_cons_r|rw remove_nvars_app_r]).
      allrw memvar_singleton.
      allrw <- beq_var_refl.
      allrw remove_nvars_nil_r; allrw app_nil_r.
      rw in_remove_nvars; rw in_single_iff; sp.
    }
    sp; GC;
      try (complete (discover; allapply @subset_hs_vars_hyps; sp));
      try (complete (pose proof (ct10 con) as xx; autodimp xx hyp;
                     repeat (rw in_snoc in xx); repndors; tcsp));
      try (complete (pose proof (ct9 m) as xx; autodimp xx hyp;
                     repeat (rw in_snoc in xx); repndors; tcsp)).
  }

  destruct vhyps as [ nsn vhyps ].
  destruct vhyps as [ nsx vhyps ].
  destruct vhyps as [ nnx vhyps ].
  destruct vhyps as [ nconn vhyps ].
  destruct vhyps as [ ncons vhyps ].
  destruct vhyps as [ nconm vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nsc vhyps ].
  destruct vhyps as [ nnc vhyps ].
  destruct vhyps as [ nconc vhyps ].
  destruct vhyps as [ nxX vhyps ].
  destruct vhyps as [ nsX vhyps ].
  destruct vhyps as [ nnX vhyps ].
  destruct vhyps as [ nmX vhyps ].
  destruct vhyps as [ nconX vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nsH vhyps ].
  destruct vhyps as [ nnH nconH ].
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

  assert (!LIn con (dom_csub s1)) as ncons1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn con (dom_csub s2)) as ncons2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (wf_term B) as wB.
  { clear hyp_wfb.
    allrw @wf_member_iff2.
    allrw <- @wf_apply2_iff; sp.
  }

  assert (wf_term R) as wR.
  { clear hyp_wfr.
    allrw @wf_member_iff2.
    allrw <- @wf_apply2_iff; sp.
  }

  assert (cover_vars R s1 # cover_vars R s2) as cR.
  { clear hyp_wfr.
    allrw @covered_member.
    allrw @covered_apply2; repnd.
    allrw @vars_hyps_snoc; allsimpl.
    apply covered_snoc_implies in ct7; auto.
    apply covered_snoc_implies in ct7; auto.
    dands.
    - eapply s_cover_typ1;[exact ct7|exact sim].
    - eapply s_cover_typ1;[exact ct7|].
      apply similarity_sym in sim;[exact sim|]; auto.
  }
  destruct cR as [cR1 cR2].

  assert (cover_vars B s1 # cover_vars B s2) as cB.
  { clear hyp_wfb.
    allrw @covered_member.
    allrw @covered_apply2; repnd.
    allrw @vars_hyps_snoc; allsimpl.
    apply covered_snoc_implies in ct7; auto.
    apply covered_snoc_implies in ct7; auto.
    dands.
    - eapply s_cover_typ1;[exact ct7|exact sim].
    - eapply s_cover_typ1;[exact ct7|].
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
    vr_seq_true in hyp_wfb.
    pose proof (hyp_wfb
                  (snoc (snoc s1a (n,mkc_nat k)) (s,seq1))
                  (snoc (snoc s2a (n,mkc_nat k)) (s,seq2)))
      as h; clear hyp_wfb.
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
    lsubst_tac.
    apply tequality_in_uni_implies_tequality in h0; auto.
    apply member_if_inhabited in h1.
    apply member_in_uni in h1; auto.
  }


  assert (forall k seq1 seq2 s1a s2a cR1 cR2,
            similarity lib s1a s2a H
            -> hyps_functionality lib s1a H
            -> eq_kseq lib seq1 seq2 k
            -> tequality
                 lib
                 (mkc_apply2 (lsubstc R wR s1a cR1) (mkc_nat k) seq1)
                 (mkc_apply2 (lsubstc R wR s2a cR2) (mkc_nat k) seq2)) as Rfunc.
  { introv sim0 hf0 eqk.
    vr_seq_true in hyp_wfr.
    pose proof (hyp_wfr
                  (snoc (snoc s1a (n,mkc_nat k)) (s,seq1))
                  (snoc (snoc s2a (n,mkc_nat k)) (s,seq2)))
      as h; clear hyp_wfr.
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
    lsubst_tac.
    apply tequality_in_uni_implies_tequality in h0; auto.
    apply member_if_inhabited in h1.
    apply member_in_uni in h1; auto.
  }

  pose proof (bar_induction_meta4_con
                lib
                (fun_sim_eq lib s1 H B wB)
                (fun_sim_eq lib s1 H R wR)
                (fun_sim_eq lib s1 H X w0)
                (lsubstc B wB s1 cB1)
                (lsubstc R wR s1 cR1)
                (lsubstc X w0 s1 c0)
                (lsubstc c wt s1 ct4)
                v)
    as bi.

  repeat (autodimp bi hyp);
    [idtac (* well-formedness or R *)
    |idtac (* bar *)
    |idtac (* base case *)
    |idtac (* inductive case *)
    |(* conclusion *)
    pose proof (bi (lsubstc X w0 s2 c5) (seq2kseq (lsubstc c wt s2 ct5) 0 v)) as h;
    allrw <- @mkc_zero_eq;
    repeat (autodimp h hyp);[apply eq_kseq_seq2kseq_0|idtac|repnd; dands; complete auto];
    exists s2 c5;
    dands; complete auto
    ].

  - (* well-formedness of R *)
    introv eqk fos eqk1 fsim.
    unfold meta2_fun_on_seq in fos.
    pose proof (fos A2 s4) as q; clear fos.
    repeat (autodimp q hyp).
    { eapply eq_kseq_trans; eauto. }
    repnd.

    pose proof (Rfunc n0 s0 s3 s1 s1 cR1 cR1) as hr.
    repeat (autodimp hr hyp).
    { eapply similarity_refl; eauto. }

    dands.

    { eapply inhabited_type_tequality; eauto. }

    { eapply tequality_trans;[|exact q].
      apply tequality_sym; auto. }

  - (* base hypothesis *)
    intros seq1 iss mR.

    vr_seq_true in hyp_bar.
    pose proof (hyp_bar
                  (snoc (snoc s1 (s,seq1)) (con,mkc_axiom))
                  (snoc (snoc s1 (s,seq1)) (con,mkc_axiom)))
      as hf; clear hyp_bar.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.

        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.

        eapply alphaeqc_preserving_equality in sim'1;[|apply lsubstc_mk_nat2nat].

        lsubst_tac.
        apply tequality_isect.
        autorewrite with slow.
        dands; eauto 2 with slow.
        { apply tnat_type. }
        introv equn.
        repeat substc_lsubstc_vars3.
        lsubst_tac_c.
        apply tequality_mkc_squash.

        apply equality_in_tnat in equn.
        unfold equality_of_nat in equn; exrepnd; spcast.


        pose proof (Rfunc k t1 t2 s1a s2a cR1 c22) as hr.
        repeat (autodimp hr hyp).
        { unfold eq_kseq.
          apply equality_nat2nat_to_natk2nat; auto.
          apply nat_in_nat. }

        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;
           apply implies_cequivc_apply2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact equn1
           |apply cequivc_refl]
          |].
        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;
           apply implies_cequivc_apply2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact equn0
           |apply cequivc_refl]
          |].
        auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      {
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
    }

    {
      assert (wf_term (mk_isect mk_tnat m (mk_squash (mk_apply2 R (mk_var m) (mk_var s))))) as wfi.
      {
        apply wf_isect; eauto 2 with slow.
        apply wf_squash.
        apply wf_apply2; eauto 2 with slow.
      }

      assert (cover_vars (mk_isect mk_tnat m (mk_squash (mk_apply2 R (mk_var m) (mk_var s))))
                         (snoc s1 (s, seq1))) as covi.
      {
        apply cover_vars_isect; dands; eauto 2 with slow.
        apply cover_vars_upto_squash.
        rewrite csub_filter_snoc; rewrite memvar_singleton; boolvar; tcsp.
        apply cover_vars_upto_apply2; dands; eauto 2 with slow.
        { apply cover_vars_upto_snoc_weak.
          apply cover_vars_upto_csub_filter_disjoint; eauto 2 with slow.
          apply disjoint_singleton_r; auto. }
        { apply cover_vars_upto_var; simpl; tcsp. }
        { apply cover_vars_upto_var; simpl.
          rewrite dom_csub_snoc; simpl; rw in_snoc; tcsp. }
      }
      sim_snoc2; dands; auto.

      {
        assert (cover_vars mk_nat2nat s1) as cvn.
        { apply cover_vars_mk_nat2nat. }
        sim_snoc2; dands; auto.
        { apply similarity_refl in sim; auto. }
        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym;
            apply lsubstc_mk_nat2nat; auto].
        auto.
      }

      lsubst_tac_c.
      apply member_in_isect.
      rewrite lsubstc_mk_tnat.
      dands; eauto 2 with slow.
      introv equn.
      repeat substc_lsubstc_vars3.
      lsubst_tac_c.
      rw @tequality_mkc_squash.
      rw @member_mkc_squash.

      apply equality_in_tnat in equn.
      unfold equality_of_nat in equn; exrepnd; spcast.
      pose proof (mR k (lsubstc R wR s1 cR1) seq1) as q.
      repeat (autodimp q hyp).

      {
        apply is_seq_implies_is_kseq.
        unfold eq_kseq; auto.
      }

      {
        unfold fun_sim_eq.
        exists s1 cR1; dands; auto.
        apply similarity_refl in sim; auto.
      }

      repnd.
      dands; auto.

      {
        eapply inhabited_type_cequivc;
          [apply cequivc_sym;
           apply implies_cequivc_apply2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact equn1
           |apply cequivc_refl]
          |].
        auto.
      }

      {
        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;
           apply implies_cequivc_apply2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact equn1
           |apply cequivc_refl]
          |].
        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;
           apply implies_cequivc_apply2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact equn0
           |apply cequivc_refl]
          |].
        auto.
      }
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

    pose proof (Bfunc k seq1 (seq2kseq seq1 k v) s1 s1 cB1 cB1) as h.
    repeat (autodimp h hyp); eauto 3 with slow.

    { eapply similarity_refl; eauto. }

    { apply seq2kseq_prop3; auto.
      apply is_seq_implies_is_kseq; auto. }

    eapply inhabited_type_cequivc in hf3;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |apply computes_to_valc_implies_cequivc;eauto
         |apply cequivc_refl]
      ].

    eapply inhabited_type_tequality in hf3;[|eauto].

    dands; auto.

  - (* base case *)
    intros k seq1 iss sr sb C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.
    unfold meta2_fun_on_seq in sb.
    unfold meta2_fun_on_seq in sr.
    rename fse0 into sim0.

    assert (cover_vars B s0) as cB0.
    { eapply similarity_cover_vars;[exact sim0|]; auto. }

    assert (cover_vars R s0) as cR0.
    { eapply similarity_cover_vars;[exact sim0|]; auto. }

    pose proof (sb (lsubstc B wB s0 cB0) seq2) as hb; clear sb.
    repeat (autodimp hb hyp).
    { exists s0 cB0; dands; auto. }
    repnd.

    pose proof (sr (lsubstc R wR s0 cR0) seq2) as hr; clear sr.
    repeat (autodimp hr hyp).
    { exists s0 cR0; dands; auto. }
    repnd.

    unfold inhabited_type in hb0; exrepnd.
    rename hb1 into memb.
    rename hb  into teqb.
    rename hr0 into inhr.
    rename hr  into teqr.

    vr_seq_true in hyp_imp.
    pose proof (hyp_imp
                  (snoc (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (con,mkc_axiom)) (m,t))
                  (snoc (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (con,mkc_axiom)) (m,t)))
      as hf.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'4; simpl in sim'4.
        exrepnd; subst; ginv; inj.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'3.
        eapply alphaeqc_preserving_equality in sim'2;
          [|apply lsubstc_mk_natk2nat_sp2; auto].
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_apply2;
            [apply cequivc_refl
            |exact sim'3
            |apply cequivc_refl]
          |].
        auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

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
        apply tequality_mkc_squash.
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
      assert (cover_vars (mk_apply2 B (mk_var n) (mk_var s)) (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (con,mkc_axiom))) as cvn.
      { apply cover_vars_apply2.
        repeat (rw @cover_vars_var_iff).
        repeat (rw @dom_csub_snoc); simpl.
        repeat (rw in_snoc).
        dands; tcsp.
        repeat (apply cover_vars_snoc_weak); auto. }
      sim_snoc2.
      dands; auto.

      { assert (wf_term (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))) as wfs.
        { apply wf_squash.
          apply wf_apply2; auto. }
        assert (cover_vars (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))
                           (snoc (snoc s1 (n, mkc_nat k)) (s, seq1))) as covs.
        { apply cover_vars_squash.
          apply cover_vars_apply2; dands; eauto 3 with slow.
          { repeat (apply cover_vars_snoc_weak; auto). }
          { apply cover_vars_snoc_weak.
            apply cover_vars_var_iff.
            rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
          { apply cover_vars_var_iff.
            rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
        }
        sim_snoc2; dands; auto.

        { assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n, mkc_nat k))) as covn.
          { apply cover_vars_mk_natk2nat.
            apply cover_vars_var_iff.
            rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
          sim_snoc2; dands; auto.

          { sim_snoc2; eauto 3 with slow.
            dands; auto.
            rw @lsubstc_mk_tnat.
            apply nat_in_nat. }

          { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto].
            auto. }
        }

        { lsubst_tac.
          apply member_mkc_squash; auto. }
      }

      { lsubst_tac; auto. }
    }

    exrepnd.
    lsubst_tac.
    apply inhabited_type_if_equality in hf1.
    unfold meta_fun_on_seq.
    dands; auto.

  - (* induction case *)
    intros k seq1 iss ind C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.

    vr_seq_true in hyp_ind.

    pose proof (hyp_ind
                  (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (x,mkc_axiom))
                  (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (x,mkc_axiom)))
      as hf; clear hyp_ind.
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

        apply tequality_isect; dands.
        { apply tnat_type. }
        introv en.
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply equality_in_tnat in en.
        unfold equality_of_nat in en; exrepnd; spcast.

        apply tequality_mkc_ufun; dands.

        {
          apply tequality_mkc_squash.
          eapply tequality_respects_cequivc_right;
            [apply implies_cequivc_apply2;
             [apply cequivc_refl
             |exact sim'2
             |apply cequivc_refl]
            |].

          pose proof (Rfunc k t1 t2 s1a s2a0 cR1 c44) as hr.
          repeat (autodimp hr hyp).
        }

        introv inh.
        rw @inhabited_squash in inh.

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

        autodimp h hyp.

        {
          introv eqk funsim.
          unfold fun_sim_eq in funsim; exrepnd; subst.
          dands; auto.
        }

        pose proof (h (lsubstc X w0 s2a0 c50) (update_seq t2 k k0 v)) as q; clear h.
        repeat (autodimp q hyp).
        { apply eq_kseq_update; auto. }
        { exists s2a0 c50; dands; auto. }
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


    { assert (wf_term
                (mk_isect
                   mk_tnat m
                   (mk_ufun
                      (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))
                      (mk_squash
                         (mk_apply2
                            X
                            (mk_plus1 (mk_var n))
                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v)))))) as wa.
      { apply wf_isect; auto.
        apply wf_ufun; dands; auto;
          apply wf_squash; apply wf_apply2; auto. }

      assert (cover_vars
                (mk_isect
                   mk_tnat m
                   (mk_ufun
                      (mk_squash (mk_apply2 R (mk_var n) (mk_var s)))
                      (mk_squash
                         (mk_apply2
                            X (mk_plus1 (mk_var n))
                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v)))))
                (snoc (snoc s1 (n, mkc_nat k)) (s, seq1))) as ca.
      { apply cover_vars_isect; dands; eauto 3 with slow.
        apply cover_vars_upto_ufun; dands; auto;
          apply cover_vars_upto_squash;
          apply cover_vars_upto_apply2; dands; eauto 3 with slow.
        { apply cover_vars_upto_csub_filter_snoc_weak.
          apply cover_vars_upto_csub_filter_snoc_weak.
          apply cover_vars_upto_csub_filter_disjoint; eauto 2 with slow.
          apply disjoint_singleton_r; auto. }
        { apply cover_vars_upto_var; simpl.
          rw @dom_csub_csub_filter.
          repeat (rw @dom_csub_snoc); simpl.
          rw in_remove_nvars; simpl.
          repeat (rw in_snoc).
          right; dands; tcsp. }
        { apply cover_vars_upto_var; simpl.
          rw @dom_csub_csub_filter.
          repeat (rw @dom_csub_snoc); simpl.
          rw in_remove_nvars; simpl.
          repeat (rw in_snoc).
          right; dands; tcsp. }
        { apply cover_vars_upto_csub_filter_snoc_weak.
          apply cover_vars_upto_csub_filter_snoc_weak.
          apply cover_vars_upto_csub_filter_disjoint; eauto 2 with slow.
          apply disjoint_singleton_r; auto. }
        { unfold mk_plus1.
          apply cover_vars_upto_add; dands; eauto 3 with slow.
          apply cover_vars_upto_var; simpl.
          rw @dom_csub_csub_filter.
          repeat (rw @dom_csub_snoc); simpl.
          rw in_remove_nvars; simpl.
          repeat (rw in_snoc).
          right; dands; tcsp. }
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

      { lsubst_tac.
        apply member_in_isect.
        rewrite lsubstc_mk_tnat.
        dands; eauto 2 with slow.
        introv en.
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply equality_in_tnat in en.
        unfold equality_of_nat in en; exrepnd; spcast.

        dands.

        {
          apply equality_in_ufun.
          dands.

          {
            apply tequality_mkc_squash.
            apply Rfunc; auto.
            { eapply similarity_refl; eauto. }
            { apply is_kseq_if_eq_kseq in eqs; tcsp. }
          }

          {
            introv inh.
            apply tequality_mkc_squash.
            rw @inhabited_squash in inh.

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
                exact en1]
              |].

            pose proof (ind k0) as h; clear ind.
            autodimp h hyp.

            {
              introv eqk funsim.
              unfold fun_sim_eq in funsim; exrepnd; subst.
              dands; auto.
            }

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

          {
            introv inh.
            rw @inhabited_squash in inh.
            apply member_mkc_squash.

            eapply inhabited_type_cequivc;
              [apply cequivc_sym;
               apply implies_cequivc_apply2;
               [apply cequivc_refl
               |apply cequivc_lsubstc_mk_plus1_sp1;auto
               |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
                exact en1]
              |].

            pose proof (ind k0) as h; clear ind.

            autodimp h hyp.

            {
              introv eqk funsim.
              unfold fun_sim_eq in funsim; exrepnd; subst.
              dands; auto.
            }

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

        {
          apply tequality_mkc_ufun.
          dands.

          {
            apply tequality_mkc_squash.
            apply Rfunc; auto.
            { eapply similarity_refl; eauto. }
            { apply is_kseq_if_eq_kseq in eqs; tcsp. }
          }

          introv inh.
          rw @inhabited_squash in inh.
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
          autodimp h hyp.

          {
            introv eqk funsim.
            unfold fun_sim_eq in funsim; exrepnd; subst.
            dands; auto.
          }

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
