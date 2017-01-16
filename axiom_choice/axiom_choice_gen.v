 (*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)

Require Export cnterm.
Require Export substc_more.
Require Export per_props4.
Require Export cequiv_cnterm.
Require Export sequents2.


Lemma member_nout_implies {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_nout
    -> {u : CNTerm , ccequivc lib t (cnterm2cterm u)}.
Proof.
  introv mem.
  apply equality_in_nout in mem; exrepnd.
  exists (cterm2cnterm u mem1).
  autorewrite with slow; auto.
Qed.

Lemma member_nout_iff {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_nout
    <=> {u : CNTerm , ccequivc lib t (cnterm2cterm u)}.
Proof.
  introv; split; intro h; try (apply member_nout_implies; auto);[].
  exrepnd.
  apply equality_in_nout.
  exists (cnterm2cterm u); dands; eauto 3 with slow.
Qed.

Lemma reduces_toc_eapply_ntseqc2ntseq {o} :
  forall lib s (t u : @CTerm o),
    reduces_toc lib t u
    -> reduces_toc
         lib
         (mkc_eapply (ntseqc2ntseq s) t)
         (mkc_eapply (ntseqc2ntseq s) u).
Proof.
  introv r.
  destruct_cterms.
  allunfold @reduces_toc; allsimpl.
  apply implies_eapply_red_aux; eauto 3 with slow.
Qed.

Lemma get_cterm_cnterm2cterm_is_ntseqc2seq {o} :
  forall (f : @ntseqc o) k,
    get_cterm (cnterm2cterm (f k)) = ntseqc2seq f k.
Proof.
  introv.
  unfold cnterm2cterm, ntseqc2seq; simpl.
  remember (f k) as t; destruct t; simpl; auto.
Qed.

Lemma reduces_toc_ntseqc2ntseq_step {o} :
  forall lib (f : @ntseqc o) k,
    reduces_toc lib (mkc_eapply (ntseqc2ntseq f) (mkc_nat k)) (cnterm2cterm (f k)).
Proof.
  introv.
  unfold reduces_toc; simpl.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; simpl; boolvar; try omega.
  rewrite Znat.Nat2Z.id.
  rewrite get_cterm_cnterm2cterm_is_ntseqc2seq; auto.
Qed.

Lemma implies_approx_eapply {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_eapply f a) (mk_eapply g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_eapply {o} :
  forall lib (f g a b : @CTerm o),
    cequivc lib f g
    -> cequivc lib a b
    -> cequivc lib (mkc_eapply f a) (mkc_eapply g b).
Proof.
  unfold cequivc.
  introv H1c H2c.
  destruct_cterms.
  allsimpl.
  apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_eapply; auto.
Qed.


(*

   forall m : nat, squash (exists n : NUBase, P(m,n))

   implies

   squash (exists f : nat -> NUBase, forall m : nat, squash (P (m, f m)))

 *)
Lemma axiom_of_choice_0NUB {o} :
  forall lib f m n (P : @CTerm o),
    n <> m
    -> f <> m
    -> (forall a b,
          member lib a mkc_tnat
          -> member lib b mkc_nout
          -> type lib (mkc_apply2 P a b))
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            m
            (mkcv_squash
               [m]
               (mkcv_exists
                  [m]
                  (mkcv_nout [m])
                  n
                  (mkcv_apply2 [n,m]
                               (mk_cv [n,m] P)
                               (mk_cv_app_l [n] [m] (mkc_var m))
                               (mk_cv_app_r [m] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_exists
            nat2nout
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               m
               (mkcv_squash
                  [m,f]
                  (mkcv_apply2 [m,f]
                               (mk_cv [m,f] P)
                               (mk_cv_app_r [f] [m] (mkc_var m))
                               (mkcv_apply [m,f]
                                           (mk_cv_app_l [m] [f] (mkc_var f))
                                           (mk_cv_app_r [f] [m] (mkc_var m))))))).
Proof.
  introv d1 d2 impp inh.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> inhabited_type
                 lib
                 (mkc_exists
                    mkc_nout
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] k)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 k k) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_nout_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> {j : CTerm
                , member lib j mkc_nout
                # inhabited_type lib (mkc_apply2 P k j)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

  (* First use FunctionalChoice_on to get an existential (a Coq function from terms to terms) *)

  pose proof (FunctionalChoice_on
                {k : CTerm & member lib k mkc_tnat}
                (@CTerm o)
                (fun k j =>
                   member lib j mkc_nout
                   # inhabited_type lib (mkc_apply2 P (projT1 k) j)))
    as fc.
  simphyps.
  autodimp fc hyp; tcsp;[].
  exrepnd.
  clear h.
  rename fc0 into fc.

  pose proof (FunctionalChoice_on
                {k : CTerm & member lib k mkc_nout}
                (@CNTerm o)
                (fun k j => ((projT1 k) ~=~(lib) (cnterm2cterm j))))
    as fcn.
  simphyps.
  autodimp fcn hyp; tcsp;[sp; simpl; apply member_nout_implies; auto; fail|].
  exrepnd.
  rename fcn0 into fcn.

  assert {c : ntseqc
          & forall a : CTerm,
              member lib a mkc_tnat
              -> (member lib (mkc_eapply (ntseqc2ntseq c) a) mkc_nout
                  # inhabited_type lib (mkc_apply2 P a (mkc_eapply (ntseqc2ntseq c) a)))} as fs.
  { exists (fun n =>
              f2 (existT
                    _
                    (f1 (existT _ (mkc_nat n) (nat_in_nat lib n)))
                    (fst (fc (existT _ (mkc_nat n) (nat_in_nat lib n)))))).
    introv mem.
    dands.

    - apply member_tnat_iff in mem; exrepnd.
      allrw @computes_to_valc_iff_reduces_toc; repnd.
      eapply member_respects_reduces_toc;[apply reduces_toc_eapply_ntseqc2ntseq;exact mem1|].

      eapply member_respects_reduces_toc;
        [apply reduces_toc_ntseqc2ntseq_step|].

      simpl.
      apply member_nout_iff.
      eexists; spcast; apply cequivc_refl.

    - apply member_tnat_iff in mem; exrepnd.
      pose proof (nat_in_nat lib k) as mk.

      eapply inhabited_type_cequivc;
        [apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
          |apply implies_cequivc_eapply;
            [apply cequivc_refl
            |apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
            ]
          ]
        |].

      eapply inhabited_type_cequivc;
        [apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_sym;
            apply reduces_toc_implies_cequivc;
            apply reduces_toc_ntseqc2ntseq_step
          ]
        |].
      simpl.
      remember (fc exI(mkc_nat k, nat_in_nat lib k)) as fck.
      exrepnd.
      allsimpl.

      pose proof (fcn exI(f1 exI(mkc_nat k, nat_in_nat lib k), fck0)) as xx.
      simpl in xx; spcast.
      eapply inhabited_type_cequivc;
        [apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |eauto]
        |].
      auto.
  }
  clear f1 fc f2 fcn.
  exrepnd.

  (* then "convert" the Coq function into a Nuprl function *)

  apply inhabited_product.

  dands; eauto 3 with slow.

  { introv eqf.
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    apply tequality_function.
    dands; eauto 3 with slow.
    { apply tnat_type. }

    introv eqn.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_squash.
    apply type_respects_cequivc_left.

    { apply implies_cequivc_apply2; auto.
      { apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
      { eapply equality_nat2nout_apply in eqf;[|exact eqn].
        apply cequiv_stable.
        apply equality_in_nout in eqf; exrepnd; spcast.
        eapply cequivc_trans; eauto.
        apply cequivc_sym; auto. }
    }

    { apply impp; eauto 3 with slow.
      { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
      { eapply equality_nat2nout_apply in eqf;[|exact eqn].
        apply equality_sym in eqf; apply equality_refl in eqf; auto. }
    }
  }

  { exists (ntseqc2ntseq c).
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkc_var_substc.

    dands.

    { apply member_ntseqc2ntseq_nat2nout. }

    { apply inhabited_function; dands; eauto 3 with slow.

      - introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        apply tequality_mkc_squash.
        apply type_respects_cequivc_left.

        { apply implies_cequivc_apply2; auto.
          { apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
          { apply implies_cequivc_apply; auto.
            apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
        }

        { apply impp; eauto 3 with slow.
          { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
          { pose proof (member_ntseqc2ntseq_nat2nout lib c) as eqf.
            eapply equality_nat2nout_apply in eqf;[|exact eqn].
            apply equality_sym in eqf; apply equality_refl in eqf; auto. }
        }

      - exists (@mkc_lam o nvarx (mkcv_axiom nvarx)).
        introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        applydup @equality_int_nat_implies_cequivc in eqn.
        apply equality_refl in eqn.
        eapply equality_respects_cequivc_right;
          [apply implies_cequivc_apply;
            [apply cequivc_refl
            |exact eqn0]
          |].
        rw @member_eq.

        eapply member_respects_cequivc;
          [apply cequivc_sym;
            apply cequivc_beta
          |].
        rw @substc_mkcv_axiom.

        apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow).

        pose proof (fs0 a eqn) as q; repnd.

        eapply inhabited_type_cequivc;[|exact q].
        apply implies_cequivc_apply2; auto.
        apply cequivc_sym.
        apply reduces_toc_implies_cequivc.
        destruct_cterms.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl; auto.
    }
  }
Qed.


Definition rule_AC0NUB {o}
           (P e : @NTerm o)
           (f m n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_squash (mk_exists (mk_nat2nout) f (mk_forall mk_tnat n (mk_squash (mk_apply2 P (mk_var n) (mk_apply (mk_var f) (mk_var n)))))))))
      [ mk_baresequent H (mk_concl (mk_forall mk_tnat n (mk_squash (mk_exists mk_nout m (mk_apply2 P (mk_var n) (mk_var m))))) e),
        mk_baresequent H (mk_conclax (mk_member P (mk_fun mk_tnat (mk_fun mk_nout (mk_uni i))))) ]
      [].

Lemma rule_AC0NUB_true3 {p} :
  forall lib
         (P e : NTerm)
         (f m n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true3 lib (rule_AC0NUB P e f m n H i).
Proof.
  unfold rule_AC0NUB, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H)
                         ||- (mk_conclax
                                (mk_squash
                                   (mk_exists
                                      mk_nat2nout
                                      f
                                      (mk_forall
                                         mk_tnat
                                         n
                                         (mk_squash
                                            (mk_apply2
                                               P
                                               (mk_var n)
                                               (mk_apply
                                                  (mk_var f)
                                                  (mk_var n)))))))))) as wfc.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hh; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as qq; exrepnd; clear hyp2.

  allunfold @mk_forall.
  allunfold @mk_exists.
  allunfold @mk_nat2nout.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in qq0; auto;[].
  allrw @tequality_mkc_member_sp; repnd.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  allrw @lsubstc_mk_nout.

  pose proof (axiom_of_choice_0NUB lib f n m (lsubstc P wt s1 ct1)) as ac.
  repeat (autodimp ac hyp).

  - (* from qq1 *)
    introv m1 m2.
    apply equality_in_fun in qq1; repnd.
    pose proof (qq1 a a) as h.
    autodimp h hyp.
    lsubst_tac.
    allrw @lsubstc_mkc_tnat.
    allrw @lsubstc_mk_nout.
    apply equality_in_fun in h; repnd.
    pose proof (h b b) as q.
    autodimp q hyp.
    apply equality_in_uni in q; auto.
    allrw <- @mkc_apply2_eq; auto.

  - (* from hh1 *)
    apply equality_refl in hh1.
    exists (lsubstc e wfce0 s1 pt0).

    repeat lsubstc_vars_as_mkcv.
    allrw @lsubstc_mk_nout.
    auto.

  - repeat lsubstc_vars_as_mkcv.
    allrw @lsubstc_mk_nout.

    dands;
      [|apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow);
        allunfold @mkc_exists; allunfold @mkcv_forall;
        eapply inhabited_type_respects_alphaeqc;[|exact ac];
        apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        fold (@mk_nat2nout p);
        rewrite lsubstc_mk_nat2nout;
        eauto 3 with slow];[].

    apply tequality_mkc_squash.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        fold (@mk_nat2nout p);
        rewrite lsubstc_mk_nat2nout;
        eauto 3 with slow
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        fold (@mk_nat2nout p);
        rewrite lsubstc_mk_nat2nout;
        eauto 3 with slow
      |].
    apply tequality_product; dands.
    { apply type_nat2nout. }

    introv eqf.
    repeat (rw @substc_mkcv_function; auto;[]).
    allrw @mkcv_tnat_substc.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_apply.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto;[]).
    repeat (rw @substc2_mk_cv_app_l; auto;[]).
    allrw @mkc_var_substc.

    apply tequality_function; dands.
    { apply tnat_type. }

    introv eqn.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @mkcv_apply_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_squash.
    apply equality_in_fun in qq0; repnd.
    applydup qq0 in eqn.
    lsubst_tac.
    apply equality_in_fun in eqn0; repnd.
    pose proof (eqn0 (mkc_apply a a0) (mkc_apply a' a'0)) as q.
    allrw @lsubstc_mkc_tnat.
    allrw @lsubstc_mk_nout.
    autodimp q hyp.
    { apply equality_nat2nout_apply; auto. }
    allrw <- @mkc_apply2_eq.
    apply equality_in_uni in q; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
