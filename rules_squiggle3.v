(*

  Copyright 2014 Cornell University

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

Require Export per_props_equality.
Require Export per_props_equality_more.
Require Export per_can.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* [28] ============ CONVERGENCE ============ *)

(*
   H |- a <= b

     By convergence lvl(i) x

     H, x : halts(a) |- a <= b
     H, x : is_exc(a) |- a <= b
     H |- halts(a) in Prop(i)
     H |- is_exc(a) in Prop(i)
 *)
Definition rule_convergence {o}
           (H   : barehypotheses)
           (i   : nat)
           (a b : @NTerm o)
           (x   : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx a b)))
    [ mk_baresequent (snoc H (mk_hyp x (mk_halts a))) (mk_conclax (mk_approx a b)),
      mk_baresequent (snoc H (mk_hyp x (mk_isexc a))) (mk_conclax (mk_approx a b)),
      mk_baresequent H (mk_conclax (mk_member (mk_halts a) (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_member (mk_isexc a) (mk_uni i)))
    ]
    [].

Lemma rule_convergence_true {o} :
  forall lib
         (H : barehypotheses)
         (i : nat)
         (a b : @NTerm o)
         (x : NVar),
    rule_true lib (rule_convergence H i a b x).
Proof.
  unfold rule_convergence, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_approx a b))) as cs.
  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars a)
          # !LIn x (free_vars b)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  sp.

  destruct vhyps as [ nixa nixb ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw @member_eq.
  rw <- @member_approx_iff.
  rw @tequality_mkc_approx.

  (* Now we start proving our second subgoal: an approximation *)
  assert (capproxc lib (lsubstc a w1 s1 c1) (lsubstc b w2 s1 c2)) as apx1.
  (* for that we can assume that the term on the left computes to a value *)
  { spcast.
    (* we're going to use hyp1, but to prove similarity, we need `hv' *)
    apply approxc_assume_hasvalue; intro hv.
    apply hasvalue_likec_eq in hv; repndors;[|].

    { (* to prove that we will have to use our first subgoal *)
      vr_seq_true in hyp1.
      generalize (hyp1 (snoc s1 (x, mkc_axiom))
                       (snoc s2 (x, mkc_axiom)));
        clear hyp1; intro hyp1.
      dest_imp hyp1 hyp.
      { apply hyps_functionality_snoc2; simpl; try (complete sp).
        introv e s.
        lsubst_tac.
        rw @tequality_mkc_halts.
        apply equality_refl in e.
        rw <- @member_halts_iff in e.
        split; intro chv; try (complete sp).

        vr_seq_true in hyp3.
        generalize (hyp3 s1 s' eqh s); clear hyp3; intro hyp3; exrepnd.
        lsubst_tac.
        allrw @member_eq.
        allrw <- @member_member_iff.
        allrw @tequality_in_uni_iff_tequality.
        allapply @cequorsq_mkc_halts_implies.
        allrw <-; sp.
      }

      assert (cover_vars (mk_halts a) s1) as cvh1 by (rw @cover_vars_halts; sp).

      dest_imp hyp1 hyp.

      { allrw @similarity_snoc; simpl.
        exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh1.
        rw @member_eq; lsubst_tac; rw <- @member_halts_iff.
        sp; spcast; sp.
      }

      exrepnd; lsubst_tac.
      allrw @member_eq.
      allrw @tequality_mkc_approx.
      allrw <- @member_approx_iff.
      apply approx_stable in hyp1; auto.
    }

    { vr_seq_true in hyp2.
      generalize (hyp2 (snoc s1 (x, mkc_axiom))
                       (snoc s2 (x, mkc_axiom)));
        clear hyp2; intro hyp2.
      dest_imp hyp2 hyp.
      { apply hyps_functionality_snoc2; simpl; try (complete sp).
        introv e s.
        lsubst_tac.
        apply tequality_mkc_isexc.
        apply equality_refl in e.
        rw <- @member_isexc_iff in e; GC.
        split; intro chv; tcsp;[].

        vr_seq_true in hyp4.
        generalize (hyp4 s1 s' eqh s); clear hyp3; intro hyp3; exrepnd.
        clear hyp2.
        lsubst_tac.
        allrw @tequality_in_uni_iff_tequality.
        apply cequorsq_mkc_isexc in hyp0.
        apply hyp0; auto.
      }

      assert (cover_vars (mk_isexc a) s1) as cvh1 by (rw @cover_vars_isexc; sp).

      dest_imp hyp2 hyp.

      { allrw @similarity_snoc; simpl.
        exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) (wf_isexc a w1) cvh1.
        rw @member_eq; lsubst_tac; rw <- @member_isexc_iff.
        sp; spcast; sp.
      }

      exrepnd; lsubst_tac.
      allrw @member_eq.
      allrw @tequality_mkc_approx.
      allrw <- @member_approx_iff.
      apply approx_stable in hyp2; auto.
    }
  }

  { (* The prove the same thing but for s2 instead of s1 *)
    assert (capproxc lib (lsubstc a w1 s2 c0) (lsubstc b w2 s2 c3)) as apx2.
    (* for that we can assume that the term on the left computes to a value *)
    { spcast.
      (* we're going to use hyp1, but to prove similarity, we need `hv' *)
      apply approxc_assume_hasvalue; intro hv.
      apply hasvalue_likec_eq in hv; repndors;[|].

      { (* to prove that will have to use our first subgoal *)
        vr_seq_true in hyp1.
        generalize (hyp1 (snoc s1 (x, mkc_axiom))
                         (snoc s2 (x, mkc_axiom)));
          clear hyp1; intro hyp1.
        dest_imp hyp1 hyp.
        { apply hyps_functionality_snoc2; simpl; try (complete sp).
          introv e s.
          lsubst_tac.
          rw @tequality_mkc_halts.
          apply equality_refl in e.
          rw <- @member_halts_iff in e.
          split; intro chv; try (complete sp).

          vr_seq_true in hyp3.
          generalize (hyp3 s1 s' eqh s); clear hyp3; intro hyp3; exrepnd.
          lsubst_tac.
          allrw @member_eq.
          allrw <- @member_member_iff.
          allrw @tequality_in_uni_iff_tequality.
          allrw @cequorsq_mkc_halts.
          spcast; apply hyp0; auto.
        }

        assert (cover_vars (mk_halts a) s1) as cvh1 by (rw @cover_vars_halts; sp).
        assert (cover_vars (mk_halts a) s2) as cvh2 by (rw @cover_vars_halts; sp).

        dest_imp hyp1 hyp.
        { apply similarity_sym.

          assert (eq_hyps lib s2 s1 H) as eqhs by (apply eq_hyps_sym; apply eqh in sim; sp).
          { rw @eq_hyps_snoc; simpl.
            exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh2 cvh1.
            lsubst_tac; rw @tequality_mkc_halts; sp.

            vr_seq_true in hyp3.
            generalize (hyp3 s1 s2 eqh sim); clear hyp3; intro hyp3; exrepnd.
            lsubst_tac.
            allrw @member_eq.
            allrw <- @member_member_iff.
            allrw @tequality_in_uni_iff_tequality.
            allrw @cequorsq_mkc_halts.
            split; intro q; spcast; apply hyp0; auto.
          }

          allrw @similarity_snoc; simpl.
          exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh2.
          rw @member_eq; lsubst_tac; rw <- @member_halts_iff.
          sp; spcast; auto.
          apply similarity_sym; sp.
        }

        exrepnd; lsubst_tac.
        allrw @member_eq.
        allrw @tequality_mkc_approx.
        allrw <- @member_approx_iff.
        apply approx_stable; apply hyp0; auto.
      }

      { vr_seq_true in hyp2.
        generalize (hyp2 (snoc s1 (x, mkc_axiom))
                         (snoc s2 (x, mkc_axiom)));
          clear hyp2; intro hyp2.
        dest_imp hyp2 hyp.
        { apply hyps_functionality_snoc2; simpl; try (complete sp).
          introv e s.
          lsubst_tac.
          rw @tequality_mkc_isexc.
          apply equality_refl in e.
          rw <- @member_isexc_iff in e.
          split; intro chv; try (complete sp).

          vr_seq_true in hyp4.
          generalize (hyp4 s1 s' eqh s); clear hyp3; intro hyp3; exrepnd.
          lsubst_tac.
          allrw @member_eq.
          allrw <- @member_member_iff.
          allrw @tequality_in_uni_iff_tequality.
          allrw @cequorsq_mkc_isexc.
          spcast; apply hyp0; auto.
        }

        assert (cover_vars (mk_isexc a) s1) as cvh1 by (rw @cover_vars_isexc; sp).
        assert (cover_vars (mk_isexc a) s2) as cvh2 by (rw @cover_vars_isexc; sp).

        dest_imp hyp2 hyp.
        { apply similarity_sym.

          assert (eq_hyps lib s2 s1 H) as eqhs by (apply eq_hyps_sym; apply eqh in sim; sp).
          { rw @eq_hyps_snoc; simpl.
            exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_isexc a w1) cvh2 cvh1.
            lsubst_tac; rw @tequality_mkc_isexc; sp.

            vr_seq_true in hyp4.
            generalize (hyp4 s1 s2 eqh sim); clear hyp4; intro hyp4; exrepnd.
            lsubst_tac.
            allrw @member_eq.
            allrw <- @member_member_iff.
            allrw @tequality_in_uni_iff_tequality.
            allrw @cequorsq_mkc_isexc.
            split; intro q; spcast; apply hyp0; auto.
          }

          allrw @similarity_snoc; simpl.
          exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_isexc a w1) cvh2.
          rw @member_eq; lsubst_tac; rw <- @member_isexc_iff.
          sp; spcast; auto.
          apply similarity_sym; sp.
        }

        exrepnd; lsubst_tac.
        allrw @member_eq.
        allrw @tequality_mkc_approx.
        allrw <- @member_approx_iff.
        apply approx_stable; apply hyp0; auto.
      }
    }

    (* We finish the proof *)
    sp.
  }
Qed.


(*
   H |- a <= b

     By convergence2 lvl(i) x

     H, x : halts_like(a) |- a <= b
     H |- halts_like(a) in Prop(i)
 *)
Definition rule_convergence2 {o}
           (H   : barehypotheses)
           (i   : nat)
           (a b : @NTerm o)
           (x   : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx a b)))
    [ mk_baresequent (snoc H (mk_hyp x (mk_halts_like a))) (mk_conclax (mk_approx a b)),
      mk_baresequent H (mk_conclax (mk_member (mk_halts_like a) (mk_uni i)))
    ]
    [].

Lemma rule_convergence2_true {o} :
  forall lib
         (H : barehypotheses)
         (i : nat)
         (a b : @NTerm o)
         (x : NVar),
    rule_true lib (rule_convergence2 H i a b x).
Proof.
  unfold rule_convergence2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_approx a b))) as cs.
  clear hyp1 hyp2.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars a)
          # !LIn x (free_vars b)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp.

  destruct vhyps as [ nixa nixb ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw @member_eq.
  rw <- @member_approx_iff.
  rw @tequality_mkc_approx.

  (* Now we start proving our second subgoal: an approximation *)
  assert (capproxc lib (lsubstc a w1 s1 c1) (lsubstc b w2 s1 c2)) as apx1.
  (* for that we can assume that the term on the left computes to a value *)
  { spcast.
    (* we're going to use hyp1, but to prove similarity, we need `hv' *)
    apply approxc_assume_hasvalue; intro hv.

    (* to prove that we will have to use our first subgoal *)
    vr_seq_true in hyp1.
    generalize (hyp1 (snoc s1 (x, mkc_axiom))
                     (snoc s2 (x, mkc_axiom)));
      clear hyp1; intro hyp1.
    dest_imp hyp1 hyp.
    { apply hyps_functionality_snoc2; simpl; try (complete sp).
      introv e s.
      lsubst_tac.
      rw @tequality_mkc_halts_like.
      apply equality_refl in e.
      rw @member_halts_like_iff in e.
      split; intro chv; try (complete sp).

      vr_seq_true in hyp2.
      generalize (hyp2 s1 s' eqh s); clear hyp2; intro hyp2; exrepnd.
      lsubst_tac.
      allrw @member_eq.
      allrw <- @member_member_iff.
      allrw @tequality_in_uni_iff_tequality.
      apply cequorsq_mkc_halts_like in hyp0.
      allrw <-; sp.
    }

    assert (cover_vars (mk_halts_like a) s1) as cvh1 by (rw @cover_vars_halts_like; sp).

    dest_imp hyp1 hyp.

    { allrw @similarity_snoc; simpl.
      exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh1.
      rw @member_eq; lsubst_tac; rw @member_halts_like_iff.
      sp; spcast; sp.
    }

    exrepnd; lsubst_tac.
    allrw @member_eq.
    allrw @tequality_mkc_approx.
    allrw <- @member_approx_iff.
    apply approx_stable in hyp1; auto.
  }

  { (* The prove the same thing but for s2 instead of s1 *)
    assert (capproxc lib (lsubstc a w1 s2 c0) (lsubstc b w2 s2 c3)) as apx2.
    (* for that we can assume that the term on the left computes to a value *)
    { spcast.
      (* we're going to use hyp1, but to prove similarity, we need `hv' *)
      apply approxc_assume_hasvalue; intro hv.

      (* to prove that will have to use our first subgoal *)
      vr_seq_true in hyp1.
      generalize (hyp1 (snoc s1 (x, mkc_axiom))
                       (snoc s2 (x, mkc_axiom)));
        clear hyp1; intro hyp1.
      dest_imp hyp1 hyp.
      { apply hyps_functionality_snoc2; simpl; try (complete sp).
        introv e s.
        lsubst_tac.
        rw @tequality_mkc_halts_like.
        apply equality_refl in e.
        rw @member_halts_like_iff in e.
        split; intro chv; try (complete sp).

        vr_seq_true in hyp2.
        generalize (hyp2 s1 s' eqh s); clear hyp2; intro hyp2; exrepnd.
        lsubst_tac.
        allrw @member_eq.
        allrw <- @member_member_iff.
        allrw @tequality_in_uni_iff_tequality.
        allrw @cequorsq_mkc_halts_like.
        spcast; apply hyp0; auto.
      }

      assert (cover_vars (mk_halts_like a) s1) as cvh1 by (rw @cover_vars_halts_like; sp).
      assert (cover_vars (mk_halts_like a) s2) as cvh2 by (rw @cover_vars_halts_like; sp).

      dest_imp hyp1 hyp.
      { apply similarity_sym.

        assert (eq_hyps lib s2 s1 H) as eqhs by (apply eq_hyps_sym; apply eqh in sim; sp).
        { rw @eq_hyps_snoc; simpl.
          exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh2 cvh1.
          lsubst_tac; rw @tequality_mkc_halts_like; sp.

          vr_seq_true in hyp2.
          generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.
          lsubst_tac.
          allrw @member_eq.
          allrw <- @member_member_iff.
          allrw @tequality_in_uni_iff_tequality.
          allrw @cequorsq_mkc_halts_like.
          split; intro q; spcast; apply hyp0; auto.
        }

        allrw @similarity_snoc; simpl.
        exists s2 s1 (@mkc_axiom o) (@mkc_axiom o) (wf_halts a w1) cvh2.
        rw @member_eq; lsubst_tac; rw @member_halts_like_iff.
        sp; spcast; auto.
        apply similarity_sym; sp.
      }

      exrepnd; lsubst_tac.
      allrw @member_eq.
      allrw @tequality_mkc_approx.
      allrw <- @member_approx_iff.
      apply approx_stable; apply hyp0; auto.
    }

    (* We finish the proof *)
    sp.
  }
Qed.


(* end hide *)



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
