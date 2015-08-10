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


Require Export sequents_tacs.
Require Export sequents_equality.
Require Export per_props_equality.
Require Export per_props4.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)

(* !!MOVE *)
Lemma inhabited_approx {o} :
  forall lib (t1 t2 : @CTerm o),
    inhabited_type lib (mkc_approx t1 t2)
    <=> (t1) ~<~( lib)(t2).
Proof.
  introv.
  split; intro h.
  - unfold inhabited_type in h; exrepnd.
    rw <- @equality_in_approx in h0; sp.
  - unfold inhabited_type.
    exists (@mkc_axiom o).
    apply equality_in_approx; dands; spcast; auto;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.


(*
   H |- a <= b = c <= d

     By approxExtensionalEquality

     H |- a <= b <=> b <= a
 *)
Definition rule_approx_extensional_equality {o}
           (H : barehypotheses)
           (i : nat)
           (a b c d e : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_approx a b) (mk_approx c d) (mk_uni i))))
    [ mk_baresequent H (mk_concl (mk_iff (mk_approx a b) (mk_approx c d)) e)
    ]
    [].

Lemma rule_approx_extensional_equality_true {o} :
  forall lib (H : barehypotheses) (i : nat)
         (a b c d e : @NTerm o),
    rule_true lib (rule_approx_extensional_equality H i a b c d e).
Proof.
  unfold rule_approx_extensional_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality (mk_approx a b) (mk_approx c b) (mk_uni i)))) as cs.
  clear hyp1.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                lib
                (mk_uni i)
                (mk_approx a b)
                (mk_approx c d)
                s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0) as h.
  lsubst_tac.
  apply h; auto; clear h.

  { apply tequality_mkc_uni. }

  { clear dependent s1.
    clear dependent s2.
    introv hf sim.

    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1.
    exrepnd.
    lsubst_tac.
    apply equality_in_iff in hyp1; exrepnd; spcast.
    pose proof (hyp6 mkc_axiom mkc_axiom) as h1.
    pose proof (hyp1 mkc_axiom mkc_axiom) as h2.
    clear hyp1 hyp4 hyp5 hyp6.
    allrw <- @equality_in_approx.
    apply tequality_mkc_iff in hyp0; repnd.
    allrw @tequality_mkc_approx.
    allrw @inhabited_approx.

    clear hyp2 hyp3.

    apply mkc_approx_equality_in_uni.
    split; intro h.

    - autodimp h1 hyp; repnd; dands; auto;
      try (spcast; apply computes_to_valc_refl; eauto 3 with slow).
      autodimp hyp4 hyp.
      apply hyp4; auto.

    - autodimp hyp0 hyp.

      { exists (@mkc_id o).
        apply equality_in_fun; dands.

        - apply tequality_mkc_approx; sp.

        - introv inh.
          apply tequality_mkc_approx; sp.

        - introv ea.
          allrw <- @equality_in_approx; repnd.
          dands; tcsp.

          + autodimp h1 hyp; repnd; dands; auto;
            try (spcast; apply computes_to_valc_refl; eauto 3 with slow).

          + spcast.
            allrw @computes_to_valc_iff_reduces_toc; repnd; dands; auto.
            eapply reduces_toc_trans;[apply reduces_toc_apply_id|]; auto.

          + spcast.
            allrw @computes_to_valc_iff_reduces_toc; repnd; dands; auto.
            eapply reduces_toc_trans;[apply reduces_toc_apply_id|]; auto.
      }

      apply hyp0 in h; clear hyp0.
      autodimp h2 hyp; repnd; dands; auto; spcast;
      apply computes_to_valc_refl; eauto 3 with slow.
  }
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
