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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export choice_sequence_ind.
Require Export per_props_cequiv2.


Definition nwf_pred {o} (n s : NVar) :=
  @mk_lam
    o
    n
    (mk_lam
       s
       (mk_int_eq
          (mk_var n)
          mk_zero
          (mk_cequiv (mk_apply (mk_var s) mk_zero) mk_zero)
          (mk_int_eq
             (mk_apply (mk_var s) mk_zero)
             mk_zero
             mk_true
             mk_axiom))).

Definition lam1 {o} : @NTerm o := mk_lam nvarx mk_one.

Hint Rewrite @lsubstc_mk_zero : slow.
Hint Rewrite @substc_mkcv_zero : slow.
Hint Rewrite @mkcv_cequiv_substc : slow.
Hint Rewrite @mkcv_apply_substc : slow.

Lemma substc2_cequiv {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_cequiv [v,x] a b)
    = mkcv_cequiv [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_cequiv : slow.

Lemma implies_approx_cequiv {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_cequiv f a) (mk_cequiv g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_cequiv {p} :
  forall lib f g a b,
    cequivc lib f g
    -> @cequivc p lib a b
    -> cequivc lib (mkc_cequiv f a) (mkc_cequiv g b).
Proof.
  unfold cequivc. introv H1c H2c.
  destruct_cterms. allsimpl. apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_cequiv; auto.
Qed.

Lemma base_nwf_pred {o} :
  forall lib H n s,
    s <> n
    -> wf_hypotheses H
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_base H (nwf_pred n s) lam1 mk_axiom).
Proof.
  introv d1 wfH.

  assert (wf_csequent (choice_sequence_ind_base H (nwf_pred n s) lam1 mk_axiom)) as wfc.
  {
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    dands; tcsp;
    try (complete (rw @vswf_hypotheses_nil_eq; auto)).
    introv i; allrw in_remove_nvars; allsimpl; allrw not_over_or.
    repnd; repndors; tcsp.
  }

  exists wfc.
  vr_seq_true.
  unfold nwf_pred, lam1.
  lsubst_tac.

  dands.

  - eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta2|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta2|].
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite mkcv_lam_substc; auto;[]).
    eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta|].
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    rewrite mkc_zero_eq.
    eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
    boolvar; try omega; GC;[].

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;
        apply implies_cequivc_cequiv;
        [apply cequivc_beta|apply cequivc_refl]
      |].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;
        apply implies_cequivc_cequiv;
        [apply cequivc_beta|apply cequivc_refl]
      |].
    autorewrite with slow.

    SearchAbout type mkc_cequiv.
    apply tequality_mkc_cequiv; split; intro h

    SearchAbout tequality mkc_cequiv.

    SearchAbout substc mkc_var.
    SearchAbout lsubstc mk_zero.
    repeat lsubstc_vars_as_mkcv.

    SearchAbout mkc_apply mkc_lam.

Qed.

Lemma not_well_formed {o} :
  forall lib,
    not (tequality
           lib
           ()
        )


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
