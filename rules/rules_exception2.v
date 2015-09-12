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


Require Export computation_pair.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.

Lemma hasvaluec_implies_computes_to_valc {o} :
  forall lib (a : @CTerm o),
    hasvaluec lib a -> {b : CTerm & computes_to_valc lib a b}.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  unfold hasvalue in hv; exrepnd.
  applydup @computes_to_value_preserves_program in hv0; eauto 3 with slow.
  exists (mk_cterm t' hv1).
  unfold computes_to_valc; simpl; auto.
Qed.

Lemma implies_approx_atom_eq {o} :
  forall lib (a1 b1 c1 d1 a2 b2 c2 d2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib d1 d2
    -> approx lib (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv apa apb apc apd.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  applydup @approx_relates_only_progs in apc.
  applydup @approx_relates_only_progs in apd.
  repnd.
  unfold mk_atom_eq.
  repeat prove_approx; sp.
Qed.

Lemma implies_cequivc_atom_eq {o} :
  forall lib (a1 b1 c1 d1 a2 b2 c2 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> cequivc lib (mkc_atom_eq a1 b1 c1 d1) (mkc_atom_eq a2 b2 c2 d2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc ceqd.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  repnud ceqd.
  split; apply implies_approx_atom_eq; auto.
Qed.

Lemma implies_approx_try_sp {o} :
  forall lib (a1 b1 a2 b2 : @NTerm o) x c,
    isprog_vars [x] c
    -> approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib (mk_try a1 b1 x c) (mk_try a2 b2 x c).
Proof.
  introv ispv apa apb.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  repnd.
  unfold mk_try.
  repeat prove_approx; sp;
  allrw <- @isprog_vars_iff_isprogram_bt; auto.
  unfold blift.
  exists [x] c c; dands; eauto 3 with slow.
Qed.

Lemma implies_cequivc_try_sp {o} :
  forall lib (a1 b1 a2 b2 : @CTerm o) x c,
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_try a1 b1 x c) (mkc_try a2 b2 x c).
Proof.
  unfold cequivc.
  introv ceqa ceqb.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  split; apply implies_approx_try_sp; auto.
Qed.

Lemma cequivc_mkc_try_if_hasvaluec {o} :
  forall lib (t : @CTerm o) n x c,
    hasvaluec lib t
    -> cequivc lib (mkc_try t n x c) (mkc_atom_eq n n t mkc_bottom).
Proof.
  introv hv.
  apply hasvaluec_implies_computes_to_valc in hv; exrepnd.
  eapply cequivc_trans;
    [|apply implies_cequivc_atom_eq;
       [apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_sym; apply computes_to_valc_implies_cequivc; eauto
       |apply cequivc_refl]
    ].
  eapply cequivc_trans;
    [apply implies_cequivc_try_sp;
      [apply computes_to_valc_implies_cequivc; eauto
      |apply cequivc_refl]
    |].

  apply reduces_toc_implies_cequivc.
  destruct_cterms.
  unfold computes_to_valc in hv0; allsimpl.
  unfold computes_to_value in hv0; repnd.
  unfold reduces_toc; simpl.

  apply reduces_to_if_step.
  csunf; simpl.
  allrw @isvalue_iff; repnd.
  apply iscan_implies in hv2; repndors; exrepnd; subst; auto.
Qed.


(*
   H |- try(t1;n;x.t2) ~ if n=n then t1 else bottom

     By tryReduceValue

     H |- halts(t1)
 *)
Definition rule_try_reduce_value {o}
           (H : barehypotheses)
           (t1 n t2 : @NTerm o)
           (x : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv
                                     (mk_try t1 n x t2)
                                     (mk_atom_eq n n t1 mk_bottom))))
    [ mk_baresequent H (mk_conclax (mk_halts t1))
    ]
    [].

Lemma rule_try_reduce_value_true {o} :
  forall lib (H : barehypotheses)
         (t1 n t2 : @NTerm o)
         (x : NVar),
    rule_true lib (rule_try_reduce_value H t1 n t2 x).
Proof.
  unfold rule_try_reduce_value, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.

  lsubst_tac.
  rw <- @member_cequiv_iff.
  rw @tequality_mkc_cequiv.

  rw <- @member_halts_iff in hyp1.
  apply tequality_mkc_halts in hyp0.
  applydup hyp0 in hyp1; clear hyp0.

  dands.

  - split; intro ceq; spcast.

    + apply cequivc_mkc_try_if_hasvaluec; auto.

    + apply cequivc_mkc_try_if_hasvaluec; auto.

  - spcast.
    apply cequivc_mkc_try_if_hasvaluec; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)
