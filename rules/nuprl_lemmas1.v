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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import sequents_tacs.
Require Import rules_isect.
Require Import rules_squiggle.
Require Import rules_struct.



(* ============ SOME LEMMAS ============ *)

(* prove: top in Type(0) *)
Lemma top_in_type0 {o} :
  let goal := @mk_member o mk_top (mk_uni 0) in
    {wc : wf_csequent (mk_baresequent [] (mk_conclax goal))
     & sequent_true emlib (mk_wcseq (mk_baresequent [] (mk_conclax goal)) wc)}.
Proof.
  simpl.
  eexists.

  assert (subst mk_false nvarx (mk_var nvary) = @mk_false o)
    as eq1
    by (try (unfold subst; rw lsubstn_lsubst;
             try (complete (simpl; rw disjoint_singleton_r; simpl; sp; inversion e)));
        apply subst_mk_false;
        simpl; sp; inversion e).

  generalize (@rule_isect_equality_true_ex o emlib nvary 0); intro rule_ie.
  unfold rule_true_if in rule_ie; simpl in rule_ie.
  apply rule_ie; simpl; sp; subst; clear rule_ie;
  try (complete inversion e);
  try (complete wfseq).

  generalize (@rule_approx_intensional_equality_simple_true_ex o emlib 0); intro rule_sie.
  unfold rule_true_if in rule_sie; simpl in rule_sie.
  apply rule_sie; simpl; sp; subst; clear rule_sie;
  try (complete inversion e);
  try (complete wfseq).

  revert c.
  unfold rule_isect_equality_hyp2; simpl.
  assert ([mk_hyp nvary mk_false] = [] ++ [mk_hyp nvary (@mk_false o)])
    as eq2 by (simpl; sp).
  rw eq1; rw eq2.
  intro.

  generalize (@rule_thin_hyps_true_ex o); intro rule_th.
  unfold rule_true_if in rule_th; simpl in rule_th.
  apply rule_th; simpl; sp; subst; clear rule_th;
  try (complete inversion e);
  try (complete wfseq).

  generalize (@rule_approx_intensional_equality_simple_true_ex o emlib 0); intro rule_sie.
  unfold rule_true_if in rule_sie; simpl in rule_sie.
  apply rule_sie; simpl; sp; subst; clear rule_sie;
  try (complete inversion e);
  try (complete wfseq).

  Grab Existential Variables.
  wfseq.
Qed.


Definition nprove {o} goal :=
  {t : @NTerm o
   & {wc : wf_csequent (mk_baresequent [] (mk_concl goal t))
      & sequent_true emlib (mk_wcseq (mk_baresequent [] (mk_concl goal t)) wc)}}.


(* Same thing as top_in_hyp0 but here we quantify the extract *)
Lemma top_in_type {o} :
  @nprove o (mk_member mk_top (mk_uni 0)).
Proof.
  eexists.
  eexists.

  assert (subst mk_false nvarx (mk_var nvary) = @mk_false o)
    as eq1
    by (try (unfold subst; rw lsubstn_lsubst;
             try (complete (simpl; rw disjoint_singleton_r; simpl; sp; inversion e)));
        apply subst_mk_false;
        simpl; sp; inversion e).

  generalize (@rule_isect_equality_true_ex o emlib nvary 0); intro rule_ie.
  unfold rule_true_if in rule_ie; simpl in rule_ie.
  apply rule_ie; simpl; sp; subst; clear rule_ie;
  try (complete inversion e);
  try (complete wfseq).

  generalize (@rule_approx_intensional_equality_simple_true_ex o emlib 0); intro rule_sie.
  unfold rule_true_if in rule_sie; simpl in rule_sie.
  apply rule_sie; simpl; sp; subst; clear rule_sie;
  try (complete inversion e);
  try (complete wfseq).

  revert c.
  unfold rule_isect_equality_hyp2; simpl.
  assert ([mk_hyp nvary mk_false] = [] ++ [mk_hyp nvary (@mk_false o)])
    as eq2 by (simpl; sp).
  rw eq1; rw eq2.
  intro.

  generalize (@rule_thin_hyps_true_ex o); intro rule_th.
  unfold rule_true_if in rule_th; simpl in rule_th.
  apply rule_th; simpl; sp; subst; clear rule_th;
  try (complete inversion e);
  try (complete wfseq).

  generalize (@rule_approx_intensional_equality_simple_true_ex o emlib 0); intro rule_sie.
  unfold rule_true_if in rule_sie; simpl in rule_sie.
  apply rule_sie; simpl; sp; subst; clear rule_sie;
  try (complete inversion e);
  try (complete wfseq).

  Grab Existential Variables.
  wfseq.
Defined.


(* prove: [uall x : Top], x ~ x. *)
Lemma cequiv_refl_top {o} :
  nprove (mk_uall mk_top nvarx (mk_cequiv (mk_var nvarx) (@mk_var o nvarx))).
Proof.
  simpl.
  eexists.
  eexists.

  generalize (@rule_isect_member_formation_true_ex o emlib 0 nvary mk_axiom); intro rule_imf.

  unfold rule_true_if in rule_imf; simpl in rule_imf.
  apply rule_imf; simpl; sp; subst; clear rule_imf;
  try (complete wfseq).

  Focus 3.

  revert c.
  unfold rule_isect_member_formation_hyp1.
  unfold subst, lsubst; simpl.
  rw @fold_nobnd; rw @fold_cequiv; sp.

  generalize @rule_cequiv_refl_true_ex; intro rule_sqeqrefl.
  unfold rule_true_if in rule_sqeqrefl; simpl in rule_sqeqrefl.
  apply @rule_sqeqrefl; simpl; sp; subst; clear rule_sqeqrefl;
  try (complete wfseq).

  Focus 3.

  revert c.
  unfold rule_isect_member_formation_hyp2.
  rewrite fold_member; sp.

  remember (@top_in_type o); allsimpl.
  remember (projT1 n).
  duplicate Heqn0 as eq.
  rw Heqn in eq.
  rw Heqn0 in eq.
  simpl in eq.
  clear Heqn0 Heqn.
  unfold nprove in n; exrepnd; allsimpl; subst.
  apply sequent_true_change_wf with (w2 := c) in n2; auto.


  (* now we prove the wf subgoals *)
  wfseq.
  wfseq.

  Grab Existential Variables.
  wfseq.
Qed.
