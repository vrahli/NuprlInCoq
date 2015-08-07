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


Require Export computation_pair.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_top.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)


(**

  The following rule states that if [mk_spread p x y b] computes to
  a value then [p] must compute to a pair:

<<
  H |- p in Top x Top

    By haltSpread

    H |- halts(mk_spread p x y b)
>>

*)

Definition rule_halt_spread {o}
           (H : barehypotheses)
           (x y : NVar)
           (p b  : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member p (mk_prod mk_top mk_top))))
    [ mk_baresequent H (mk_conclax (mk_halts (mk_spread p x y b)))
    ]
    [].

Lemma rule_halt_spread_true {o} :
  forall lib (H  : barehypotheses)
         (x y : NVar)
         (p b : @NTerm o),
    rule_true lib (rule_halt_spread H x y p b).
Proof.
  intros.
  unfold rule_halt_spread, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_member_iff.
  apply @teq_and_member_if_member with (H := H); auto.

  - lsubst_tac.
    apply tequality_mkc_prod.
    rw @fold_type; dands; sp; apply type_mkc_top.

  - clear dependent s1.
    clear dependent s2.
    introv hf sim.
    vr_seq_true in hyp1.
    generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
    lsubst_tac.
    allrw @member_eq.
    allrw <- @member_halts_iff.
    allrw @tequality_mkc_halts.
    applydup hyp0 in hyp1; clear hyp0.
    spcast.

    apply hasvaluec_mkc_spread in hyp1.
    apply hasvaluec_mkc_spread in hyp2.
    exrepnd.

    rw @equality_in_prod; dands.

    + apply type_mkc_top.

    + intro k; apply type_mkc_top.

    + exists a0 a b1 b0; dands; spcast; auto; apply equality_mkc_top.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
