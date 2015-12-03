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


Require Export sequents2.
Require Export sequents_tacs.
Require Export Classical_Prop.
Require Export per_props_union.
Require Export per_props_equality.
Require Export per_props_squash.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(* begin hide *)


(* end hide*)

(**

I think Abhishek proved that to be inconsistent with Nuprl, but let's see
how far we can go just for the hell of it.

<<
   H |- squash(forall x : T. P x) ext Ax

     By SquashAll

     H |- isect x : T. squash(P x) ext Ax
>>

 *)

Definition rule_squash_all {o}
           (P T : NTerm)
           (x : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash (mk_function T x P))))
    [ mk_baresequent H (mk_conclax (mk_isect T x (mk_squash P)))
    ]
    [].

Lemma rule_squash_all_true3 {o} :
  forall lib (P T : NTerm),
  forall x : NVar,
  forall H : @barehypotheses o,
    rule_true3 lib (rule_squash_all P T x H).
Proof.
  unfold rule_squash_all, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [ws hyp1].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_squash (mk_function T x P))))) as wfs.
  { prove_seq. }
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_concl in wfs; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  apply tequality_isect in hyp0.
  apply equality_in_isect in hyp1.
  repnd.

  apply implies_tequality_equality_mkc_squash.

  - apply tequality_function; dands; auto;[].
    introv equ.
    applydup hyp0 in equ.
    repeat (substc_lsubstc_vars3;[]).
    lsubst_tac.
    rw @tequality_mkc_squash in equ0; auto.

  - apply inhabited_function.
    dands; auto.

    + introv equ.
      applydup hyp3 in equ.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      rw @tequality_mkc_squash in equ0; auto.

    + assert (forall a, cover_vars P ((x, a) :: s1)) as cov.
      { introv.
        apply cover_vars_eq.
        unfold cover_vars_upto in c6; allsimpl.
        allrw @dom_csub_csub_filter.
        rw subvars_prop in c6; rw subvars_prop.
        introv i; apply c6 in i; allsimpl; repndors; subst; tcsp.
        allrw in_remove_nvars; tcsp. }

      assert (forall a a' : CTerm,
                equality lib a a' (lsubstc T w1 s1 c1)
                -> inhabited_type lib (lsubstc P w4 ((x,a) :: s1) (cov a))) as F.
      { introv equ.
        apply hyp1 in equ.
        repeat (substc_lsubstc_vars3;[]).
        remember (cov a) as ca; clear Heqca.
        lsubst_tac.
        apply equality_in_mkc_squash in equ; repnd; auto. }
      clear hyp1.

      unfold inhabited_type in F.
      pose proof (FunctionalChoice_on
                    {a : CTerm & {a' : CTerm & equality lib a a' (lsubstc T w1 s1 c1)}}
                    (@CTerm o)
                    (fun a t => member lib t (lsubstc P w4 ((x, (projT1 a)) :: s1) (cov (projT1 a)))))
        as fc; simpl in fc.
      autodimp fc hyp.
      { introv; exrepnd; allsimpl.
        pose proof (F a0 a' a2) as k; auto. }
      clear F.
      exrepnd.

      (* even if we could get a function from [CTerm] to [CTerm] from [f]
         (which we can't---right now we can at best get such functions when they're
          from nats to CTerms without atoms),
         we still don't get a function that functional over [(lsubstc T w1 s1 c1)] *)

Abort.

(* begin hide *)

(* end hide *)



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
