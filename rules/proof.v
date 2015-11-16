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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export rules_isect.
Require Export rules_squiggle.
Require Export rules_false.
Require Export rules_struct.


Inductive valid_rule {o} : @rule o -> Type :=
| valid_rule_isect_equality :
    forall a1 a2 b1 b2 x1 x2 y i H,
      !LIn y (vars_hyps H)
      -> valid_rule (rule_isect_equality a1 a2 b1 b2 x1 x2 y i H).

Inductive gen_proof {o} (G : @baresequent o) : Type :=
| gen_proof_cons :
    forall hyps args,
      valid_rule (mk_rule G hyps args)
      -> (forall h, LIn h hyps -> gen_proof h)
      -> gen_proof G.

(* [pwf_sequent] says that the hypotheses and conclusion are well-formed and
   the type is closed w.r.t. the hypotheses.
 *)
Lemma valid_gen_proof {o} :
  forall lib (seq : @baresequent o) (wf : pwf_sequent seq),
    gen_proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p as [? ? ? vr imp ih].
  inversion vr as [a1 a2 b1 b2 x1 x2 y i hs niy]; subst; allsimpl; clear vr.

  - apply (rule_isect_equality_true2 lib y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.
Qed.

Inductive proof {o} : @baresequent o -> Type :=
| proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      !LIn y (vars_hyps H)
      -> proof (rule_isect_equality_hyp1 a1 a2 i H)
      -> proof (rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> proof (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| proof_approx_refl :
    forall a H,
      proof (rule_approx_refl_concl a H)
| proof_cequiv_approx :
    forall a b H,
      proof (rule_cequiv_approx_hyp1 a b H)
      -> proof (rule_cequiv_approx_hyp2 a b H)
      -> proof (rule_cequiv_approx_concl a b H)
| proof_bottom_diverges :
    forall x H J,
      proof (rule_bottom_diverges_concl x H J)
| proof_cut :
    forall B C t u x H,
      wf_term B
      -> wf_term u (* !!Should get rid of that one *)
      -> covered B (vars_hyps H)
      -> !LIn x (vars_hyps H)
      -> proof (rule_cut_hyp1 H B u)
      -> proof (rule_cut_hyp2 H x B C t)
      -> proof (rule_cut_concl H C t x u).

Lemma valid_proof {o} :
  forall lib (seq : @baresequent o) (wf : pwf_sequent seq),
    proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p
    as [ a1 a2 b1 b2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | a hs
       | a b hs p1 ih1 p2 ih2
       | x hs js
       | B C t u x hs wB wu covB nixH p1 ih1 p2 ih2
       ];
    allsimpl.

  - apply (rule_isect_equality_true2 lib y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

  - apply (rule_approx_refl_true2 lib hs a); simpl; tcsp.

  - apply (rule_cequiv_approx_true2 lib hs a b); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx_wf a b hs); simpl; tcsp.

  - apply (rule_bottom_diverges_true2 lib x hs js); simpl; tcsp.

  - apply (rule_cut_true2 lib hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf hs B C t u x); simpl; tcsp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)
