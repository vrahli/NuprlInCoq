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


Require Export rules_isect.
Require Export rules_squiggle.
Require Export rules_squiggle2.
Require Export rules_squiggle3.
Require Export rules_squiggle5.
Require Export rules_squiggle6.
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

Definition NVin v (vs : list NVar) := memvar v vs = false.

Definition Vin v (vs : list NVar) := memvar v vs = true.

Lemma NVin_iff :
  forall v vs, NVin v vs <=> !LIn v vs.
Proof.
  introv.
  unfold NVin.
  rw <- (@assert_memberb NVar eq_var_dec).
  rw <- not_of_assert; sp.
Qed.

Lemma Vin_iff :
  forall v vs, Vin v vs <=> LIn v vs.
Proof.
  introv.
  unfold Vin.
  rw <- (@assert_memberb NVar eq_var_dec); auto.
Qed.

Inductive Llist {A} (f : A -> Type) : list A -> Type :=
| lnil : Llist f []
| lcons : forall {h t}, (f h) -> Llist f t -> Llist f (h :: t).

Lemma in_Llist {A} :
  forall f (a : A) l,
    LIn a l -> Llist f l -> f a.
Proof.
  induction l; introv i h; allsimpl; tcsp.
  repndors; subst; auto.
  - inversion h; subst; auto.
  - apply IHl; auto.
    inversion h; subst; auto.
Qed.

Lemma Llist_implies_forall {A f} {l : list A} :
  Llist f l -> (forall v, LIn v l -> f v).
Proof.
  introv h i.
  eapply in_Llist in h;eauto.
Qed.

Inductive proof {o} : @baresequent o -> Type :=
| proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof (rule_isect_equality_hyp1 a1 a2 i H)
      -> proof (rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> proof (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| proof_approx_refl :
    forall a H,
      proof (rule_approx_refl_concl a H)
| proof_cequiv_approx :
    forall a b H,
      proof (rule_cequiv_approx_hyp a b H)
      -> proof (rule_cequiv_approx_hyp b a H)
      -> proof (rule_cequiv_approx_concl a b H)
| proof_approx_eq :
    forall a1 a2 b1 b2 i H,
      proof (rule_eq_base_hyp a1 a2 H)
      -> proof (rule_eq_base_hyp b1 b2 H)
      -> proof (rule_approx_eq_concl a1 a2 b1 b2 i H)
| proof_cequiv_eq :
    forall a1 a2 b1 b2 i H,
      proof (rule_eq_base_hyp a1 a2 H)
      -> proof (rule_eq_base_hyp b1 b2 H)
      -> proof (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
| proof_bottom_diverges :
    forall x H J,
      proof (rule_bottom_diverges_concl x H J)
| proof_cut :
    forall B C t u x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> proof (rule_cut_hyp1 H B u)
      -> proof (rule_cut_hyp2 H x B C t)
      -> proof (rule_cut_concl H C t x u)
| proof_equal_in_base :
    forall a b H,
      proof (rule_equal_in_base_hyp1 a b H)
      -> (forall v, LIn v (free_vars a) -> proof (rule_equal_in_base_hyp2 v H))
      -> proof (rule_equal_in_base_concl a b H)
| proof_hypothesis :
    forall x A G J,
      proof (rule_hypothesis_concl G J A x)
| proof_cequiv_subst_concl :
    forall C x a b t H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> proof (rule_cequiv_subst_hyp1 H x C b t)
      -> proof (rule_cequiv_subst_hyp2 H a b)
      -> proof (rule_cequiv_subst_hyp1 H x C a t)
| proof_approx_member_eq :
    forall a b H,
      proof (rule_approx_member_eq_hyp a b H)
      -> proof (rule_approx_member_eq_concl a b H).

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall lib (seq : @baresequent o) (wf : wf_bseq seq),
    proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p
    as [ (* isect_eq           *) a1 a2 b1 b2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl        *) a hs
       | (* cequiv_approx      *) a b hs p1 ih1 p2 ih2
       | (* approx_eq          *) a1 a2 b1 b2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq          *) a1 a2 b1 b2 i hs p1 ih1 p2 ih2
       | (* bottom_diverges    *) x hs js
       | (* cut                *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base      *) a b H p1 ih1 ps ihs
       | (* hypothesis         *) x A G J
       | (* cequiv_subst_concl *) C x a b t H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq   *) a b H p ih
       ];
    allsimpl;
    allrw NVin_iff.

  - apply (rule_isect_equality_true3 lib a1 a2 b1 b2 x1 x2 y i hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality_wf2 y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality_wf2 y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

  - apply (rule_approx_refl_true3 lib hs a); simpl; tcsp.

  - apply (rule_cequiv_approx_true3 lib hs a b); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx_wf2 a b hs); simpl; tcsp.

  - apply (rule_approx_eq_true3 lib a1 a2 b1 b2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_approx_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_approx_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

  - apply (rule_cequiv_eq_true3 lib a1 a2 b1 b2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_cequiv_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_cequiv_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

  - apply (rule_bottom_diverges_true3 lib x hs js); simpl; tcsp.

  - apply (rule_cut_true3 lib hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

  - apply (rule_equal_in_base_true3 lib); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base_rest in xx; rw in_map_iff in xx; exrepnd; subst.
    applydup Vin_iff in xx1.
    pose proof (ihs a0) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base_wf2 H a b) as w.
    apply w; simpl; tcsp.
    right.
    rw in_map_iff; eexists; dands; eauto.

  - apply (rule_hypothesis_true3 lib); simpl; tcsp.

  - apply (rule_cequiv_subst_concl_true3 lib H x C a b t); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply ih1.
      apply (rule_cequiv_subst_concl_wf2 H x C a b t); simpl; tcsp.

    + apply ih2.
      apply (rule_cequiv_subst_concl_wf2 H x C a b t); simpl; tcsp.

  - apply (rule_approx_member_eq_true3 lib); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq_wf2 a b H); simpl; tcsp.
Qed.

Lemma test {o} :
  @sequent_true2 o emlib (mk_baresequent [] (mk_conclax ((mk_member mk_axiom mk_unit)))).
Proof.
  apply valid_proof;
  [ exact (eq_refl, (eq_refl, eq_refl))
  | exact (proof_approx_member_eq (mk_axiom) (mk_axiom) (nil) (proof_approx_refl (mk_axiom) (nil)))
          (* This last bit was generated by JonPRL; I've got to generate the whole thing now *)
  ].
Qed.


(* Looking at how we can define a Nuprl process *)

Lemma eq_opabs_implies :
  forall x y : opabs,
    x = y -> (opabs_name x = opabs_name y
              # opabs_params x = opabs_params y
              # opabs_sign x = opabs_sign y).
Proof.
  introv xx; subst; auto.
Qed.

Lemma opabs_deq : Deq opabs.
Proof.
  introv.
  destruct (decidable_eq_opabs_name x y);
    destruct (decidable_eq_opabs_sign x y);
    destruct (parameters_dec (opabs_params x) (opabs_params y));
    destruct x, y; simpl in *; subst; tcsp;
    try (complete (right; intro xx; apply eq_opabs_implies in xx; tcsp)).
Qed.

Lemma sovar_sig_deq : Deq sovar_sig.
Proof.
  introv.
  destruct x, y.
  destruct (deq_nat n0 n2); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
  destruct (deq_nvar n n1); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
Qed.

Definition same_lib_abs : Deq (opabs # list sovar_sig) :=
  deq_prod _ _ opabs_deq (deq_list sovar_sig_deq).

Definition abs_in_lib {o} opabs1 vars1 (lib : @library o) : bool :=
  existsb
    (fun e =>
       match e with
       | lib_abs opabs vars rhs correct =>
         if same_lib_abs (opabs, vars) (opabs1, vars1)
         then true
         else false
       end)
    lib.

Inductive command {o} :=
| COM_add_def :
    forall (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : @SOTerm o)
           (correct : correct_abs opabs vars rhs),
      command.

Definition update {o} (lib : @library o) (com : command) : library :=
  match com with
  | COM_add_def opabs vars rhs correct =>
    if abs_in_lib opabs vars lib
    then lib
    else lib ++ [lib_abs opabs vars rhs correct]
  end.

CoInductive Loop {o} : Type :=
| proc : (@command o -> Loop) -> Loop.

CoFixpoint loop {o} (lib : @library o) : Loop :=
  proc (fun c => loop (update lib c)).


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)
