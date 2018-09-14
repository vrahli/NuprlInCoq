(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export sterm.
Require Export sequents_tacs.
Require Export per_props_tequality.
Require Export per_props_disect.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export sequents2.
Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export variables.
Require Export per_props_subtype_rel.


Lemma equality_subtype_rel_refl {o} :
  forall lib (A: @CTerm o),
    type lib A
    -> equality lib mkc_axiom mkc_axiom (mkc_subtype_rel A A).
Proof.
  intros.
  rw @equality_in_subtype_rel.
  split. spcast. eauto 2 with slow. split. spcast. eauto 2 with slow.
  split; auto. split; auto. unfold subtype_rel. auto.
Qed.
Hint Resolve equality_subtype_rel_refl : slow.

Lemma subtype_rel_refl {o} :
  forall lib (A : @CTerm o),
    subtype_rel lib A A.
Proof.
  introv h; tcsp.
Qed.
Hint Resolve subtype_rel_refl : slow.

Lemma equality_in_mkc_istype {o} :
  forall lib a b (A: @CTerm o),
    equality lib a b (mkc_istype A)
    <=> type lib A # ccomputes_to_valc lib a mkc_axiom # ccomputes_to_valc lib b mkc_axiom.
Proof.
  intros.
  rw @equality_in_subtype_rel.
  split; intro h; repnd; dands; spcast; eauto 3 with slow.
Qed.

Lemma equality_axiom_in_mkc_istype {o} :
  forall lib (A: @CTerm o),
    equality lib mkc_axiom mkc_axiom (mkc_istype A)
    <=> type lib A.
Proof.
  introv; rw @equality_in_mkc_istype; split; intro h; repnd; dands; spcast; eauto 3 with slow.
Qed.

Lemma implies_equality_in_mkc_istype {o} :
  forall lib (A: @CTerm o),
    type lib A
    -> equality lib mkc_axiom mkc_axiom (mkc_istype A).
Proof.
  introv h.
  apply equality_in_mkc_istype; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_equality_in_mkc_istype : slow.

Lemma tequality_subtype_rel_refl {o} :
  forall lib (A B: @CTerm o),
    tequality lib A B
    -> tequality lib (mkc_subtype_rel A A) (mkc_subtype_rel B B) .
Proof.
  intros.
  rw @mkc_subtype_rel_eq. rw @mkc_subtype_rel_eq. apply tequality_mkc_member_sp.
  split.
  { apply tequality_fun. split; auto. }
  { right. spcast. eauto 2 with slow. }
Qed.
Hint Resolve tequality_subtype_rel_refl : slow.

Lemma tequality_mkc_subtype_rel {o} :
  forall lib (A B C D: @CTerm o),
    tequality lib (mkc_subtype_rel A B) (mkc_subtype_rel C D)
    <=> (tequality lib A C # (inhabited_type lib A -> tequality lib B D)).
Proof.
  introv; repeat rewrite mkc_subtype_rel_eq; split; intro h.
  { apply tequality_mkc_member_sp in h; repnd.
    apply tequality_mkc_fun in h0; repnd; tcsp. }
  { repnd.
    apply tequality_mkc_member_sp.
    rw @tequality_mkc_fun; dands; tcsp.
    right; spcast; eauto 3 with slow. }
Qed.

Lemma tequality_mkc_istype {o} :
  forall lib (A B : @CTerm o),
    tequality lib (mkc_istype A) (mkc_istype B) <=> tequality lib A B.
Proof.
  introv.
  unfold mkc_istype.
  rw @tequality_mkc_subtype_rel; split; intro h; repnd; tcsp.
Qed.

Lemma tequality_implies_type_left {o} :
  forall lib (a b : @CTerm o),
    tequality lib a b -> type lib a.
Proof.
  introv teq; eauto 3 with slow.
  apply tequality_refl in teq; auto.
Qed.
Hint Resolve tequality_implies_type_left : slow.

Lemma tequality_implies_type_right {o} :
  forall lib (a b : @CTerm o),
    tequality lib a b -> type lib b.
Proof.
  introv teq; eauto 3 with slow.
  apply tequality_sym in teq; apply tequality_refl in teq; auto.
Qed.
Hint Resolve tequality_implies_type_right : slow.

Lemma teq_and_eq_istype {o} :
  forall lib
         (T1 T2 : @CTerm o),
    tequality lib T1 T2
    -> tequality lib (mkc_istype T1) (mkc_istype T2)
       # equality lib mkc_axiom mkc_axiom (mkc_istype T1).
Proof.
  introv teq.
  rw @tequality_mkc_istype; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_family {o} :
  forall  (x y : NVar) (B : NTerm) (s : CSub) (a : CTerm),
    cover_vars_upto B (csub_filter s [x]) [x]
    -> cover_vars (subst B x (@mk_var  o y)) (snoc s (y, a)).
Proof.
  introv cov.
  unfold cover_vars_upto in cov.
  unfold cover_vars.
  unfold over_vars; simpl in *.
  rw @dom_csub_csub_filter in cov.
  rw @dom_csub_snoc. simpl.
  allrw subvars_eq.
  introv i; allrw in_snoc.
  apply eqset_free_vars_disjoint in i; simpl in *.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
  boolvar; repndors; repnd; tcsp;
    unfold sub_free_vars in *; simpl in *; repndors; subst; tcsp;
      apply cov in i0; simpl in *; allrw in_remove_nvars; allrw in_single_iff;
        repndors; repnd; subst; tcsp.
Qed.


(* This rule says that in order to prove that T is a type
   it is enough to prove that it is inhabited.

    H |-  istype(T)
        By inhabitedType t
    H |-  t in T
*)

Definition rule_inhabited_type {o}
           (H : barehypotheses)
           (T t: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype T)))
    [ mk_baresequent H (mk_conclax (mk_member t T))
    ]
    [].

Lemma tequality_preserves_member {p} :
  forall lib (a b t: @CTerm p),
    tequality lib a b
    ->  member lib t a
    ->  member lib t b.
Proof.
  introv teq inh.
  allunfold @tequality; exrepnd.
  allunfold @member.
  allunfold @equality; exrepnd.
  generalize (nuprl_uniquely_valued lib a eq eq0); intro i; repeat (dest_imp i hyp).
  apply nuprl_refl with (t2 := b); sp.
  exists eq; sp.
  apply nuprl_refl with (t2 := a); sp.
  apply nuprl_sym; sp.
  rw i; sp.
Qed.

Lemma rule_inhabited_type_true {o} :
  forall lib (H : barehypotheses)
         (T t: @NTerm o),
    rule_true lib (rule_inhabited_type H T t).
Proof.
  unfold rule_inhabited_type, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.
  lsubst_tac.
  apply teq_and_eq_istype.
  allrw @tequality_mkc_member_sp; tcsp.
Qed.

Lemma mk_istype_true2_implies {o} :
   forall lib (H : barehypotheses)
          (A : @NTerm o),
     (sequent_true2 lib (mk_baresequent H (mk_conclax (mk_istype A)))) ->
     (forall (s1 s2 : CSub)
             (w : wf_term A)
             (c1 : cover_vars A s1)
             (c2 : cover_vars A s2),
       hyps_functionality lib s1 H ->
       similarity lib s1 s2 H ->
       (type lib (lsubstc A w s1 c1)
        # (tequality lib (lsubstc A w s1 c1) (lsubstc A w s2 c2)))).
Proof.
    unfold mk_istype.
    intros. destruct X as [ ws1 hyp1 ].
    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2) as hyp; clear hyp1.
    repeat (autodimp hyp hh).
    exrepnd.
    lsubst_tac.
    apply equality_in_subtype_rel in hyp1; repnd.
    split. auto.
    generalize_lsubstc_terms T1.
    generalize_lsubstc_terms T2.
    clear - hyp0.
    rw @mkc_subtype_rel_eq in hyp0.
    rw @mkc_subtype_rel_eq in hyp0.
    rw @tequality_mkc_member_sp in hyp0.
    exrepnd.
    rw @tequality_mkc_fun in hyp1.
    exrepnd.
    auto.
Qed.

Lemma implies_cover_vars_var_snoc {o} :
  forall v (s : @CSub o) t,
    cover_vars (mk_var v) (snoc s (v, t)).
Proof.
  introv; apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp.
Qed.
Hint Resolve implies_cover_vars_var_snoc : slow.



(* We can prove that a:A -> B, a:A x B, {a:A | B}, and isect(a:A,B) are types when
    A is a type and  a:A |-  B is a type  *)

(*  Here is the rule for the function type:

    H |-  istype(x:A->B)
        By functionType y
    H |-  istype(A)
    H, y:A |- istype(B[x/y])
*)

Definition rule_function_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_function A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_function_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_function_type H x y A B).
Proof.
  unfold rule_function_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.

(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  apply teq_and_eq_istype.
  apply tequality_function.

  pose proof (Atype s1 s2 w0 c0 c4) as q.
  repeat (autodimp q hyp); repnd; dands; auto;[].
  introv eqa.
  repeat substc_lsubstc_vars3.

  assert (wf_term (subst B x (mk_var y))) as wfs by eauto 3 with slow.
  assert (cover_vars (subst B x (mk_var y)) (snoc s1 (y,a))) as cov1.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c1; tcsp. }
  assert (cover_vars (subst B x (mk_var y)) (snoc s2 (y,a'))) as cov2.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c3; tcsp. }
  pose proof (Btype (snoc s1 (y,a)) (snoc s2 (y,a')) wfs cov1 cov2) as z.

  assert (cover_vars (mk_var y) (snoc s1 (y, a))) as covy1 by eauto 3 with slow.
  assert (cover_vars (mk_var y) (snoc s2 (y, a'))) as covy2 by eauto 3 with slow.

  repeat (autodimp z hyp); repnd; auto.

  { apply hyps_functionality_snoc2; simpl; auto;[].
    introv equa sim'.
    pose proof (Atype s1 s' w0 c0 c') as xx.
    repeat (autodimp xx hyp); repnd; dands; auto;[].
    proof_irr; auto. }

  { sim_snoc; dands; auto. }

  repeat (lsubstc_subst_aeq2;[]).
  repeat (substc_lsubstc_vars3;[]).
  progress lsubst_tac.
  repeat lsubstc_snoc2.
  GC; proof_irr; auto.
Qed.

(*  Next is the rule for the product type:

    H |-  istype(x:A x B)
        By productType y
    H |-  istype(A)
    H, y:A |- istype(B[x/y])
*)

Definition rule_product_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_product A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_product_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_product_type H x y A B).
Proof.
  unfold rule_product_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.

(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  apply teq_and_eq_istype.
  apply tequality_product.

  pose proof (Atype s1 s2 w0 c2 c4) as q.
  repeat (autodimp q hyp); repnd; dands; auto;[].
  introv eqa.
  repeat substc_lsubstc_vars3.

  assert (wf_term (subst B x (mk_var y))) as wfs by eauto 3 with slow.
  assert (cover_vars (subst B x (mk_var y)) (snoc s1 (y,a))) as cov1.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c1; tcsp. }
  assert (cover_vars (subst B x (mk_var y)) (snoc s2 (y,a'))) as cov2.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_product in c0; tcsp.
 }
  pose proof (Btype (snoc s1 (y,a)) (snoc s2 (y,a')) wfs cov1 cov2) as z.

  assert (cover_vars (mk_var y) (snoc s1 (y, a))) as covy1 by eauto 3 with slow.
  assert (cover_vars (mk_var y) (snoc s2 (y, a'))) as covy2 by eauto 3 with slow.

  repeat (autodimp z hyp); repnd; auto.

  { apply hyps_functionality_snoc2; simpl; auto;[].
    introv equa sim'.
    pose proof (Atype s1 s' w0 c2 c') as xx.
    repeat (autodimp xx hyp); repnd; dands; auto;[].
    proof_irr; auto. }

  { sim_snoc; dands; auto. }

  repeat (lsubstc_subst_aeq2;[]).
  repeat (substc_lsubstc_vars3;[]).
  progress lsubst_tac.
  repeat lsubstc_snoc2.
  GC; proof_irr; auto.
Qed.

(*  Next is the rule for the intersection type:

    H |-  istype(isect(x:A, B)
        By isectType y
    H |-  istype(A)
    H, y:A |- istype(B[x/y])
*)

Definition rule_isect_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_isect A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_isect_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_isect_type H x y A B).
Proof.
  unfold rule_isect_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.

(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  apply teq_and_eq_istype.
  apply tequality_isect.

  pose proof (Atype s1 s2 w0 c0 c4) as q.
  repeat (autodimp q hyp); repnd; dands; auto;[].
  introv eqa.
  repeat substc_lsubstc_vars3.

  assert (wf_term (subst B x (mk_var y))) as wfs by eauto 3 with slow.
  assert (cover_vars (subst B x (mk_var y)) (snoc s1 (y,a))) as cov1.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c1; tcsp. }
  assert (cover_vars (subst B x (mk_var y)) (snoc s2 (y,a'))) as cov2.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_isect in c3; tcsp.
 }
  pose proof (Btype (snoc s1 (y,a)) (snoc s2 (y,a')) wfs cov1 cov2) as z.

  assert (cover_vars (mk_var y) (snoc s1 (y, a))) as covy1 by eauto 3 with slow.
  assert (cover_vars (mk_var y) (snoc s2 (y, a'))) as covy2 by eauto 3 with slow.

  repeat (autodimp z hyp); repnd; auto.

  { apply hyps_functionality_snoc2; simpl; auto;[].
    introv equa sim'.
    pose proof (Atype s1 s' w0 c7 c') as xx.
    repeat (autodimp xx hyp); repnd; dands; auto;[].
    proof_irr; auto. }

  { sim_snoc; dands; auto. }

  repeat (lsubstc_subst_aeq2;[]).
  repeat (substc_lsubstc_vars3;[]).
  progress lsubst_tac.
  repeat lsubstc_snoc2.
  GC; proof_irr; auto.
Qed.

(*  Next is the rule for the set type:

    H |-  istype({x:A | B})
        By setType y
    H |-  istype(A)
    H, y:A |- istype(B[x/y])
*)

Definition rule_set_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_set A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_set_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_set_type H x y A B).
Proof.
  unfold rule_set_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.

(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  apply teq_and_eq_istype.
  apply tequality_set.

  pose proof (Atype s1 s2 w0 c0 c4) as q.
  repeat (autodimp q hyp); repnd; dands; auto;[].
  introv eqa.
  repeat substc_lsubstc_vars3.

  assert (wf_term (subst B x (mk_var y))) as wfs by eauto 3 with slow.
  assert (cover_vars (subst B x (mk_var y)) (snoc s1 (y,a))) as cov1.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c1; tcsp. }
  assert (cover_vars (subst B x (mk_var y)) (snoc s2 (y,a'))) as cov2.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_isect in c3; tcsp.
 }
  pose proof (Btype (snoc s1 (y,a)) (snoc s2 (y,a')) wfs cov1 cov2) as z.

  assert (cover_vars (mk_var y) (snoc s1 (y, a))) as covy1 by eauto 3 with slow.
  assert (cover_vars (mk_var y) (snoc s2 (y, a'))) as covy2 by eauto 3 with slow.

  repeat (autodimp z hyp); repnd; auto.

  { apply hyps_functionality_snoc2; simpl; auto;[].
    introv equa sim'.
    pose proof (Atype s1 s' w0 c7 c') as xx.
    repeat (autodimp xx hyp); repnd; dands; auto;[].
    proof_irr; auto. }

  { sim_snoc; dands; auto. }

  repeat (lsubstc_subst_aeq2;[]).
  repeat (substc_lsubstc_vars3;[]).
  progress lsubst_tac.
  repeat lsubstc_snoc2.
  GC; proof_irr; auto.
Qed.


(*  Next is the rule for the dependent intersection type:

    H |-  istype(x:A isect B)
        By depIsectType y
    H |-  istype(A)
    H, y:A |- istype(B[x/y])
*)

Definition rule_dep_isect_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_disect A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_dep_isect_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_dep_isect_type H x y A B).
Proof.
  unfold rule_dep_isect_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.

(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  apply teq_and_eq_istype.
  apply tequality_disect.

  pose proof (Atype s1 s2 w0 c0 c4) as q.
  repeat (autodimp q hyp); repnd; dands; auto;[].
  introv eqa.
  repeat substc_lsubstc_vars3.

  assert (wf_term (subst B x (mk_var y))) as wfs by eauto 3 with slow.
  assert (cover_vars (subst B x (mk_var y)) (snoc s1 (y,a))) as cov1.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_function in c1; tcsp. }
  assert (cover_vars (subst B x (mk_var y)) (snoc s2 (y,a'))) as cov2.
  { eauto 3 with slow.
    apply cover_vars_family.
    apply cover_vars_isect in c3; tcsp.
 }
  pose proof (Btype (snoc s1 (y,a)) (snoc s2 (y,a')) wfs cov1 cov2) as z.

  assert (cover_vars (mk_var y) (snoc s1 (y, a))) as covy1 by eauto 3 with slow.
  assert (cover_vars (mk_var y) (snoc s2 (y, a'))) as covy2 by eauto 3 with slow.

  repeat (autodimp z hyp); repnd; auto.

  { apply hyps_functionality_snoc2; simpl; auto;[].
    introv equa sim'.
    pose proof (Atype s1 s' w0 c7 c') as xx.
    repeat (autodimp xx hyp); repnd; dands; auto;[].
    proof_irr; auto. }

  { sim_snoc; dands; auto. }

  repeat (lsubstc_subst_aeq2;[]).
  repeat (substc_lsubstc_vars3;[]).
  progress lsubst_tac.
  repeat lsubstc_snoc2.
  GC; proof_irr; auto.
Qed.
