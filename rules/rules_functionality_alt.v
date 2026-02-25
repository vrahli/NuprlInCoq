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



Require Export rules_typehood.
Require Export rules_functionality.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)




(* [15] ============ FUNCTIONALITY FOR EQUALITY (ALT) ============ *)

(**

  This is a simpler version of the functionality rule to prove equalities:
<<
   G, x : A, J |- a = b in T

     By functionalityForEquality y z

     G, x : A, J | istype(T)
     G, x : Base, y : Base, z : x = y in A, J |- a = b[x\y] in T
>>
*)

Definition rule_functionality_for_equality_alt {o}
           (G J     : @barehypotheses o)
           (A a b T : NTerm)
           (x y z   : NVar) :=
  mk_rule
    (mk_baresequent (snoc G (mk_hyp x A) ++ J) (mk_conclax (mk_equality a b T)))
    [ mk_baresequent
        (snoc G (mk_hyp x A) ++ J)
        (mk_conclax (mk_istype T)),
      mk_baresequent
        (snoc (snoc (snoc G (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_equality (mk_var x) (mk_var y) A))
              ++ J)
        (mk_conclax (mk_equality a (subst b x (mk_var y)) T))
    ]
    [].

Lemma rule_functionality_for_equality_alt_true {o} :
  forall lib (G J     : @barehypotheses o)
         (A a b T : NTerm)
         (x y z   : NVar)
         (bc      : !LIn y (bound_vars b)),
    rule_true lib (rule_functionality_for_equality_alt G J A a b T x y z).
Proof.
  unfold rule_functionality_for_equality_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ws1 hyp1].
  destruct Hyp0 as [ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.

  exists (@covered_axiom o (nh_vars_hyps (snoc G (mk_hyp x A) ++ J))).

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps G)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps G)
          # !LIn y (vars_hyps J)
          # !LIn z (vars_hyps G)
          # !LIn z (vars_hyps J)
          # !LIn x (free_vars A)
          # !LIn y (free_vars A)
          # !LIn z (free_vars A)
          # !LIn y (free_vars T)
          # !LIn z (free_vars T)
          # !LIn y (free_vars a)
          # !LIn z (free_vars a)
          # !LIn y (free_vars b)
          # !LIn z (free_vars b)
          # !LIn y (free_vars_hyps J)
          # !LIn z (free_vars_hyps J)
          # !LIn y (hyps_free_vars J)
          # !LIn z (hyps_free_vars J)
          # x <> y
          # x <> z
          # y <> z) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp; try (complete (discover; allrw in_app_iff; allrw in_snoc; sp;
                     generalize (subvars_hs_vars_hyps G); intro k1; rw subvars_prop in k1;
                     generalize (subvars_hs_vars_hyps J); intro k2; rw subvars_prop in k2;
                     discover; sp)).

  destruct vhyps as [ nixG vhyps ].
  destruct vhyps as [ nixJ vhyps ].
  destruct vhyps as [ niyG vhyps ].
  destruct vhyps as [ niyJ vhyps ].
  destruct vhyps as [ nizG vhyps ].
  destruct vhyps as [ nizJ vhyps ].
  destruct vhyps as [ nixA vhyps ].
  destruct vhyps as [ niyA vhyps ].
  destruct vhyps as [ nizA vhyps ].
  destruct vhyps as [ niyT vhyps ].
  destruct vhyps as [ nizT vhyps ].
  destruct vhyps as [ niya vhyps ].
  destruct vhyps as [ niza vhyps ].
  destruct vhyps as [ niyb vhyps ].
  destruct vhyps as [ nizb vhyps ].
  destruct vhyps as [ niyJ2 vhyps ].
  destruct vhyps as [ nizJ2 vhyps ].
  destruct vhyps as [ niyJ3 vhyps ].
  destruct vhyps as [ nizJ3 vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxz nyz ].
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  apply teq_and_eq_if_equality with (H := snoc G (mk_hyp x A) ++ J); auto.

  - vr_seq_true in hyp1.
    generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
    lsubst_tac.
    rw @tequality_mkc_istype in hyp0. auto.
    
  - clear dependent s1.
    clear dependent s2.
    introv hf sim.

    clear hyp1.

    rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

    vr_seq_true in hyp2.
    generalize (hyp2
                  (snoc (snoc (snoc s1a0 (x,t1)) (y,t2)) (z,mkc_axiom) ++ s1b)
                  (snoc (snoc (snoc s2a0 (x,t1)) (y,t2)) (z,mkc_axiom) ++ s2b)).
    clear hyp2; intro hyp2.

    autodimp hyp2 hyp.


    (* -- We start proving the hyps_functionality -- *)
    introv sim'.
    rw @similarity_app in sim'; simpl in sim'; exrepnd; subst; cpx.
    apply app_split in sim'0; simpl; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
    rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
    rw @similarity_snoc in sim'6; simpl in sim'6; exrepnd; subst; cpx.
    lsubst_tac.
    allrw @equality_in_base_iff.
    allrw @equality_in_mkc_equality; repnd.
    spcast; GC.

    rewrite substitute_hyps_snoc_sub_weak in sim'1; try (complete sp).
    rewrite substitute_hyps_snoc_sub_weak in sim'1; try (complete sp).

    duplicate hf as hf1.
    apply hyps_functionality_init_seg with (s3 := s2b0) in hf1; try (complete sp).
    generalize (hyps_functionality_init_seg_snoc2 lib s1a t2 t0 G x A w p hf1 sim2);
      intro hf2.

    rw @eq_hyps_app; simpl.
    eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto.

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto;
    try (complete (lsubst_tac; apply @tequality_base)).

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto;
    try (complete (lsubst_tac; apply @tequality_base)).

    lsubst_tac.
    apply @tequality_equality_if_cequivc; auto.
    generalize (hf1 (snoc s2a1 (x,t0))); intro k.
    autodimp k hyp.
    rw @similarity_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto.
    exact sim2.
    rw @eq_hyps_snoc in k; simpl in k; exrepnd; cpx; proof_irr; auto.

    apply sub_eq_hyps_snoc_weak; auto.
    apply sub_eq_hyps_snoc_weak; auto.
    generalize (hf (snoc s2a1 (x,t5) ++ s2b0)); intro k.
    autodimp k hyp.
    rw @similarity_app; simpl.
    eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.
    rw @similarity_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto.
    apply @equality_respects_cequivc; auto.
    apply @equality_refl in sim2; exact sim2.
    rw @eq_hyps_app in k; simpl in k; exrepnd; cpx.
    apply app_split in k0; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    apply app_split in k2; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).


    (* -- We now prove the similarity hyp -- *)
    autodimp hyp2 hyp.
    rw @similarity_app; simpl.
    eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.

    rw @similarity_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.

    rw @similarity_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.

    rw @similarity_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; auto.

    lsubst_tac.
    apply @equality_in_base_iff; spcast; auto.

    lsubst_tac.
    apply @equality_in_base_iff; spcast; auto.

    lsubst_tac.
    rw <- @member_equality_iff; auto.

    rewrite substitute_hyps_snoc_sub_weak; sp.
    rewrite substitute_hyps_snoc_sub_weak; sp.


    (* -- We can now use our hypothesis -- *)
    exrepnd; lsubst_tac; proof_irr; GC.
    allrw @member_eq.
    allrw <- @member_equality_iff.

    assert (!LIn z (free_vars (subst b x (mk_var y)))) as nizs.
    generalize (eqvars_free_vars_disjoint b [(x,mk_var y)]); simpl; boolvar; simpl;
    rw @fold_subst; introv eqv iz;
    rw eqvars_prop in eqv; apply eqv in iz;
    rw in_app_iff in iz; rw in_remove_nvars in iz; repeat (rw in_single_iff in iz); sp.

    repeat lsubstc_snoc_app; proof_irr; GC.
    revert dependent w3.
    revert dependent c'6.
    revert dependent c'11.
    lsubst_tac.
    introv tequ equ.
    repeat lsubstc_app; proof_irr.
    revert dependent w'3.
    revert dependent c'3.
    revert dependent w'6.
    revert dependent c'14.
    repeat csubst_subst_snoc.
    repeat (rw @csub_filter_snoc; boolvar; allrw not_over_or; try (complete sp)).
    repeat (rw @csub_filter_trivial; try (complete (rw disjoint_singleton_l; insub))).
    introv tequ equ; proof_irr.
    eapply @equality_commutes4 in tequ; eauto.

    Unshelve.
    { auto. }
    { auto. }
    { apply cover_vars_equality; dands;
        try (apply cover_vars_var); repeat (rw @dom_csub_snoc); simpl;
        repeat (rw in_snoc); sp;
        repeat (apply cover_vars_snoc_weak); auto.
      eapply similarity_cover_vars; eauto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { apply wf_equality; auto. }
    { apply cover_vars_equality; dands;
        try (apply cover_vars_var); repeat (rw @dom_csub_snoc); simpl;
        repeat (rw in_snoc); sp;
        repeat (apply cover_vars_snoc_weak); auto;
        apply cover_vars_change_sub with (sub1 := s1a); auto;
        allapply @similarity_dom; sp; allrw; sp. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
Qed.
