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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export sequents_equality.
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export rules_tyfam.
Require Export rules_tyfam2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export lsubstc_weak.

Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.

Hint Resolve cover_vars_snoc_weak : slow.
Hint Resolve similarity_cover_vars : slow.


Lemma covered_member {o} :
  forall (t T : @NTerm o) vs,
    covered (mk_member t T) vs <-> (covered t vs # covered T vs).
Proof.
  introv; split; intro h; unfold covered in *; simpl in *;
    autorewrite with slow in *; repnd; dands; allrw subvars_eq.

  - introv i; apply h; allrw in_app_iff; tcsp.

  - introv i; apply h; allrw in_app_iff; tcsp.

  - introv i; allrw in_app_iff; repndors; tcsp.
Qed.

Hint Resolve isprogram_csubst : slow.

Lemma csubst_snoc_as_subst_csubst {o} :
  forall (t : @NTerm o) s x a,
    csubst t (snoc s (x, a))
    = subst (csubst t s) x (get_cterm a).
Proof.
  introv.
  unfold csubst.
  allrw @csub2sub_snoc.
  rewrite <- simple_lsubst_snoc; auto.
  introv i.
  apply in_csub2sub in i; auto.
Qed.

Lemma cover_vars_implies_closed_csubst {o} :
  forall (t : @NTerm o) s, cover_vars t s -> closed (csubst t s).
Proof.
  introv h; apply cover_vars_iff_closed_lsubstc; auto.
Qed.

Hint Resolve cover_vars_implies_closed_csubst : slow.

Lemma aeq_simple_subst_lsubst_aux {o} :
  forall (t : @NTerm o) v u sub,
    cl_sub sub
    -> covered u (dom_sub sub)
    -> alpha_eq
         (subst
            (lsubst_aux t (sub_filter sub [v]))
            v
            (lsubst_aux u sub))
         (lsubst_aux (subst t v u) sub).
Proof.
  introv clsub cov.
  unfold subst, lsubst; boolvar; allsimpl; allrw app_nil_r.

  - pose proof (simple_subst_lsubst_aux t u v sub) as h.
    repeat (autodimp h hyp).
    rewrite h; eauto 2 with slow.

  - pose proof (change_bvars_alpha_spec t (free_vars u)) as h; simpl in h; repnd.
    remember (change_bvars_alpha (free_vars u) t) as t'; clear Heqt'.
    pose proof (simple_lsubst_aux_lsubst_aux_aeq t t' u v sub) as k.
    repeat (autodimp k hyp); eauto 3 with slow; apply alphaeq_eq; auto.

  - provefalse; destruct n.
    pose proof (free_vars_lsubst_aux_cl u sub) as fv.
    autodimp fv hyp.
    rewrite fv; clear fv.
    pose proof (covered_implies_remove_nvars u (dom_sub sub) (dom_sub sub)) as h.
    repeat (autodimp h hyp).
    rewrite h; auto.

  - provefalse; destruct n.
    pose proof (free_vars_lsubst_aux_cl u sub) as fv.
    autodimp fv hyp.
    rewrite fv; clear fv.
    pose proof (covered_implies_remove_nvars u (dom_sub sub) (dom_sub sub)) as h.
    repeat (autodimp h hyp).
    rewrite h; auto.
Qed.

Lemma lsubstc_snoc_snoc_as_lsubstc_subst_snoc {o} :
  forall (t : @NTerm o) u s wt z ws x wu cu a c c',
    !LIn z (dom_csub s)
    -> alphaeqc
         (lsubstc t wt (snoc (snoc s (z, lsubstc u wu s cu)) (x, a)) c)
         (lsubstc (subst t z u) ws (snoc s (x, a)) c').
Proof.
  introv nizs.
  unfold alphaeqc; simpl.
  repeat (rewrite (csubst_snoc_as_subst_csubst _ _ x)).
  apply lsubst_alpha_congr3; eauto 2 with slow;[].

  unfold csubst.
  rw @csub2sub_snoc; simpl.
  rewrite <- simple_lsubst_snoc; eauto 3 with slow;
    [|introv i; apply in_csub2sub in i; auto];[].

  unfold csubst.
  repeat unflsubst.
  eapply alpha_eq_trans;[|apply aeq_simple_subst_lsubst_aux]; eauto 2 with slow;
    [|rewrite dom_csub_eq; auto].

  rewrite sub_filter_disjoint1; eauto 2 with slow.
  apply disjoint_singleton_r.
  rewrite dom_csub_eq; auto.
Qed.


(*

  Our elimination rules are simpler than the ones in Nuprl.
  This rule is to get back the same behavior

<<
   H, x : t in T |- C ext e[z\t]

     By elimination z

     H, z : T, x : z = t in T |- C ext e
>>

 *)


Definition rule_elimination_concl {o} (H : @bhyps o) x z t T C e :=
  mk_baresequent
    (snoc H (mk_hyp x (mk_member t T)))
    (mk_concl C (subst e z t)).

Definition rule_elimination_hyp1 {o} (H : @bhyps o) x z t T C e :=
  mk_baresequent
    (snoc (snoc H (mk_hyp z T)) (mk_hyp x (mk_equality (mk_var z) t T)))
    (mk_concl C e).

Definition rule_elimination {o}
           (H : @bhyps o)
           (x z : NVar)
           (t T C e : NTerm) :=
  mk_rule
    (rule_elimination_concl H x z t T C e)
    [
      rule_elimination_hyp1 H x z t T C e
    ]
    [(*sarg_term a, sarg_var z*)].

Lemma rule_elimination_true3 {o} :
  forall lib (H : @bhyps o) x z t T C e (covt : covered t (nh_vars_hyps H)),
    rule_true3 lib (rule_elimination H x z t T C e).
Proof.
  unfold rule_elimination, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    prove_seq; eauto 3 with slow.

    - allrw @vswf_hypotheses_nil_eq.
      allrw @wf_hypotheses_snoc; repnd; simpl in *.
      dands; tcsp.

    - apply wf_term_subst; auto.
      allrw @vswf_hypotheses_nil_eq.
      allrw @wf_hypotheses_snoc; repnd; simpl in *.
      allrw @isprog_vars_iff_covered; repnd; auto.
      allrw <- @wf_member_iff; tcsp.

    - apply covered_subst.

      + eapply covered_subvars;[|eauto].
        rw subvars_eq; introv i; allsimpl; allrw in_snoc; tcsp.

      + apply covered_snoc_weak; auto.
  }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert (!LIn z (free_vars C)
          # !LIn z (vars_hyps H)
          # !LIn x (vars_hyps H)
          # !LIn z (free_vars T)
          # !LIn x (free_vars T)
          # !LIn z (free_vars t)
          # !LIn x (free_vars t)
          # (x <> z)) as vhyps.
  {
    clear hyp1.
    dwfseq.
    sp; try (complete (discover; allrw in_snoc; repndors; tcsp)).
  }

  destruct vhyps as [ nizH vhyps ].
  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nizT vhyps ].
  destruct vhyps as [ nixT vhyps ].
  destruct vhyps as [ nizt vhyps ].
  destruct vhyps as [ nixt dxz ].
  (* done with proving these simple facts *)

  vr_seq_true.
  allrw @similarity_snoc; exrepnd; simpl in *; subst.
  lsubst_tac.

  vr_seq_true in hyp1.

  assert (cover_vars t s2a) as covt2 by (eauto 2 with slow).

  pose proof (hyp1 (snoc (snoc s1a (z, lsubstc t wt s1a ct0)) (x, t1))
                   (snoc (snoc s2a (z, lsubstc t wt s2a covt2)) (x, t2))) as hyp1.
  repeat (autodimp hyp1 h); exrepnd.

  {
    (* hyps_functionality *)

    apply hyps_functionality_snoc2; simpl; auto.

    {
      introv equ sim'.
      apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx.
      lsubst_tac.
      apply equality_in_mkc_equality in equ; repnd.
      allrw @equality_in_member; repnd.

      apply tequality_mkc_equality2.

      pose proof (eqh (snoc s2a0 (x,mkc_axiom))) as h.
      autodimp h hyp.

      - sim_snoc; dands; auto.
        lsubst_tac.
        apply equality_in_member; dands; auto; spcast; eauto 2 with slow.

      - apply eq_hyps_snoc in h; simpl in h.
        exrepnd; cpx.
        lsubst_tac.
        rw @tequality_mkc_member in h0; tcsp.
    }

    apply hyps_functionality_snoc2; simpl; auto.

    {
      introv equ sim'.
      allrw @equality_in_member; repnd.

      pose proof (eqh (snoc s' (x,mkc_axiom))) as h.
      autodimp h hyp.

      - sim_snoc; dands; auto.
        lsubst_tac.
        apply equality_in_member; dands; auto; spcast; eauto 2 with slow.

      - apply eq_hyps_snoc in h; simpl in h.
        exrepnd; cpx.
        lsubst_tac.
        allrw @tequality_mkc_member; tcsp.
    }

    apply (hyps_functionality_init_seg_snoc2 _ _ t1 t2 _  _ _ w p) in eqh; auto.
    lsubst_tac; auto.
  }

  {
    (* similarity *)

    sim_snoc2; dands; auto; try (sim_snoc; dands; auto).

    { apply wf_equality; eauto 2 with slow. }

    {
      apply cover_vars_equality; dands; auto; eauto 2 with slow.
      apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp.
    }

    {
      allrw @equality_in_member; repnd.

      pose proof (eqh (snoc s2a (x,mkc_axiom))) as h.
      autodimp h hyp.

      - sim_snoc; dands; auto.
        lsubst_tac.
        apply equality_in_member; dands; auto.
        spcast; apply computes_to_valc_refl; eauto 2 with slow.

      - apply eq_hyps_snoc in h; simpl in h.
        exrepnd; cpx.
        lsubst_tac.
        eapply tequality_mkc_member_implies_sp;[eauto|]; auto.
    }

    {
      lsubst_tac.
      allrw @equality_in_member; repnd.
      apply equality_in_mkc_equality; dands; auto.
    }
  }

  lsubst_tac.

  pose proof (lsubstc_snoc_snoc C s1a z x (lsubstc t wt s1a ct0) t1 wf1 pC0) as q.
  autodimp q hyp; exrepnd.
  rewrite q0 in hyp0.
  rewrite q0 in hyp1.
  clear q0.
  proof_irr.

  pose proof (lsubstc_snoc_snoc C s2a z x (lsubstc t wt s2a covt2) t2 wf1 pC3) as q.
  autodimp q hyp; exrepnd.
  rewrite q0 in hyp0.
  clear q0.
  proof_irr.

  dands; auto;[].

  assert (!LIn z (dom_csub s1a)) as nizs1.
  { apply similarity_dom in sim3; repnd; allrw; auto. }

  assert (!LIn z (dom_csub s2a)) as nizs2.
  { apply similarity_dom in sim3; repnd; allrw; auto. }

  eapply equality_respects_alphaeqc_left in hyp1;
    [|apply lsubstc_snoc_snoc_as_lsubstc_subst_snoc]; auto;[].
  eapply equality_respects_alphaeqc_right in hyp1;
    [|apply lsubstc_snoc_snoc_as_lsubstc_subst_snoc]; auto;[].
  exact hyp1.
Qed.

Lemma rule_elimination_true_ext_lib {o} :
  forall lib (H : @bhyps o) x z t T C e (covt : covered t (nh_vars_hyps H)),
    rule_true_ext_lib lib (rule_elimination H x z t T C e).
Proof.
  introv covt.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_elimination_true3; auto.
Qed.
