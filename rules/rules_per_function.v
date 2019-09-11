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


Require Import sequents_tacs.
Require Import rules_pertype2.
Require Import subst_tacs.
Require Import cequiv_tacs.
Require Import tactics2.
Require Import per_props_per.
Require Import rwper.



Lemma wf_sequent_per_function_rel :
  forall H f A B J C e z,
    wf_term C
    -> wf_term e
    -> wf_hypotheses (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
    -> wf_sequent
         (mk_bseq
            (snoc H (mk_hyp f (mk_pertype (mk_per_function_rel A B))) ++ J)
            (mk_concl C (subst e z mk_axiom))).
Proof.
  introv wfC wfe wfhyps.
  unfold wf_sequent, wf_concl; simpl; sp.
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; sp.
  rw nt_wf_eq; sp.
Qed.

Lemma closed_type_nwfsequent_per_function_rel :
  forall H f A B J C e z,
    covered C (vars_hyps (snoc H (mk_hyp f (mk_per_function A B)) ++ J))
    -> closed_type_baresequent
         (mk_bseq
            (snoc H (mk_hyp f (mk_pertype (mk_per_function_rel A B))) ++ J)
            (mk_concl C (subst e z mk_axiom))).
Proof.
  introv.
  unfold closed_type_baresequent, closed_type; simpl.
  allrw vars_hyps_app; allrw vars_hyps_snoc; simpl; sp.
Qed.

Lemma wf_csequent_per_function_rel_app :
  forall H f A B J C e z s,
    wf_term C
    -> wf_term (subst e z mk_axiom)
    -> covered C (vars_hyps (snoc H (mk_hyp f (mk_per_function A B)) ++ J))
    -> covered (subst e z mk_axiom)
               (nh_vars_hyps (snoc H (mk_hyp f (mk_per_function A B)) ++ J))
    -> wf_hypotheses
         (snoc (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
               (mk_hyp z (mk_member (mk_apply (mk_var f) s) (mk_apply B s))))
    -> wf_csequent
         (mk_bseq
            (snoc (snoc H (mk_hyp f (mk_pertype (mk_per_function_rel A B))) ++ J)
                  (mk_hhyp z (mk_apply2 (mk_per_function_rel A B) (mk_var f) (mk_var f))))
            (mk_concl C (subst e z mk_axiom))).
Proof.
  introv wfC wfe covC cove wfhyps.
  unfold wf_csequent, wf_sequent, closed_type, closed_extract, wf_concl; simpl.
  allrw vars_hyps_snoc; allrw vars_hyps_app; allrw vars_hyps_snoc; simpl.
  allrw nh_vars_hyps_snoc; allrw nh_vars_hyps_app; allrw nh_vars_hyps_snoc; simpl.
  dands; try (complete sp).

  allrw wf_hypotheses_snoc; allsimpl; repnd; dands; try (complete sp).
  allrw vars_hyps_app; allsimpl.
  allrw vars_hyps_snoc; allsimpl.
  apply isprog_vars_apply2; dands; try (complete sp).
  apply isprog_vars_app1.
  apply isprog_vars_weak_l; sp.
  allrw wf_hypotheses_app; repnd.
  allrw wf_hypotheses_snoc; repnd; allsimpl.
  rw <- isprog_vars_mk_per_function_rel_iff; sp;
  rw <- isprog_vars_mk_per_function_iff in wfhyps3; sp.

  apply isprog_vars_app1.
  apply isprog_vars_var_if; rw in_snoc; sp.

  apply isprog_vars_app1.
  apply isprog_vars_var_if; rw in_snoc; sp.

  allsimpl.
  apply covered_subvars with (vs1 := snoc (vars_hyps H) f ++ vars_hyps J); sp.
  rw subvars_prop; introv i.
  allrw in_snoc; allrw in_app_iff; allrw in_snoc; sp.
Qed.

Lemma wf_csequent_per_function_rel_type :
  forall H f A B J,
    wf_hypotheses (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
    -> wf_csequent
         (mk_bseq
            (snoc H (mk_hyp f (mk_pertype (mk_per_function_rel A B))))
            (mk_concl_t
               (mk_apply2 (mk_per_function_rel A B) (mk_var f) (mk_var f)))).
Proof.
  introv wfhyps.
  unfold wf_csequent, wf_sequent, closed_type, closed_extract, wf_concl; simpl.
  rw <- wf_apply2_iff.
  rw covered_apply2.
  rw covered_per_function_rel.
  rw wf_term_mk_per_function_rel.
  allrw vars_hyps_snoc; simpl.
  allrw covered_var.
  allrw in_snoc.
  allrw wf_term_mk_per_function; repnd.
  allrw wf_hypotheses_app; repnd.
  allrw wf_hypotheses_snoc; repnd; allsimpl.
  rw isprog_vars_pertype.
  rw <- isprog_vars_mk_per_function_rel_iff.
  allrw <- isprog_vars_mk_per_function_iff; repnd.

  dands; try (complete sp).

  apply isprog_vars_eq in wfhyps3; repnd.
  allrw nt_wf_eq; sp.

  apply isprog_vars_eq in wfhyps1; repnd.
  allrw nt_wf_eq; sp.

  apply isprog_vars_eq in wfhyps3; repnd.
  unfold covered.
  apply subvars_trans with (vs2 := vars_hyps H); sp.
  apply subvars_snoc_weak; sp.

  apply isprog_vars_eq in wfhyps1; repnd.
  unfold covered.
  apply subvars_trans with (vs2 := vars_hyps H); sp.
  apply subvars_snoc_weak; sp.
Qed.

Lemma wf_csequent_per_function_rel_type2 :
  forall H f A B J,
    wf_hypotheses (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
    -> wf_csequent
         (mk_bseq
            (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
            (mk_concl_t
               (mk_apply2 (mk_per_function_rel A B) (mk_var f) (mk_var f)))).
Proof.
  introv wfhyps.
  unfold wf_csequent, wf_sequent, closed_type, closed_extract, wf_concl; simpl.
  rw <- wf_apply2_iff.
  rw covered_apply2.
  rw covered_per_function_rel.
  rw wf_term_mk_per_function_rel.
  allrw vars_hyps_app; simpl.
  allrw vars_hyps_snoc; simpl.
  allrw covered_var.
  allrw in_app_iff.
  allrw in_snoc.
  allrw wf_term_mk_per_function; repnd.
  allrw wf_hypotheses_app; repnd.
  allrw wf_hypotheses_snoc; repnd; allsimpl.
  rw isprog_vars_pertype.
  rw <- isprog_vars_mk_per_function_rel_iff.
  allrw <- isprog_vars_mk_per_function_iff; repnd.

  dands; try (complete sp).

  apply isprog_vars_eq in wfhyps3; repnd.
  allrw nt_wf_eq; sp.

  apply isprog_vars_eq in wfhyps1; repnd.
  allrw nt_wf_eq; sp.

  apply isprog_vars_eq in wfhyps3; repnd.
  unfold covered.
  apply subvars_trans with (vs2 := vars_hyps H); sp.
  apply subvars_app_weak_l; sp.
  apply subvars_snoc_weak; sp.

  apply isprog_vars_eq in wfhyps1; repnd.
  unfold covered.
  apply subvars_trans with (vs2 := vars_hyps H); sp.
  apply subvars_app_weak_l; sp.
  apply subvars_snoc_weak; sp.
Qed.


Lemma unfold_mk_per_function_rel2 :
  forall A B,
    {va, vb, vf, vg, vx : NVar
     $ mk_per_function_rel A B
       = mk_lam vf (mk_lam vg (erase (mk_per_function_base va vb vf vg vx A B)))
     # (va, vb, vf, vg, vx) = newvars5 [A, B] }.
Proof.
  apply unfold_mk_per_function_rel.
Qed.

Lemma equality_in_per_function_implies :
  forall f g A B w s c,
    equality f g (lsubstc (mk_per_function A B) w s c)
    -> {wa : wf_term A
        , {wb : wf_term B
        , {ca : cover_vars A s
        , {cb : cover_vars B s
        , let cA := lsubstc A wa s ca in
          let cB := lsubstc B wb s cb in
          type cA
          # forall a a',
              equality a a' cA
              -> equality (mkc_apply f a) (mkc_apply g a') (mkc_apply cB a)
                 # tequality (mkc_apply cB a) (mkc_apply cB a')}}}}.
Proof.
  introv eq.

  assert (wf_term A)
    as wA by (dup w as w'; apply wf_term_mk_per_function in w'; sp).
  assert (wf_term B)
    as wB by (dup w as w'; apply wf_term_mk_per_function in w'; sp).

  assert (cover_vars A s)
    as cA by (dup c as c'; apply cover_vars_per_function in c'; sp).
  assert (cover_vars B s)
    as cB by (dup c as c'; apply cover_vars_per_function in c'; sp).

  exists wA wB cA cB; cbv zeta.

  unfold mk_per_function in eq.
  lsubst_tac.
  rwpers.
  generalize (unfold_mk_per_function_rel2 A B); intro e; exrepnd.
  apply newvars5_prop2 in e0; simpl in e0;
  repeat (rw app_nil_r in e0); repeat (rw in_app_iff in e0);
  repeat (rw not_over_or in e0); repnd.

  revert dependent eq0.
  revert dependent w1.
  revert dependent c1.
  rw e1; introv isper ty inh.
  lsubst_tac.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw inhabited_type_erasec in inh.

  unfold mk_per_function_base in inh.
  lsubst_tac.
  unfold inhabited_type in inh; exrepnd.
  rwpers.

  dands.

  generalize (inh0 mkc_axiom mkc_axiom); intro k.
  autodimp k hyp; repnd.
  rwpers; auto.
  repeat substc_lsubstc_vars3; lsubst_tac.
  rwpers.
  generalize (k0 mkc_axiom mkc_axiom); intro j.
  autodimp j hyp; repnd.
  rwpers; auto.
  repeat substc_lsubstc_vars3; lsubst_tac.
  rwpers.

  introv ea.
  generalize (inh0 a a); clear inh0; intro k.
  autodimp k hyp; repnd.
  rwpers.
  clear k.
  repeat substc_lsubstc_vars3; lsubst_tac.
  rwpers.
  generalize (k0 a' a'); clear k0; intro eq.
  autodimp eq hyp; repnd.
  rwpers.
  clear eq.
  repeat substc_lsubstc_vars3; lsubst_tac.
  rwpers.
  generalize (eq0 mkc_axiom mkc_axiom); clear eq0; intro eq'.
  autodimp eq' hyp; repnd.
  rwpers.
  clear eq'.
  repeat substc_lsubstc_vars3; lsubst_tac.
  rwpers; repnd; auto.
  apply equality_in_uand_implies in eq'0; exrepnd.
  lsubst_tac.
  rwper; repnd; auto.
  dands; auto.
  apply inhabited_implies_tequality in eq'0.
  rw tequality_iff_mkc_tequality in eq'0; auto.
Qed.


(* [29] ============ PER-FUNCTION ELIMINATION ============ *)

  (*
   H, f : per-function(A,B), J |- C ext e[z\axiom]

     By perFunctionElimination s y z

     H, f : per-function(A,B), J |- a in A
     H, f : per-function(A,B), J, z : (f a) in (B a) |- C ext e
 *)
Definition rule_per_function_elimination
           (A B C a e : NTerm)
           (f z : NVar)
           (H J : barehypotheses) :=
  mk_rule
    (mk_bseq
       (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
       (mk_concl C (subst e z mk_axiom)))
    [ mk_bseq
        (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
        (mk_conclax (mk_member a A)),
      mk_bseq
        (snoc (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
              (mk_hyp z (mk_member (mk_apply (mk_var f) a) (mk_apply B a))))
        (mk_concl C e)
    ]
    [sarg_term a, sarg_var z].

Lemma rule_per_function_elimination_true :
  forall A B C a e : NTerm,
  forall f z : NVar,
  forall H J : barehypotheses,
    rule_true (rule_per_function_elimination
                 A B C a e
                 f z
                 H J).
Proof.
  unfold rule_per_function_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered
            (subst e z mk_axiom)
            (nh_vars_hyps (snoc H (mk_hyp f (mk_per_function A B)) ++ J))) as cv.
  (* begin proof of assert *)
  clear hyp1 hyp2.
  dwfseq.
  intros.
  generalize (isprogram_lsubst2 e [(z,mk_axiom)]); simpl; intro k.
  dest_imp k hyp; sp; cpx.
  unfold subst in X; rw k in X; clear k.
  rw in_remove_nvars in X; simpl in X; sp.
  apply not_over_or in X; sp.
  generalize (ce x); sp.
  allrw in_app_iff; allrw in_snoc; sp.
  allrw in_app_iff; allrw in_snoc; sp.
  (* end proof of assert *)

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn f (vars_hyps H)
          # !LIn f (vars_hyps J)
          # !LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # !(z = f)
          # !LIn f (free_vars (mk_per_function_rel A B))
          # disjoint (free_vars (mk_per_function_rel A B)) (vars_hyps J)
          # !LIn z (free_vars C)) as vhyps.

  clear hyp1 hyp2.
  remember (mk_per_function A B) as pf.
  remember (mk_per_function_rel A B) as pfr.
  dwfseq.
  subst.
  allrw free_vars_mk_per_function.
  allrw free_vars_per_function_rel_eq.
  sp;
    try (complete (discover; repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp));
    try (complete (unfold disjoint; unfold disjoint in wfh11; introv i; discover; sp)).

  destruct vhyps as [ nifH vhyps ].
  destruct vhyps as [ nifJ vhyps ].
  destruct vhyps as [ nizH vhyps ].
  destruct vhyps as [ nizJ vhyps ].
  destruct vhyps as [ nezf vhyps ].
  destruct vhyps as [ nifFR vhyps ].
  destruct vhyps as [ disjFRJ nizC ].
  (* done with proving these simple facts *)


  (* The following is used by lsubst_tac to clean some substitutions *)
  assert (!LIn f (free_vars (mk_per_function_rel A B))) as nffrel.
  (* begin proof of assert *)
  clear hyp1 hyp2.
  rw wf_hypotheses_app in wfh; destruct wfh as [wfha wfhb].
  rw wf_hypotheses_snoc in wfha; destruct wfha as [isp wfha].
  destruct wfha as [ni wfh]; simphyps.
  rw isprog_vars_eq in isp; destruct isp as [sv ntwf].
  intro k; rw subvars_prop in sv.
  rw <- free_vars_mk_per_function in k.
  apply sv in k; sp.
  (* end proof of assert *)

  assert (!LIn z (free_vars (subst e z mk_axiom))) as nizs.
  (* begin proof of assert *)
  unfold subst.
  rw isprogram_lsubst2; try (complete (simpl; sp; inj)).
  rw in_remove_nvars; simpl; sp.
  (* end proof of assert *)

  assert (disjoint (free_vars A) (vars_hyps J))
    as disjAJ
      by (allrw free_vars_per_function_rel_eq; allrw disjoint_app_l; sp).

  assert (disjoint (free_vars B) (vars_hyps J))
    as disjBJ
      by (allrw free_vars_per_function_rel_eq; allrw disjoint_app_l; sp).

  assert (!LIn f (free_vars A))
    as nifA
      by (allrw free_vars_per_function_rel_eq; allrw in_app_iff; sp).

  assert (!LIn f (free_vars B))
    as nifB
      by (allrw free_vars_per_function_rel_eq; allrw in_app_iff; sp).

  vr_seq_true.

  dup sim as simapp.
  rw similarity_app in sim; simpl in sim; exrepnd; subst; inj.
  rw similarity_snoc in sim5; simpl in sim5; exrepnd; subst; inj.
  allrw length_snoc; inj.

  apply equality_in_per_function_implies in sim2; exrepnd; cbv zeta in sim2; repnd.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom))
                   (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)));
    clear hyp2; intros hyp2.
  repeat (autodimp hyp2 h); exrepnd.

  (* hyps_functionality *)

  generalize (hyps_functionality_snoc
                (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
                (mk_hyp z (mk_member (mk_apply (mk_var f) a) (mk_apply B a)))
                (snoc s1a0 (f, t1) ++ s1b)
                mkc_axiom); simpl; intro k.
  apply k; try (complete auto); clear k.
  introv eq sim; GC; lsubst_tac.
  rw tequality_mkc_member.
  apply equality_refl in eq.
  rw <- member_member_iff in eq.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b) s'); clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw member_eq in hyp1.
  rw <- member_member_iff in hyp1.
  rw tequality_mkc_member in hyp0; repnd.

  assert (equality (lsubstc a w2 (snoc s1a0 (f, t1) ++ s1b) c2)
                   (lsubstc a w2 s' c4)
                   (lsubstc A wa s1a0 ca)) as eqa.
  sp.
  unfold member in hyp1.
  spcast; apply equality_respects_cequivc_right with (t2 := lsubstc a w2 (snoc s1a0 (f, t1) ++ s1b) c2); sp.

  applydup sim2 in eqa; repnd.

  duplicate sim as sim'.
  apply eqh in sim'.

  rw eq_hyps_app in sim'; simpl in sim'; exrepnd; subst; inj.
  apply app_split in sim'0; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; inj.

  rw eq_hyps_snoc in sim'5; simpl in sim'5; exrepnd; subst; inj.
  allrw length_snoc; inj; GC.
  lsubst_tac.

XXXXXXXXXXXX

  rw tequality_function in sim'0; repnd.

  applydup sim'0 in eqa as teq.

  assert (substc (lsubstc a wa (snoc s1a (f, t0) ++ s1b0) c3) x
                 (lsubstc_vars B w2 (csub_filter s1a [x]) [x] c2)
          = lsubstc (subst B x a) wT (snoc s1a (f, t0) ++ s1b0) cT)
         as eq1
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq1 in teq.

  assert (substc (lsubstc a wa (snoc s2a1 (f, t3) ++ s2b0) c5) x
                 (lsubstc_vars B w2 (csub_filter s2a1 [x]) [x] c9)
          = lsubstc (subst B x a) wT (snoc s2a1 (f, t3) ++ s2b0) cT0)
         as eq2
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq2 in teq.

  split; try (complete auto).

  rw similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  apply app_split in sim7; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.
  apply app_split in sim9; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.
  rw similarity_snoc in sim12; simpl in sim12; exrepnd; subst; cpx.
  lsubst_tac.
  rw equality_in_function in sim9; repnd.
  applydup sim9 in eqa as eqf.
  rw eq1 in eqf.

  split.

  split; intro m; try (complete auto).
  apply equality_sym in eqf.
  apply equality_refl in eqf.
  allunfold member.
  apply tequality_preserving_equality with (A := (lsubstc (subst B x a) wT (snoc s1a0 (f, t1) ++ s1b) cT)); sp.

  left; sp.

  (* similarity *)

  assert (wf_term (mk_member (mk_apply (mk_var f) a) (subst B x a))) as wm.
  apply wf_member; sp; try (apply wf_apply; sp).
  apply subst_preserves_wf_term; sp.

  assert (cover_vars (mk_member (mk_apply (mk_var f) a) (subst B x a))
                     (snoc s1a0 (f, t1) ++ s1b)) as cm.
  apply cover_vars_member; sp.
  apply cover_vars_apply; sp.
  apply cover_vars_var.
  rw dom_csub_app; rw dom_csub_snoc; rw in_app_iff; rw in_snoc; simpl; sp.
  rw cover_vars_eq; rw dom_csub_app; rw dom_csub_snoc; insub.
  (* begin proof of last cover_vars *)
  rw cover_vars_eq; rw cover_vars_covered; apply covered_subst; sp.
  rw dom_csub_app; rw dom_csub_snoc; simpl.
  rw cons_app; apply covered_app_weak_l.
  clear sim2 sim5; unfold cover_vars_upto in c2; unfold covered.
  prove_subvars c2; allsimpl; sp.
  rw dom_csub_csub_filter in l; rw in_remove_nvars in l; rw in_single_iff in l.
  rw in_snoc; sp.
  clear hyp1; rw covered_equality in ct0; repnd.
  unfold covered; unfold covered in ct1.
  rw vars_hyps_app in ct1; rw vars_hyps_snoc in ct1; simpl in ct1.
  rw dom_csub_app; rw dom_csub_snoc; simpl.
  allapply similarity_dom; repnd; allrw; rw vars_hyps_substitute_hyps; sp.
  (* end proof of last cover_vars *)

  rw similarity_snoc; simpl.
  exists (snoc s1a0 (f, t1) ++ s1b)
         (snoc s2a0 (f, t2) ++ s2b)
         mkc_axiom mkc_axiom
         wm cm; sp.
  lsubst_tac.
  rw member_eq.
  rw <- member_member_iff.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b)
                   (snoc s2a0 (f, t2) ++ s2b));
    clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw member_eq in hyp1.
  rw <- member_member_iff in hyp1.
  rw tequality_mkc_member in hyp0; repnd.
  unfold member in hyp1.
  apply sim2 in hyp1.

  assert (substc (lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) c3) x
                 (lsubstc_vars B w2 (csub_filter s1a0 [x]) [x] c2)
          = lsubstc (subst B x a) wT (snoc s1a0 (f, t1) ++ s1b) cT)
         as eq1
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq1 in hyp1.
  apply equality_refl in hyp1; sp.

  (* conclusion *)

  lsubst_tac; sp.

  assert (lsubstc e wfce0 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom)) pt0
          = lsubstc (subst e z mk_axiom) wfce (snoc s1a0 (f, t1) ++ s1b) pt1) as eq1.
  apply lsubstc_eq_if_csubst.
  rw <- csubst_swap.
  rw cons_as_app.
  rw <- csubst_app.
  unfold csubst, subst; simpl; sp.
  rw dom_csub_app; rw dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  assert (lsubstc e wfce0 (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)) pt3
          = lsubstc (subst e z mk_axiom) wfce (snoc s2a0 (f, t2) ++ s2b) pt2) as eq2.
  apply lsubstc_eq_if_csubst.
  rw <- csubst_swap.
  rw cons_as_app.
  rw <- csubst_app.
  unfold csubst, subst; simpl; sp.
  rw dom_csub_app; rw dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  rw eq1 in hyp2; rw eq2 in hyp2; sp.
Qed.

Lemma rule_per_function_elimination_true :
  forall A B C a e : NTerm,
  forall f z : NVar,
  forall H J : barehypotheses,
    rule_true (rule_per_function_elimination
                 A B C a e
                 f z
                 H J).
Proof.
  unfold rule_per_function_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered
            (subst e z mk_axiom)
            (nh_vars_hyps (snoc H (mk_hyp f (mk_per_function A B)) ++ J))) as cv.
  (* begin proof of assert *)
  clear hyp1 hyp2.
  dwfseq.
  intros.
  generalize (isprogram_lsubst2 e [(z,mk_axiom)]); simpl; intro k.
  dest_imp k hyp; sp; cpx.
  unfold subst in X; rw k in X; clear k.
  rw in_remove_nvars in X; simpl in X; sp.
  apply not_over_or in X; sp.
  generalize (ce x); sp.
  allrw in_app_iff; allrw in_snoc; sp.
  allrw in_app_iff; allrw in_snoc; sp.
  (* end proof of assert *)

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn f (vars_hyps H)
          # !LIn f (vars_hyps J)
          # !LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # !(z = f)
          # !LIn f (free_vars (mk_per_function_rel A B))
          # disjoint (free_vars (mk_per_function_rel A B)) (vars_hyps J)
          # !LIn z (free_vars C)) as vhyps.

  clear hyp1 hyp2.
  remember (mk_per_function A B) as pf.
  remember (mk_per_function_rel A B) as pfr.
  dwfseq.
  subst.
  allrw free_vars_per_function.
  allrw free_vars_per_function_rel.
  sp;
    try (complete (discover; repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp));
    try (complete (unfold disjoint; unfold disjoint in wfh11; introv i; discover; sp)).

  destruct vhyps as [ nifH vhyps ].
  destruct vhyps as [ nifJ vhyps ].
  destruct vhyps as [ nizH vhyps ].
  destruct vhyps as [ nizJ vhyps ].
  destruct vhyps as [ nezf vhyps ].
  destruct vhyps as [ nifFR vhyps ].
  destruct vhyps as [ disjFRJ nizC ].
  (* done with proving these simple facts *)


  (* The following is used by lsubst_tac to clean some substitutions *)
  assert (!LIn f (free_vars (mk_per_function_rel A B))) as nffrel.
  (* begin proof of assert *)
  clear hyp1 hyp2.
  rw wf_hypotheses_app in wfh; destruct wfh as [wfha wfhb].
  rw wf_hypotheses_snoc in wfha; destruct wfha as [isp wfha].
  destruct wfha as [ni wfh]; simphyps.
  rw isprog_vars_eq in isp; destruct isp as [sv ntwf].
  intro k; rw subvars_prop in sv.
  rw <- free_vars_mk_per_function in k.
  apply sv in k; sp.
  (* end proof of assert *)

  assert (!LIn z (free_vars (subst e z mk_axiom))) as nizs.
  (* begin proof of assert *)
  unfold subst.
  rw isprogram_lsubst2; try (complete (simpl; sp; cpx)).
  rw in_remove_nvars; simpl; sp.
  (* end proof of assert *)

XXXXXXXXXXXXXXX

  (* we use pertype_elimination4 --- !! I SHOULD NOT USE THAT *)
  generalize (rule_pertype_elimination4_true_ex
                z (mk_per_function_rel A B) C (subst e z mk_axiom) f H J).
  intro rti.
  unfold rule_true_if in rti; simpl in rti.
  apply rti; simpl; clear rti.

  apply wf_sequent_per_function_rel; sp.

  apply closed_type_nwfsequent_per_function_rel; sp.

  introv seq; repdors; subst; try (complete sp).

  apply wf_csequent_per_function_rel_app with (s := a); sp.

  apply wf_csequent_per_function_rel_type with (J := J); sp.

  allunfold args_constraints; allsimpl.
  introv k; repdors; sp.

  (* Now we start proving that the sequents we got from pertype_elimination4 are true *)
  fold (mk_per_function A B).
  introv es; introv; repdors; try (complete sp); subst.


  (* 1st subgoal *)
  destruct c as [wfseq cl]; simpl in cl.
  destruct cl as [cltype clext].
  destruct wfseq as [wfhyps wfconcl].
  destruct wfconcl as [wfconclT wfconcle].
  simpl in wfconclT, wfconcle, cltype, clext.
  vr_seq_true.

  duplicate sim as simapp.

  rw similarity_snoc in sim; simpl in sim; exrepnd; subst; cpx.
  rw similarity_app in sim3; simpl in sim3; exrepnd; subst; cpx.
  rw similarity_snoc in sim6; simpl in sim6; exrepnd; subst; cpx.

  lsubst_tac.

XXXXXXXXXXX


  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a (f, t1) ++ s1b) (z, mkc_axiom))
                   (snoc (snoc s2a (f, t2) ++ s2b) (z, mkc_axiom)));
    clear hyp2; intros hyp2.
  repeat (autodimp hyp2 h); exrepnd.

  (* hyps_functionality *)

  generalize (hyps_functionality_snoc
                (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
                (mk_hyp z (mk_member (mk_apply (mk_var f) a) (mk_apply B a)))
                (snoc s1a (f, t1) ++ s1b)
                mkc_axiom); simpl; intro k.
  apply k; try (complete auto); clear k.
  introv eq sim; GC; lsubst_tac.
  apply equality_refl in eq.
  rw <- member_member_iff in eq.
  rw tequality_mkc_member.

  (* similarity *)

XXXXXXXXXX

(*

 1) Provide a characterization of
     equality t1 t2
           (mkc_apply2
              (lsubstc (mk_per_function_rel A B) w1 s1a c1) t0 t0)

 *)


  (* 2nd subgoal *)
  generalize (rule_per_function_type_true A B f H []); intro rt.
  unfold rule_true, rule_per_function_type in rt; simpl in rt.
  rw app_nil_r in rt.
  destruct c as [wfs c].
  destruct c as [clt cle].
  generalize (rt wfs clt); clear rt; intro rt.
  autodimp rt hyp.
  dest_imp rt hyp.

Abort.





(* [17] ============ PER-IMAGE EQUALITY ============ *)

  (*
   H |- per-image(A1,f1) = per-image(A2,f2) in Type

     By perImageEquality ()

     H |- f1 = f2 in Base
     H |- A1 = A2 in Type
 *)
Definition rule_per_image_equality
           (A1 A2 f1 f2 : NTerm)
           (i : nat)
           (H : nwfhypotheses) :=
  mk_rule
    (mk_nwfsequent
       H
       (mk_conclax (mk_equality
                      (mk_per_image A1 f1)
                      (mk_per_image A2 f2)
                      (mk_uni i))))
    [ mk_nwfsequent H (mk_conclax (mk_equality f1 f2 mk_base)),
      mk_nwfsequent H (mk_conclax (mk_equality A1 A2 (mk_uni i)))
    ]
    [].

Lemma rule_per_image_equality_true :
  forall A1 A2 f1 f2 : NTerm,
  forall i : nat,
  forall H : nwfhypotheses,
    rule_true (rule_per_image_equality
                 A1 A2 f1 f2
                 i
                 H).
Proof.
  unfold rule_per_image_equality, rule_true, closed_type_nwfsequent, closed_extract_nwfsequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  inversion wg as [ wfh wfc ]; allsimpl.
  inversion wfc as [ wtt wte ]; allsimpl; clear wfc.
  generalize (hyps (mk_nwfsequent H (mk_conclax (mk_equality f1 f2 mk_base)))
                   (inl eq_refl))
             (hyps (mk_nwfsequent H (mk_conclax (mk_equality A1 A2 (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destruct ws1 as [ ws1 ws1' ]; allsimpl.
  destruct ws2 as [ ws2 ws2' ]; allsimpl.
  destruct ws1 as [ wh1 wc1 ]; allsimpl.
  destruct ws2 as [ wh2 wc2 ]; allsimpl.
  destruct ws1' as [ ct1 ce1 ]; allsimpl.
  destruct ws2' as [ ct2 ce2 ]; allsimpl.
  allunfold closed_type; allsimpl.
  allunfold closed_extract; allsimpl;
  GC.

  allunfold closed_type; allunfold closed_extract; allunfold nh_vars_hyps; allsimpl.

  assert (covered mk_axiom (vars_hyps (filter is_nh H))) as ce by prove_seq.
  exists ce.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  allrw sequent_true_eq_VR.
  rw VR_sequent_true_all; simpl; introv sim eqh.
  rw VR_sequent_true_ex in hyp1; rw VR_sequent_true_ex in hyp2; allsimpl.
  generalize (hyp1 s1 s2) (hyp2 s1 s2); clear hyp1 hyp2; intros hyp1 hyp2.
  repeat (dest_imp hyp1 h); repeat (dest_imp hyp2 h); exrepnd.
  lift_lsubst;
    lift_lsubst in hyp0;
    lift_lsubst in hyp1;
    lift_lsubst in hyp2;
    lift_lsubst in hyp3.
  allrw member_eq.
  allrw <- member_equality_iff.

Abort.
