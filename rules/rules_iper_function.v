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


Require Export sequents_tacs.
(*Require Import rules_pertype2.*)
Require Export subst_tacs.
Require Export cequiv_tacs.
Require Export tactics2.
Require Export per_props_per.
Require Export rwper.
Require Export list. (* why *)


(* begin hide *)


Lemma unfold_mk_iper_function_rel2 {o} :
  forall A B : @NTerm o,
    {va, vb, vf, vg, vx : NVar
     $ mk_iper_function_rel A B
       = mk_lam vf (mk_lam vg (mk_per_function_base va vb vf vg vx A B))
     # (va, vb, vf, vg, vx) = newvars5 [A, B] }.
Proof.
  apply unfold_mk_iper_function_rel.
Qed.

Lemma equality_in_iper_function {o} :
  forall lib f g A B w s c,
    @equality o lib f g (lsubstc (mk_iper_function A B) w s c)
    -> {wa : wf_term A
        , {wb : wf_term B
        , {ca : cover_vars A s
        , {cb : cover_vars B s
        , let cA := lsubstc A wa s ca in
          let cB := lsubstc B wb s cb in
          type lib cA
          # forall a a',
              equality lib a a' cA
              -> equality lib (mkc_apply f a) (mkc_apply g a') (mkc_apply cB a)
                 # tequality lib (mkc_apply cB a) (mkc_apply cB a')}}}}.
Proof.
  introv eq.

  assert (wf_term A)
    as wA by (dup w as w'; apply wf_term_mk_iper_function in w'; sp).
  assert (wf_term B)
    as wB by (dup w as w'; apply wf_term_mk_iper_function in w'; sp).

  assert (cover_vars A s)
    as cA by (dup c as c'; apply cover_vars_iper_function in c'; sp).
  assert (cover_vars B s)
    as cB by (dup c as c'; apply cover_vars_iper_function in c'; sp).

  exists wA wB cA cB; cbv zeta.

  unfold mk_iper_function in eq.
  lsubst_tac.
  rwpers.
  generalize (unfold_mk_iper_function_rel2 A B); intro e; exrepnd.
  apply newvars5_prop2 in e0; simpl in e0;
  repeat (rw app_nil_r in e0); repeat (rw in_app_iff in e0);
  repeat (rw not_over_or in e0); repnd.

  revert dependent eq0.
  revert dependent w1.
  revert dependent c1.
  rw e1; introv isper ty inh.
  lsubst_tac.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
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
  apply equality_in_uand_implies in eq'0; exrepnd.
  lsubst_tac.
  rwpers; repnd; dands; auto.
  apply inhabited_implies_tequality in eq'0.
  rw @tequality_iff_mkc_tequality in eq'0; auto.
Qed.

Lemma tequality_mk_iper_function_implies {o} :
  forall lib A B w s1 s2 c1 c2,
    @tequality o lib (lsubstc (mk_iper_function A B) w s1 c1)
              (lsubstc (mk_iper_function A B) w s2 c2)
    -> {wa : wf_term A
        , {wb : wf_term B
        , {ca1 : cover_vars A s1
        , {ca2 : cover_vars A s2
        , {cb1 : cover_vars B s1
        , {cb2 : cover_vars B s2
        , let A1 := lsubstc A wa s1 ca1 in
          let A2 := lsubstc A wa s2 ca2 in
          let B1 := lsubstc B wb s1 cb1 in
          let B2 := lsubstc B wb s2 cb2 in
          tequality lib A1 A2
          # forall a1 a2,
              equality lib a1 a2 A1
              -> tequality lib (mkc_apply B1 a1) (mkc_apply B2 a2)}}}}}}.
Proof.
  introv teq.

  assert (wf_term A)
    as wA by (dup w as w'; apply wf_term_mk_iper_function in w'; sp).
  assert (wf_term B)
    as wB by (dup w as w'; apply wf_term_mk_iper_function in w'; sp).

  assert (cover_vars A s1)
    as cA1 by (dup c1 as c'; apply cover_vars_iper_function in c'; sp).
  assert (cover_vars B s1)
    as cB1 by (dup c1 as c'; apply cover_vars_iper_function in c'; sp).
  assert (cover_vars A s2)
    as cA2 by (dup c2 as c'; apply cover_vars_iper_function in c'; sp).
  assert (cover_vars B s2)
    as cB2 by (dup c2 as c'; apply cover_vars_iper_function in c'; sp).

  exists wA wB cA1 cA2 cB1 cB2; cbv zeta.

  unfold mk_iper_function in teq.
  lsubst_tac.
  rwpers.
  generalize (unfold_mk_iper_function_rel2 A B); intro e; exrepnd.
  apply newvars5_prop2 in e0; simpl in e0;
  repeat (rw app_nil_r in e0); repeat (rw in_app_iff in e0);
  repeat (rw not_over_or in e0); repnd.

  revert dependent teq0.
  revert dependent w1.
  revert dependent c0.
  revert dependent c3.
  rw e1; introv isper teq.
  lsubst_tac.

  generalize (teq mkc_axiom mkc_axiom); clear teq; intro teq.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  unfold mk_per_function_base in teq.
  lsubst_tac.
  rwpers.

  dands.

  generalize (teq mkc_axiom mkc_axiom); clear teq; intro teq.
  autodimp teq hyp.
  rwpers.
  repeat substc_lsubstc_vars3; lsubst_tac; auto; rwpers.
  generalize (teq mkc_axiom mkc_axiom); clear teq; intro teq.
  autodimp teq hyp.
  rwpers.
  repeat substc_lsubstc_vars3; lsubst_tac; auto; rwpers; repnd; auto.

  introv ea.
  generalize (teq a1 a1); clear teq; intro teq.
  autodimp teq hyp.
  rwpers.
  repeat substc_lsubstc_vars3; lsubst_tac; auto; rwpers.
  generalize (teq a2 a2); clear teq; intro teq.
  autodimp teq hyp.
  rwpers.
  repeat substc_lsubstc_vars3; lsubst_tac; auto; rwpers; repnd; auto.
  generalize (teq mkc_axiom mkc_axiom); clear teq; intro teq.
  autodimp teq hyp.
  rwpers.
  repeat substc_lsubstc_vars3.
  apply tequality_uand_implies in teq; exrepnd.
  clear teq3.
  lsubst_tac.
  rw @tequality_mkc_tequality in teq4; repnd.
  apply tequality_trans with (t2 := mkc_apply (lsubstc B wB s1 cB1) a2); auto.
Qed.


(* end hide *)


(* [29] ============ IPER-FUNCTION ELIMINATION ============ *)

  (*
   H, f : iper-function(A,B), J |- C ext e[z\axiom]

     By iperFunctionElimination s y z

     H, f : iper-function(A,B), J |- a in A
     H, f : iper-function(A,B), J, z : (f a) in (B a) |- C ext e
 *)
Definition rule_iper_function_elimination {o}
           (A B C a e : NTerm)
           (f z : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_bseq
       (snoc H (mk_hyp f (mk_iper_function A B)) ++ J)
       (mk_concl C (subst e z mk_axiom)))
    [ mk_bseq
        (snoc H (mk_hyp f (mk_iper_function A B)) ++ J)
        (mk_conclax (mk_member a A)),
      mk_bseq
        (snoc (snoc H (mk_hyp f (mk_iper_function A B)) ++ J)
              (mk_hyp z (mk_member (mk_apply (mk_var f) a) (mk_apply B a))))
        (mk_concl C e)
    ]
    [sarg_term a, sarg_var z].

Lemma rule_iper_function_elimination_true {o} :
  forall lib (A B C a e : NTerm),
  forall f z : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_iper_function_elimination
                 A B C a e
                 f z
                 H J).
Proof.
  unfold rule_iper_function_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered
            (subst e z mk_axiom)
            (nh_vars_hyps (snoc H (mk_hyp f (mk_iper_function A B)) ++ J))) as cv.
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
          # !LIn f (free_vars (mk_iper_function_rel A B))
          # disjoint (free_vars (mk_iper_function_rel A B)) (vars_hyps J)
          # !LIn z (free_vars C)) as vhyps.

  clear hyp1 hyp2.
  remember (mk_iper_function A B) as pf.
  remember (mk_iper_function_rel A B) as pfr.
  dwfseq.
  subst.
  allrw @free_vars_mk_iper_function.
  allrw @free_vars_iper_function_rel_eq.
  sp;
    try (complete (allunfold @disjoint; introv k; discover; allrw in_app_iff; sp));
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
  assert (!LIn f (free_vars (mk_iper_function_rel A B))) as nffrel.
  (* begin proof of assert *)
  clear hyp1 hyp2.
  allapply @vswf_hypotheses_nil_implies.
  rw @wf_hypotheses_app in wfh; destruct wfh as [wfha wfhb].
  rw @wf_hypotheses_snoc in wfha; destruct wfha as [isp wfha].
  destruct wfha as [ni wfh]; simphyps.
  rw @isprog_vars_eq in isp; destruct isp as [sv ntwf].
  intro k; rw subvars_prop in sv.
  rw <- @free_vars_mk_iper_function in k.
  apply sv in k; sp.
  (* end proof of assert *)

  assert (!LIn z (free_vars (subst e z mk_axiom))) as nizs.
  (* begin proof of assert *)
  unfold subst.
  rw @isprogram_lsubst2; try (complete (simpl; sp; cpx)).
  rw in_remove_nvars; simpl; sp.
  (* end proof of assert *)

  assert (disjoint (free_vars A) (vars_hyps J))
    as disjAJ
      by (allrw @free_vars_iper_function_rel_eq; allrw disjoint_app_l; sp).

  assert (disjoint (free_vars B) (vars_hyps J))
    as disjBJ
      by (allrw @free_vars_iper_function_rel_eq; allrw disjoint_app_l; sp).

  assert (!LIn f (free_vars A))
    as nifA
      by (allrw @free_vars_iper_function_rel_eq; allrw in_app_iff; sp).

  assert (!LIn f (free_vars B))
    as nifB
      by (allrw @free_vars_iper_function_rel_eq; allrw in_app_iff; sp).

  vr_seq_true.

  dup sim as simapp.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

  apply equality_in_iper_function in sim2; exrepnd; cbv zeta in sim2; repnd.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom))
                   (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)));
    clear hyp2; intros hyp2.
  repeat (autodimp hyp2 h); exrepnd.

  (* hyps_functionality *)

  generalize (hyps_functionality_snoc
                lib (snoc H (mk_hyp f (mk_iper_function A B)) ++ J)
                (mk_hyp z (mk_member (mk_apply (mk_var f) a) (mk_apply B a)))
                (snoc s1a0 (f, t1) ++ s1b)
                mkc_axiom); simpl; intro k.
  apply k; try (complete auto); clear k.
  introv eq sim; GC; lsubst_tac.
  rw @tequality_mkc_member.
  apply equality_refl in eq.
  rw <- @member_member_iff in eq.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b) s'); clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  rw @tequality_mkc_member in hyp0; repnd.

  assert (equality lib (lsubstc a w2 (snoc s1a0 (f, t1) ++ s1b) c2)
                   (lsubstc a w2 s' c4)
                   (lsubstc A wa s1a0 ca)) as eqa.
  sp.
  unfold member in hyp1.
  spcast; apply @equality_respects_cequivc_right with (t2 := lsubstc a w2 (snoc s1a0 (f, t1) ++ s1b) c2); sp.
  clear hyp0.

  applydup sim2 in eqa.

  duplicate sim as sim'.
  apply eqh in sim'.

  rw @eq_hyps_app in sim'; simpl in sim'; exrepnd; subst; cpx.
  apply app_split in sim'0; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.

  rw @eq_hyps_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
  lsubst_tac.

  apply tequality_mk_iper_function_implies in sim'0; exrepnd;
  cbv zeta in sim'0; repnd; proof_irr; GC.

  applydup sim'0 in eqa as teq.

  split; try (complete auto).

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; inj.
  allrw length_snoc.
  apply app_split in sim5; repnd; allrw length_snoc; try (complete (allrw; sp)); subst; inj.
  apply app_split in sim8; repnd; allrw length_snoc; try (complete (allrw; sp)); subst; inj.
  allrw length_snoc; inj; GC.
  rw @similarity_snoc in sim11; simpl in sim11; exrepnd; subst; inj.
  apply equality_in_iper_function in sim8; exrepnd; cbv zeta in sim8; repnd; proof_irr; GC.
  applydup sim8 in eqa as eqf; repnd.

  split; try (complete (left; auto)).

  split; intro m; try (complete auto).
  apply equality_sym in eqf0.
  apply equality_refl in eqf0.
  allunfold @member.
  apply @tequality_preserving_equality with (A := mkc_apply (lsubstc B wb s1a0 cb)
                                                           (lsubstc a w2 (snoc s1a0 (f, t1) ++ s1b) c2)); sp.

  (* similarity *)

  assert (wf_term (mk_member (mk_apply (mk_var f) a) (mk_apply B a))) as wm.
  clear hyp1.
  apply wf_member; sp; try (apply wf_apply; sp); apply wf_member_iff in wfct1; sp.

  assert (cover_vars (mk_member (mk_apply (mk_var f) a) (mk_apply B a))
                     (snoc s1a0 (f, t1) ++ s1b)) as cm.
  (* end proof of assert *)
  apply cover_vars_member; sp; apply cover_vars_apply; sp.
  apply cover_vars_var.
  rw @dom_csub_app; rw @dom_csub_snoc; rw in_app_iff; rw in_snoc; simpl; sp.
  dup ct0 as cvm.
  apply covered_iff_cover_vars with (s := snoc s1a0 (f, t1) ++ s1b) in cvm.
  rw @cover_vars_member in cvm; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; rw @vars_hyps_app; rw @vars_hyps_snoc; simpl.
  allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; sp.
  apply cover_vars_app_weak; apply cover_vars_snoc_weak; auto.
  dup ct0 as cvm.
  apply covered_iff_cover_vars with (s := snoc s1a0 (f, t1) ++ s1b) in cvm.
  rw @cover_vars_member in cvm; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; rw @vars_hyps_app; rw @vars_hyps_snoc; simpl.
  allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; sp.
  (* end proof of assert *)

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (f, t1) ++ s1b)
         (snoc s2a0 (f, t2) ++ s2b)
         (@mkc_axiom o) (@mkc_axiom o)
         wm cm; sp.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_member_iff.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b)
                   (snoc s2a0 (f, t2) ++ s2b));
    clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  rw @tequality_mkc_member in hyp0; repnd.
  unfold member in hyp1.
  apply sim2 in hyp1; repnd; auto.
  apply equality_refl in hyp4; auto.

  (* conclusion *)

  lsubst_tac; sp.

  assert (lsubstc e wfce0 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom)) pt0
          = lsubstc (subst e z mk_axiom) wfce (snoc s1a0 (f, t1) ++ s1b) pt1) as eq1.
  apply lsubstc_eq_if_csubst.
  rw <- @csubst_swap.
  rw cons_as_app.
  rw <- @csubst_app.
  unfold csubst, subst; simpl; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  assert (lsubstc e wfce0 (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)) pt3
          = lsubstc (subst e z mk_axiom) wfce (snoc s2a0 (f, t2) ++ s2b) pt2) as eq2.
  apply lsubstc_eq_if_csubst.
  rw <- @csubst_swap.
  rw cons_as_app.
  rw <- @csubst_app.
  unfold csubst, subst; simpl; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  rw eq1 in hyp2; rw eq2 in hyp2; sp.
Qed.


(* begin hide *)
