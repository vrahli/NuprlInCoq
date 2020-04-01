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
Require Export sequents_props.
Require Export list. (* why? *)


Definition rule_move_to_last {p}
           (b : bool)
           (T C e : NTerm)
           (x : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (mk_baresequent (snoc H (mk_nlhyp b x T) ++ J) (mk_concl C e))
    [ mk_baresequent (snoc (H ++ J) (mk_nlhyp b x T)) (mk_concl C e)
    ]
    [].

Lemma rule_move_to_last_true {p} :
  forall uk (lib : library)
         (b : bool)
         (T C e : NTerm)
         (x : NVar)
         (H J : @barehypotheses p)
         (ni1 : !LIn x (free_vars_hyps J)),
    rule_true uk lib
              (rule_move_to_last
                 b
                 T C e
                 x
                 H J).
Proof.
  unfold rule_move_to_last, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered e (nh_vars_hyps (snoc H (mk_nlhyp b x T) ++ J))) as cv.
  clear hyp1.
  dwfseq.
  introv h.
  destruct b; allsimpl;
  apply ce in h; allrw in_app_iff; allrw in_snoc; allrw in_app_iff; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps J)
          # !LIn x (hyps_free_vars J)
          # covered T (vars_hyps H)
          # True) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (discover; allrw in_app_iff; allrw in_snoc; sp)).

  destruct vhyps as [nixJ1 vhyps ].
  destruct vhyps as [nixJ2 vhyps ].
  destruct vhyps as [covTH vhyps ].
  (* done with proving these simple facts *)

  vr_seq_true.

  dup sim as sim'.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

  vr_seq_true in hyp1.

  pose proof (hyp1
                _ ext
                (snoc (s1a0 ++ s1b) (x,t1))
                (snoc (s2a0 ++ s2b) (x,t2)))
    as h; clear hyp1; rename h into hyp1.

  (* ========== hyps_functionality ========== *)

  autodimp hyp1 hyp.
  { introv xta.
    apply hyps_functionality_move_to_last; auto. }

  (* ========== similarity ========== *)

  autodimp hyp1 hyp.
  { apply similarity_move_to_last; auto. }

  (* ========== now we use hyp1 ========== *)

  exrepnd.
  rw @substitute_hyps_snoc_sub_weak in sim1; auto.

  assert (!LIn x (dom_csub s1b))
    as nix1 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  assert (!LIn x (dom_csub s2b))
    as nix2 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  pose proof (lsubstc_snoc_app_move_to_last C s1a0 s1b x t1 wfct pC1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_to_last C s2a0 s2b x t2 wfct pC2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_to_last e s1a0 s1b x t1 wfce pt1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_to_last e s2a0 s2b x t2 wfce pt2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  auto.
Qed.

Lemma rule_move_to_last_true2 {o} :
  forall uk lib b T C e x H J (ni1 : !LIn x (free_vars_hyps J)),
    @rule_true2 o uk lib (rule_move_to_last b T C e x H J).
Proof.
  introv ni1.
  generalize (rule_move_to_last_true uk lib b T C e x H J ni1); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.


Definition rule_move_down {p}
           (b : bool)
           (T C e : NTerm)
           (x : NVar)
           (H J K : @barehypotheses p) :=
  mk_rule
    (mk_baresequent ((snoc H (mk_nlhyp b x T) ++ J) ++ K) (mk_concl C e))
    [ mk_baresequent ((H ++ (snoc J (mk_nlhyp b x T))) ++ K) (mk_concl C e)
    ]
    [].

Lemma rule_move_down_true {p} :
  forall uk (lib : library)
         (b : bool)
         (T C e : NTerm)
         (x : NVar)
         (H J K : @barehypotheses p)
         (ni1 : !LIn x (free_vars_hyps J)),
    rule_true uk lib
              (rule_move_down
                 b T C e
                 x
                 H J K).
Proof.
  unfold rule_move_down, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered e (nh_vars_hyps ((snoc H (mk_nlhyp b x T) ++ J) ++ K))) as cv.
  clear hyp1.
  dwfseq.
  introv h.
  destruct b; allsimpl; apply ce in h; allrw in_app_iff; allrw in_snoc; allrw in_app_iff; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps J)
          # !LIn x (hyps_free_vars J)
          # covered T (vars_hyps H)
          # True) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (discover; allrw in_app_iff; allrw in_snoc; sp)).

  destruct vhyps as [nixJ1 vhyps ].
  destruct vhyps as [nixJ2 vhyps ].
  destruct vhyps as [covTH vhyps ].
  (* done with proving these simple facts *)

  vr_seq_true.

  dup sim as sim'.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_app in sim5; simpl in sim5; exrepnd; subst; cpx.
  rw @similarity_snoc in sim8; simpl in sim8; exrepnd; subst; cpx.

  vr_seq_true in hyp1.

  pose proof (hyp1
                _ ext
                ((s1a ++ snoc s1b0 (x,t1)) ++ s1b)
                ((s2a ++ snoc s2b0 (x,t2)) ++ s2b))
    as h; clear hyp1; rename h into hyp1.

  applydup @similarity_length in sim2; repnd.
  allrw @length_substitute_hyps.

  (* ========== hyps_functionality ========== *)

  autodimp hyp1 hyp.

  { repeat (rw snoc_append_l).
    introv xta.
    apply hyps_functionality_move_down; auto. }

  (* ========== similarity ========== *)

  autodimp hyp1 hyp.

  { repeat (rw snoc_append_l).
    apply similarity_move_down; auto. }

  (* ========== now we use hyp1 ========== *)

  exrepnd.

  assert (!LIn x (dom_csub s1b0))
    as nix1 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  assert (!LIn x (dom_csub s2b0))
    as nix2 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  pose proof (lsubstc_snoc_app_move_down C s1a s1b0 s1b x t1 wfct pC1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down C s2a s2b0 s2b x t2 wfct pC2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down e s1a s1b0 s1b x t1 wfce pt1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down e s2a s2b0 s2b x t2 wfce pt2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  revert pC0 pC3 pt0 pt3 hyp1 hyp0.
  repeat (rw snoc_append_l).
  sp; PI; auto.
Qed.

Lemma rule_move_down_true2 {o} :
  forall uk lib b T C e x H J K (ni1 : !LIn x (free_vars_hyps J)),
    @rule_true2 o uk lib (rule_move_down b T C e x H J K).
Proof.
  introv ni1.
  generalize (rule_move_down_true uk lib b T C e x H J K ni1); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_move_down_wf {o} :
  forall b T C e x H J K
         (ni1 : !LIn x (free_vars_hyps J))
         (ni2 : !LIn x (vars_hyps J)),
    @wf_rule o (rule_move_down b T C e x H J K).
Proof.
  introv ni1 ni2.

  introv pwf m; allsimpl; repdors; subst; sp;
  allunfold @pwf_sequent; wfseq; sp.

  - allrw @vswf_hypotheses_nil_eq.
    apply wf_hypotheses_app in pwf1; repnd.
    rw @vars_hyps_app in pwf1.
    rw @vars_hyps_snoc in pwf1.
    apply wf_hypotheses_app in pwf3; repnd.
    apply wf_hypotheses_snoc in pwf4; repnd; allsimpl.
    allrw @vars_hyps_snoc; allsimpl.
    apply wf_hypotheses_app; dands.
    + apply wf_hypotheses_app; dands; auto.
      apply vs_wf_hypotheses_snoc; dands; auto; simpl.
      * apply isprog_vars_app1; auto.
      * rw in_app_iff; rw not_over_or; dands; auto.
      * eapply vs_wf_hypotheses_snoc_weak_iff; eauto.
    + rw @vars_hyps_app; rw @vars_hyps_snoc; simpl.
      eapply vs_wf_hypotheses_eqvars; [|eauto].
      rw eqvars_prop; introv; repeat (rw in_app_iff); repeat (rw in_snoc); split; sp.

  - allunfold @covered.
    allrw subvars_prop; introv k; discover.
    allrw in_app_iff; allrw in_snoc; sp.
Qed.


Definition rule_move_up {p}
           (b : bool)
           (T C e : NTerm)
           (x : NVar)
           (H J K : @barehypotheses p) :=
  mk_rule
    (mk_baresequent ((H ++ (snoc J (mk_nlhyp b x T))) ++ K) (mk_concl C e))
    [ mk_baresequent ((snoc H (mk_nlhyp b x T) ++ J) ++ K) (mk_concl C e)
    ]
    [].

Lemma rule_move_up_true {p} :
  forall uk (lib : library)
         (b : bool)
         (T C e : NTerm)
         (x : NVar)
         (H J K : @barehypotheses p)
         (ni1 : !LIn x (free_vars_hyps J)),
    rule_true uk lib
              (rule_move_up
                 b T C e
                 x
                 H J K).
Proof.
  unfold rule_move_up, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered e (nh_vars_hyps ((H ++ (snoc J (mk_nlhyp b x T))) ++ K)))  as cv.
  clear hyp1.
  dwfseq.
  introv h.
  destruct b; allsimpl; apply ce in h; allrw in_app_iff; allrw in_snoc; allrw in_app_iff; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps J)
          # !LIn x (hyps_free_vars J)
          # covered T (vars_hyps H)
          # True) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (discover; allrw in_app_iff; allrw in_snoc; sp)).

  destruct vhyps as [nixJ1 vhyps ].
  destruct vhyps as [nixJ2 vhyps ].
  destruct vhyps as [covTH vhyps ].
  (* done with proving these simple facts *)

  vr_seq_true.

  dup sim as sim'.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_app in sim5; simpl in sim5; exrepnd; subst; cpx.
  rw @substitute_hyps_snoc in sim2.
  rw @similarity_snoc in sim2; simpl in sim2; exrepnd; subst; cpx.

  vr_seq_true in hyp1.

  pose proof (hyp1
                _ ext
                ((snoc s1a0 (x,t1) ++ s1a) ++ s1b)
                ((snoc s2a0 (x,t2) ++ s2a) ++ s2b))
    as h; clear hyp1; rename h into hyp1.

  applydup @similarity_length in sim9; repnd.
  allrw @length_substitute_hyps.

  (* ========== hyps_functionality ========== *)

  autodimp hyp1 hyp.

  { repeat (rw snoc_append_l in eqh).
    introv xta.
    apply hyps_functionality_move_down; auto. }

  (* ========== similarity ========== *)

  autodimp hyp1 hyp.

  { repeat (rw snoc_append_l in sim').
    apply similarity_move_down; auto. }

  (* ========== now we use hyp1 ========== *)

  exrepnd.

  assert (!LIn x (dom_csub s1a))
    as nix1 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  assert (!LIn x (dom_csub s2a))
    as nix2 by (allapply @similarity_dom; repnd;
                allrw @vars_hyps_substitute_hyps; allrw; sp).

  revert pC1 pC2 pt1 pt2.
  repeat (rw snoc_append_l); introv; PI.

  pose proof (lsubstc_snoc_app_move_down2 C s1a0 s1a s1b x t1 wfct pC1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down2 C s2a0 s2a s2b x t2 wfct pC2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down2 e s1a0 s1a s1b x t1 wfce pt1 nix1) as h1;
    exrepnd; PI; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_down2 e s2a0 s2a s2b x t2 wfce pt2 nix2) as h1;
    exrepnd; PI; rw h0; clear h0.

  auto.
Qed.

Lemma rule_move_up_true2 {o} :
  forall uk lib b T C e x H J K (ni1 : !LIn x (free_vars_hyps J)),
    @rule_true2 o uk lib (rule_move_up b T C e x H J K).
Proof.
  introv ni1.
  generalize (rule_move_up_true uk lib b T C e x H J K ni1); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_move_up_wf {o} :
  forall b T C e x H J K
         (ni1 : !LIn x (free_vars_hyps J))
         (isp : isprog_vars (vars_hyps H) T),
    @wf_rule o (rule_move_up b T C e x H J K).
Proof.
  introv ni1 isp.

  introv pwf m; allsimpl; repdors; subst; sp;
  allunfold @pwf_sequent; wfseq; sp.

  - allrw @vswf_hypotheses_nil_eq.
    apply wf_hypotheses_app in pwf1; repnd.
    rw @vars_hyps_app in pwf1.
    rw @vars_hyps_snoc in pwf1.
    apply wf_hypotheses_app in pwf3; repnd.
    apply vs_wf_hypotheses_snoc in pwf3; repnd; allsimpl.
    allrw in_app_iff; allrw not_over_or; repnd.
    apply wf_hypotheses_app; dands.
    + apply wf_hypotheses_app; dands.
      * apply wf_hypotheses_snoc; dands; auto; simpl.
      * rw @vars_hyps_snoc; simpl.
        apply vs_wf_hypotheses_snoc_weak; auto.
    + rw @vars_hyps_app; rw @vars_hyps_snoc; simpl.
      eapply vs_wf_hypotheses_eqvars; [|eauto].
      rw eqvars_prop; introv; repeat (rw in_app_iff); repeat (rw in_snoc); split; sp.

  - allunfold @covered.
    allrw subvars_prop; introv k; discover.
    allrw in_app_iff; allrw in_snoc; sp.
Qed.
