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
Require Export rules_useful.
Require Export per_props_set.
Require Export rules_move.
Require Export subst_tacs.
Require Export cequiv_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export rules_tyfam.
Require Export list. (* why? *)


Ltac aautodimp H hyp :=
  match type of H with
    | forall v : ?T1, ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete auto)
        | try (let concl := fresh "hyp" in
                 pose proof (H hyp) as concl;
               try (clear hyp);
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.

Lemma mk_nlhyp_true {o} :
  forall x (t : @NTerm o),
    mk_nlhyp true x t = mk_hhyp x t.
Proof. sp. Qed.

Lemma if_in_open_bar_tequality_and_equality {o} :
  forall (lib : @library o) A B a b C,
    in_open_bar
      lib
      (fun lib' => tequality lib' A B # equality lib' a b C)
    -> tequality lib A B # equality lib a b C.
Proof.
  introv h; dands.
  { apply all_in_ex_bar_tequality_implies_tequality; auto.
    eapply in_open_bar_pres; eauto; introv xt q; tcsp. }
  { apply all_in_ex_bar_equality_implies_equality; auto.
    eapply in_open_bar_pres; eauto; introv xt q; tcsp. }
Qed.



(**

<<
   H, x : {v:A | B[v]}, J |- C ext e[y\x]

     By setElimination y z

     H, x : {v:A | B[v]}, y : A, [z : B[v\y]], J |- C ext e
>>

 *)

Definition rule_set_elimination {p}
           (A B C e : NTerm)
           (v x y z : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_set A v B)) ++ J)
       (mk_concl C (subst e y (mk_var x))))
    [ mk_baresequent
        ((snoc (snoc (snoc H (mk_hyp x (mk_set A v B)))
                     (mk_hyp y A))
               (mk_hhyp z (subst B v (mk_var y))))
           ++ J)
        (mk_concl C e)
    ]
    [].

Lemma rule_set_elimination_true {p} :
  forall lib
         (A B C e : NTerm)
         (v x y z : NVar)
         (H J : @barehypotheses p)
         (bc1 : !LIn y (bound_vars B))
         (bc2 : !LIn x (bound_vars e))
         (bc3 : !LIn v (vars_hyps H))
         (bc4 : !LIn v (vars_hyps J))
         (bc5 : x <> v),
    rule_true lib (rule_set_elimination
                 A B C e
                 v x y z
                 H J).
Proof.
  unfold rule_set_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered
            (subst e y (mk_var x))
            (nh_vars_hyps (snoc H (mk_hyp x (mk_set A v B)) ++ J))) as cv.
  clear hyp1.
  dwfseq.
  introv h.
  pose proof (eqvars_free_vars_disjoint e [(y,mk_var x)]) as ev.
  fold (subst e y (mk_var x)) in ev.
  eapply eqvars_prop in ev; apply ev in h; clear ev; simpl in h.
  rw in_app_iff in h; rw in_remove_nvars in h; rw in_single_iff in h.
  rw in_app_iff; rw in_snoc; dorn h; repnd.
  apply ce in h0; rw in_app_iff in h0; repeat (rw in_snoc in h0); repeat (dorn h0); tcsp.
  revert h; boolvar; simpl; intro h; try (dorn h); subst; tcsp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (disjoint (free_vars A) (vars_hyps J)
          # disjoint (free_vars (subst B v (mk_var y))) (vars_hyps J)
          # disjoint (free_vars B) (vars_hyps J)
          # !LIn x (free_vars B)
          # (y <> v -> !LIn y (free_vars B))

          # !LIn y (free_vars A)
          # !LIn y (free_vars C)
          # !LIn y (vars_hyps H)
          # !LIn y (vars_hyps J)
          # !LIn y (free_vars_hyps J)

          # !LIn z (free_vars A)
          # !LIn z (free_vars C)
          # !LIn z (free_vars e)
          # !LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # !LIn z (free_vars_hyps J)

          # !LIn x (free_vars A)
          # !LIn x (vars_hyps H)
          # !LIn x (vars_hyps J)

          # (x <> y)
          # (x <> z)
          # True) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (introv k; allunfold @disjoint; discover; auto));
    try (complete (discover; allrw in_app_iff; allrw in_snoc; sp));
    try (complete (introv i; discover; allrw in_snoc; sp; subst; sp;
                   allunfold @disjoint; discover; sp));
    try (complete (assert (LIn y (remove_nvars [v] (free_vars B)))
                    as k by (rw in_remove_nvars; rw in_single_iff; sp);
                   discover; sp));
    try (complete (assert (LIn x (remove_nvars [v] (free_vars B)))
                    as k by (rw in_remove_nvars; rw in_single_iff; sp);
                   discover; sp));
    try (complete (intros u k;
                   destruct (deq_nvar u v); subst; auto;
                   assert (LIn u (remove_nvars [v] (free_vars B)))
                     as q by (rw in_remove_nvars; rw in_single_iff; sp);
                   allunfold @disjoint; discover; sp));
    try (complete (assert (LIn z (free_vars (subst e y (mk_var x))))
                    by (pose proof (eqvars_free_vars_disjoint e [(y,mk_var x)]) as ev;
                        rw eqvars_prop in ev; apply ev; clear ev;
                        rw in_app_iff; simpl; rw in_remove_nvars; rw in_single_iff;
                        boolvar; simpl; sp);
                   discover;
                   allrw in_app_iff; allrw in_snoc; sp;
                   pose proof (subset_hs_vars_hyps H) as k1; unfold subset in k1;
                   pose proof (subset_hs_vars_hyps J) as k2; unfold subset in k2;
                   discover; sp)).

  destruct vhyps as [ daj     vhyps ].
  destruct vhyps as [ disjbj1 vhyps ].
  destruct vhyps as [ disjbj2 vhyps ].
  destruct vhyps as [ disjbj3 vhyps ].
  destruct vhyps as [ niyb    vhyps ].

  destruct vhyps as [ niya  vhyps ].
  destruct vhyps as [ niyc  vhyps ].
  destruct vhyps as [ niyh  vhyps ].
  destruct vhyps as [ niyj1 vhyps ].
  destruct vhyps as [ niyj2 vhyps ].

  destruct vhyps as [ niza  vhyps ].
  destruct vhyps as [ nizc  vhyps ].
  destruct vhyps as [ nizh  vhyps ].
  destruct vhyps as [ nizj1 vhyps ].
  destruct vhyps as [ nizj2 vhyps ].

  destruct vhyps as [ nixa  vhyps ].
  destruct vhyps as [ nixh  vhyps ].

  destruct vhyps as [ nexy  vhyps ].
  destruct vhyps as [ nexz  vhyps ].
  GC.
  (* done with proving these simple facts *)

  vr_seq_true.

  dup sim as simbackup.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

  lsubst_tac.

  duplicate sim2 as eis.
  apply equality_in_set in sim2; repnd.
  (*unfold inhabited_type in sim2; destruct sim2 as [t mem].*)

  (* ==== moving z ==== *)
  pose proof (rule_move_up_true2 lib
                true
                (subst B v (mk_var y))
                C e z
                (snoc (snoc H (mk_hyp x (mk_set A v B))) (mk_hyp y A))
                J []) as rt.
  pose proof (rule_move_down_wf
                true
                (subst B v (mk_var y))
                C e z
                (snoc (snoc H (mk_hyp x (mk_set A v B))) (mk_hyp y A))
                J []) as wf.
  autodimp rt hyp.
  autodimp wf hyp.
  autodimp wf hyp.
  unfold rule_true2 in rt; simpl in rt; allrw app_nil_r.
  autodimp rt hyp;
    [ unfold wf_rule, rule_move_down, wf_subgoals in wf; simpl in wf;
      allrw app_nil_r; autodimp wf hyp; repeat (split; simpl; auto);
      fail
    | ]; clear wf.
  autodimp rt hyp;[].
  autodimp rt hyp;
    [ introv k; dorn k; tcsp; subst; auto;
      exists (wfh0, (wfct, wfce0), (ct, ce)); auto
    | ].
  clear hyp1; rename rt into hyp1.
  (* ==== moved z ==== *)

  (* ==== moving y ==== *)
  rw (snoc_as_append _ J) in hyp1; rw app_assoc in hyp1.
  rw @mk_nlhyp_true in hyp1.
  destruct hyp1 as [wc hyp1].
  destruct wc as [ws cl]; simpl in cl.
  destruct cl as [cty cex].
  pose proof (rule_move_up_true2 lib
                false
                A
                C e y
                (snoc H (mk_hyp x (mk_set A v B)))
                J
                [mk_hhyp z (subst B v (mk_var y))]) as rt.
  pose proof (rule_move_down_wf
                false
                A
                C e y
                (snoc H (mk_hyp x (mk_set A v B)))
                J
                [mk_hhyp z (subst B v (mk_var y))]) as wf.
  autodimp rt hyp.
  autodimp wf hyp.
  autodimp wf hyp.
  unfold rule_true2 in rt; simpl in rt; allrw app_nil_r.
  autodimp rt hyp;
    [ unfold wf_rule, rule_move_down, wf_subgoals in wf; simpl in wf;
      autodimp wf hyp; split; simpl; auto
    | ]; clear wf.
  autodimp rt hyp;[].
  autodimp rt hyp;
    [ introv k; dorn k; tcsp; subst; auto;
      exists (ws, (cty, cex)); auto
     | ].
  clear hyp1; rename rt into hyp1.
  clear ws cty cex ce ct.
  rw <- snoc_as_append in hyp1.
  rw snoc_append_l in hyp1.
  destruct hyp1 as [ws hyp1].
  destruct ws as [ws cl];
    destruct cl as [ct ce];
    destruct ws as [wfhy wfc];
    destruct wfc as [wfT wfe].
  simpl in ct, ce, wfhy, wfT, wfe; PI.
  (* ==== moved y ==== *)


  apply if_in_open_bar_tequality_and_equality.
  eapply in_open_bar_pres; try exact sim2; clear sim2; introv xta sim2.
  assert (lib_extends lib'0 lib) as xtb by eauto 3 with slow.
  unfold inhabited_type in sim2; destruct sim2 as [t mem].


  vr_seq_true in hyp1.

  pose proof (hyp1
                _ xtb
                (snoc (snoc (snoc s1a0 (x,t1) ++ s1b) (y,t1)) (z,t))
                (snoc (snoc (snoc s2a0 (x,t2) ++ s2b) (y,t2)) (z,t)))
    as h; clear hyp1; rename h into hyp1.


  autodimp hyp1 hyp.


  (* ========== hyps_functionality ========== *)


  { introv xtc sim'.
    apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx.

    assert (cover_vars (subst B v (mk_var y)) s2a)
      as cv1
        by (eapply cover_vars_change_sub;[|eauto];
            allapply @similarity_dom; repnd; allrw; auto).

    apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; cpx.

    apply eq_hyps_snoc; simpl.
    exists (snoc (snoc s1a0 (x, t4) ++ s1b) (y, t4))
           (snoc s2a1 (y, t5))
           t0 t3 w0 p1 cv1; dands; auto.

    { assert (cover_vars A s2a1)
        as cv2
          by (eapply cover_vars_change_sub;[|eauto];
              allapply @similarity_dom; repnd; allrw; auto).

      apply eq_hyps_snoc; simpl.
      exists (snoc s1a0 (x, t4) ++ s1b) s2a1 t4 t5 w3 p2 cv2; dands; auto.

      { applydup eqh in sim'4 as eqh'; eauto 3 with slow. }

      applydup eqh in sim'4 as eqh'; eauto 3 with slow.
      apply eq_hyps_app in eqh'; exrepnd; subst; cpx.
      apply app_split in eqh'0; [|complete (rw length_snoc; allrw; auto)].
      repnd; subst; cpx.
      apply eq_hyps_snoc in eqh'5; simpl in eqh'5; exrepnd; cpx.
      lsubst_tac.
      apply tequality_set in eqh'0; repnd; auto. }

    assert (disjoint (free_vars (subst B v (mk_var y))) (dom_csub s1b))
      as disj
        by (allapply @similarity_dom; repnd;
            allrw @vars_hyps_substitute_hyps; allrw; auto).

    applydup eqh in sim'4 as eqh'; eauto 3 with slow.
    apply eq_hyps_app in eqh'; exrepnd; subst; cpx.
    apply app_split in eqh'0; [|complete (rw length_snoc; allrw; auto)].
    repnd; subst; cpx.
    apply eq_hyps_snoc in eqh'5; simpl in eqh'5; exrepnd; cpx.
    lsubst_tac.
    apply tequality_set in eqh'0; repnd; auto.
    apply eqh'0 in sim'2; eauto 3 with slow.
    substc_lsubstc_vars2;[complete(allapply @similarity_dom; repnd; allrw; auto)|].
    substc_lsubstc_vars2;[complete(allapply @eq_hyps_dom; repnd; allrw; auto)|].

    pose proof (lsubstc_subst_snoc_eq_ex (snoc s1a (x, t1) ++ s1b0) B v y t1 w0 p1) as h.
    repeat (autodimp h hyp);
      [ rw @dom_csub_app; repeat (rw @dom_csub_snoc); simpl; rw in_app_iff; rw in_snoc;
        allapply @similarity_dom; repnd; allrw;
        rw @vars_hyps_substitute_hyps; sp
      | ].
    exrepnd.
    rw h1; clear h1.
    repeat substc_lsubstc_vars3.

    pose proof (lsubstc_subst_snoc_eq_ex (snoc s2a1 (x, t6) ++ s2b0) B v y t5 w0 cv1) as h.
    repeat (autodimp h hyp);
      [ rw @dom_csub_app; repeat (rw @dom_csub_snoc); simpl; rw in_app_iff; rw in_snoc;
        allapply @eq_hyps_dom; allapply @sub_eq_hyps_dom; repnd; allrw; sp
      | ].
    exrepnd.
    rw h1; clear h1.
    repeat substc_lsubstc_vars3.

    revert c7 c10; repeat (rw app_comm_cons); introv.
    lsubst_tac.

    revert c11 c12; repeat (rw cons_snoc); introv.
    lsubst_tac.

    pose proof (lsubstc_snoc_app_move_to_last B [] s1a v t1 w2 c8) as h; simpl in h.
    autodimp h hyp; [allapply @eq_hyps_dom; repnd; allrw; auto|].
    exrepnd; PI; rw h0; clear h0.

    pose proof (lsubstc_snoc_app_move_to_last B [] s2a1 v t5 w2 c13) as h; simpl in h.
    autodimp h hyp; [allapply @eq_hyps_dom; repnd; allrw; auto|].
    exrepnd; PI; rw h0; clear h0.
    auto. }


  (* ========== similarity ========== *)


  autodimp hyp1 hyp.

  { assert (wf_term (subst B v (mk_var y)))
      as wsb
        by (apply lsubst_preserves_wf_term; auto;
            unfold wf_sub, sub_range_sat; simpl; sp; cpx).

    assert (cover_vars (subst B v (mk_var y))
                       (snoc (snoc s1a0 (x, t1) ++ s1b) (y, t1))) as cvsb.
    { destseq; allsimpl; dwfseq.
      allunfold @cover_vars_upto; allsimpl.
      rw @cover_vars_eq; rw subvars_prop; introv h.
      pose proof (eqvars_free_vars_disjoint B [(v,mk_var y)]) as ev.
      fold (subst B v (mk_var y)) in ev.
      eapply eqvars_prop in ev; apply ev in h; clear ev; simpl in h.
      rw in_app_iff in h.
      rw @dom_csub_snoc; rw @dom_csub_app; rw @dom_csub_snoc; simpl.
      rw in_snoc; rw in_app_iff; rw in_snoc.
      allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps.
      dorn h; discover; sp.
      revert h; boolvar; intro h; simpl in h; sp. }

    apply similarity_snoc; simpl.
    exists (snoc (snoc s1a0 (x, t1) ++ s1b) (y, t1))
           (snoc (snoc s2a0 (x, t2) ++ s2b) (y, t2))
           t t wsb cvsb; dands; auto.

    { assert (cover_vars A (snoc s1a0 (x, t1) ++ s1b))
        as cva by (apply cover_vars_app_weak; apply cover_vars_snoc_weak; auto).

      apply similarity_snoc; simpl.
      exists (snoc s1a0 (x, t1) ++ s1b)
             (snoc s2a0 (x, t2) ++ s2b)
             t1 t2 w1 cva; dands; auto; eauto 3 with slow.
      lsubst_tac; auto; eauto 3 with slow. }

    substc_lsubstc_vars2;[complete(allapply @similarity_dom; repnd; allrw; auto)|].

    pose proof (lsubstc_subst_snoc_eq_ex (snoc s1a0 (x, t1) ++ s1b) B v y t1 wsb cvsb) as h.
    repeat (autodimp h hyp);
      [ rw @dom_csub_app; repeat (rw @dom_csub_snoc); simpl; rw in_app_iff; rw in_snoc;
        allapply @similarity_dom; repnd; allrw;
        rw @vars_hyps_substitute_hyps; sp
      | ].
    exrepnd.
    rw h1; clear h1.
    repeat substc_lsubstc_vars3.

    revert c3; rw app_comm_cons; introv.
    lsubst_tac.

    revert c4; rw cons_snoc; introv.
    lsubst_tac.

    pose proof (lsubstc_snoc_app_move_to_last B [] s1a0 v t1 w2 c5) as h; simpl in h.
    autodimp h hyp; [allapply @similarity_dom; repnd; allrw; auto|].
    exrepnd; PI; rw h0; clear h0; auto. }


  (* ========== now we use hyp1 ========== *)


  exrepnd.
  lsubst_tac.
  dands; auto.

  pose proof (lsubstc_snoc_app_move_to_last
                (subst e y (mk_var x)) s1a0 s1b x t1 wfce pt1) as h; simpl in h.
  autodimp h hyp;[allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; auto|].
  exrepnd; rw h0; clear h0.

  pose proof (lsubstc_snoc_app_move_to_last
                (subst e y (mk_var x)) s2a0 s2b x t2 wfce pt2) as h; simpl in h.
  autodimp h hyp;[allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; auto|].
  exrepnd; rw h0; clear h0.

  pose proof (lsubstc_subst_snoc_eq2_ex (s1a0 ++ s1b) e y x t1 wfce c') as h;
    repeat (autodimp h hyp);
    try (complete (rw @dom_csub_app; rw in_app_iff;
                   allapply @similarity_dom; repnd; allrw;
                   rw @vars_hyps_substitute_hyps; sp)).
  exrepnd; rw h1; clear h1.

  pose proof (lsubstc_subst_snoc_eq2_ex (s2a0 ++ s2b) e y x t2 wfce c'0) as h;
    repeat (autodimp h hyp);
    try (complete (rw @dom_csub_app; rw in_app_iff;
                   allapply @similarity_dom; repnd; allrw;
                   rw @vars_hyps_substitute_hyps; sp)).
  exrepnd; rw h1; clear h1.

  PI.

  revert c5.
  rw <- snoc_append_l; introv.

  pose proof (lsubstc_snoc_app_move_down2
                e s1a0 (snoc s1b (y, t1)) [] x t1 wfce0) as h.
  rw app_nil_r in h.
  pose proof (h c5) as k; clear h.
  autodimp k hyp;
    [ rw @dom_csub_snoc; simpl; rw in_snoc;
      allapply @similarity_dom; repnd; allrw;
      rw @vars_hyps_substitute_hyps; sp
    | ].
  exrepnd; rw k0; clear k0.

  revert c6.
  rw <- snoc_append_l; introv.

  pose proof (lsubstc_snoc_app_move_down2
                e s2a0 (snoc s2b (y, t2)) [] x t2 wfce0) as h.
  rw app_nil_r in h.
  pose proof (h c6) as k; clear h.
  autodimp k hyp;
    [ rw @dom_csub_snoc; simpl; rw in_snoc;
      allapply @similarity_dom; repnd; allrw;
      rw @vars_hyps_substitute_hyps; sp
    | ].
  exrepnd; rw k0; clear k0.

  revert c'1 c'2.
  allrw app_nil_r; introv.

  revert c c0 hyp1.
  repeat (rw <- snoc_append_l); introv h; PI; auto.
Qed.

Lemma rule_set_elimination_true_nobc {p} :
  forall lib (A B C e : NTerm)
         (v x y z : NVar)
         (H J : @barehypotheses p),
    rule_true lib (rule_set_elimination
                 A B C e
                 v x y z
                 H J).
Proof.
  introv.
  unfold rule_set_elimination.
  pose proof (rule_set_elimination_true lib A B C e v x y z H J) as h.

Abort.



(**

  The following rule is called the set equality rule.  It says
  that to prove that a set type is well-formed, we have to prove
  that its domain is well-formed and that its co-domain is functional
  over its domain.
<<
   H |- {x1:a1|b1} = {x2:a2|b2} in Type(i)

     By setEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_set_equality {p}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_set a1 x1 b1)
                      (mk_set a2 x2 b2)
                      (mk_uni i))))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality a1 a2 (mk_uni i))),
      mk_baresequent
        (snoc H (mk_hyp y a1))
        (mk_conclax (mk_equality
                       (subst b1 x1 (mk_var y))
                       (subst b2 x2 (mk_var y))
                       (mk_uni i)))
    ]
    [ sarg_var y ].

Lemma rule_set_equality_true {pp} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses pp,
    rule_true lib (rule_set_equality
                     a1 a2 b1 b2
                     x1 x2 y
                     i
                     H).
Proof.
  intros.
  apply (rule_tyfam_equality_true _ _ mkc_set); auto.

  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.

  - introv; apply lsubstc_mk_set_ex.

  - introv xta; apply equality_set.
Qed.

(* begin hide *)

Lemma rule_set_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H,
    @rule_true_if o lib (rule_set_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_set_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.


Lemma sim_cons2 {o} :
  forall (lib : library) (t1 t2 : @CTerm o)
         (s1 s2 : CSubstitution) (h : hypothesis) (hs : barehypotheses)
         (w : wf_term (htyp h)) (p : cover_vars (htyp h) s1) v,
    equality lib t1 t2 (lsubstc (htyp h) w s1 p)
    -> similarity lib s1 s2 hs
    -> v = hvar h
    -> similarity lib (snoc s1 (v, t1)) (snoc s2 (v, t2)) (snoc hs h).
Proof.
  intros; subst.
  eapply sim_cons; eauto.
Qed.


(* end hide *)

(**

<<
   H |- {x:A|B} ext a

     By dependent_set_memberFormation lvl(i) z ()

     H |- a in A
     H |- B[x\a]
     H z : A |- B[x\z] in Type(i)
>>

 *)

Definition rule_dependent_set_member_formation {p}
           (A B a e : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_set A x B) a))
    [ mk_baresequent H (mk_concl A a),
      mk_baresequent H (mk_concl (subst B x a) e),
      mk_baresequent (snoc H (mk_hyp z A))
                     (mk_conclax (mk_member (subst B x (mk_var z)) (mk_uni i)))
    ]
    [sarg_var z].

Lemma rule_dependent_set_member_formation_true {p} :
  forall lib (A B a e : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses p)
         (bc1 : !LIn z (bound_vars B))
         (bc2 : disjoint (nh_vars_hyps H) (bound_vars B)),
    rule_true lib (rule_dependent_set_member_formation A B a e x z i H).
Proof.
  intros.
  unfold rule_dependent_set_member_formation, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  rename Hyp1 into hyp3.
  destruct hyp1 as [wc1 hyp1].
  destruct hyp2 as [wc2 hyp2].
  destruct hyp3 as [wc3 hyp3].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists ce1; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.
  sp;
    try (complete (pose proof (cg z) as h; sp; allrw in_remove_nvars; allsimpl;
                   autodimp h hyp; sp)).

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  prove_and teq.

  - lsubst_tac.
    apply tequality_set.

    prove_and teqa.

    + vr_seq_true in hyp1.
      pose proof (hyp1 _ ext s1 s2 eqh sim) as h; clear hyp1.
      exrepnd; proof_irr; auto.

    + introv xta eqa.
      repeat substc_lsubstc_vars3.

      assert (lib_extends lib'0 lib) as xtb by eauto 3 with slow.
      vr_seq_true in hyp3.
      pose proof (hyp3 _ xtb (snoc s1 (z,a0)) (snoc s2 (z,a'))) as h; clear hyp3.

      repeat (autodimp h hyp).

      * introv xtc.
        apply hyps_functionality_snoc2; simpl; auto; eauto 3 with slow;[].
        introv ea sim'.
        vr_seq_true in hyp1.
        assert (lib_extends lib'1 lib) as xtd by eauto 3 with slow.
        assert (lib_extends lib'1 lib') as xte by eauto 3 with slow.
        eapply lib_extends_preserves_hyps_functionality_ext in eqh; try exact xte.
        pose proof (hyp1 _ xtd s1 s' eqh sim') as h; clear hyp1.
        exrepnd; proof_irr; auto.

      * eapply sim_cons2; simpl; eauto; eauto 3 with slow.

      * exrepnd.
        lsubst_tac.
        apply member_member_iff in h1.
        apply tequality_mkc_member_sp in h0; repnd.

        assert (!LIn z (dom_csub s1))
          as nizs1 by (allapply @similarity_dom; repnd; allrw; auto).

        assert (!LIn z (dom_csub s2))
          as nizs2 by (allapply @similarity_dom; repnd; allrw; auto).

        pose proof (lsubstc_subst_snoc_eq_ex s1 B x z a0 wt ct2) as e1.
        repeat (autodimp e1 hyp).
        exrepnd; proof_irr; GC.

        rw e1 in h0.
        rw e1 in h1.
        clear e1.

        pose proof (lsubstc_subst_snoc_eq_ex s2 B x z a' wt ct3) as e1.
        repeat (autodimp e1 hyp).
        exrepnd; proof_irr; GC.

        rw e1 in h0.
        clear e1.

        repeat substc_lsubstc_vars3.
        proof_irr.

        eapply all_in_ex_bar_tequality_implies_tequality.
        eapply in_open_bar_pres; try exact h0; clear h0; introv xtf h0.

        dorn h0.

        { apply equality_in_uni in h0; auto. }

        { spcast.
          apply ccequivc_ext_sym in h0.
          rwg h0.
          apply equality_in_uni in h1; auto; eauto 3 with slow. }

  - lsubst_tac.
    apply tequality_set in teq; repnd.
    apply equality_in_set; dands; auto.

    + introv xta eqa.
      repeat substc_lsubstc_vars3.
      applydup teq in eqa; eauto 3 with slow.
      applydup @equality_sym in eqa.
      apply equality_refl in eqa1.
      apply teq in eqa1; eauto 3 with slow.
      repeat substc_lsubstc_vars3.
      proof_irr.
      eapply tequality_trans; eauto.
      apply tequality_sym; auto.

    + vr_seq_true in hyp1.
      pose proof (hyp1 _ ext s1 s2 eqh sim) as h; clear hyp1.
      exrepnd; proof_irr; auto.

    + repeat substc_lsubstc_vars3.
      vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 eqh sim) as h; clear hyp2.
      exrepnd; proof_irr.

      assert (disjoint (free_vars a) (bound_vars B)) as disj.
      { unfold covered in ce1.
        eapply subvars_disjoint_l;[exact ce1|]; auto. }

      repeat substc_lsubstc_vars3.
      proof_irr.
      apply equality_implies_all_in_ex_bar_equality in h1.
      eapply in_open_bar_pres; try exact h1; clear h1; introv xta h1.
      apply equality_refl in h1.
      eexists; eauto.
Qed.
