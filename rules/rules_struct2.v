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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_equality.


Lemma lsubstc_eq_nil {o} :
  forall (t : @NTerm o) w s c c',
    lsubstc t w s c = lsubstc t w [] c'.
Proof.
  introv.
  apply cterm_eq; simpl.
  rewrite csubst_nil.
  rewrite csubst_trivial; auto.
  rw @cover_vars_eq in c'; simpl in c'.
  rw subvars_eq in c'.
  introv i j; apply c' in j; simpl in j; tcsp.
Qed.

(*
   H |- C ext t

     By closedConclusion

     |- C ext t
 *)
Definition rule_closed_conclusion {o}
           (H : @bhyps o)
           (C t : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_concl C t))
    [
      mk_baresequent [] (mk_concl C t)
    ]
    [].

Lemma rule_closed_conclusion_true3 {o} :
  forall lib (H : @bhyps o) C t,
    rule_true3 lib (rule_closed_conclusion H C t).
Proof.
  intros.
  unfold rule_closed_conclusion, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv i; tcsp.
    apply ce in i; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 [] []) as h; clear hyp1; exrepnd.
  repeat (autodimp h hyp); try (apply sim_nil);[].
  exrepnd.
  lsubst_tac.
  proof_irr.
  rewrite (lsubstc_eq_nil _ _ s1 _ pC0).
  rewrite (lsubstc_eq_nil _ _ s2 _ pC0).
  rewrite (lsubstc_eq_nil _ _ s1 _ pt0).
  rewrite (lsubstc_eq_nil _ _ s2 _ pt0).
  auto.
Qed.


(* [13] ============ WIDENING ============ *)

(**

  The following rule state that if we are trying to prove a goal under
  the assumption that [x] has type [T], then it suffices to prove the
  goal under the hypothesis that [x] has type [U], as long as we can
  prove that [T] is a subtype of [U], and [T] respects the equality of
  [U] on the elements of [T]:

<<
  H, x : T, J |- C ext t

     By widening y z i

     H, x : U, J |- C ext t
     H, x : T, y : U, z : x = y in U |- x = y in T
     H, x : T |- x in U
>>
 *)

Definition rule_widening {o}
           (T U C t : @NTerm o)
           (x y z : NVar)
           (i : nat)
           (H J : barehypotheses) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x T) ++ J)
       (mk_concl C t))
    [ mk_baresequent (snoc H (mk_hyp x U) ++ J)
                    (mk_concl C t),
      mk_baresequent (snoc (snoc (snoc H (mk_hyp x T))
                                (mk_hyp y U))
                          (mk_hyp z (mk_equality (mk_var x) (mk_var y) U)))
                    (mk_conclax (mk_equality (mk_var x) (mk_var y) T)),
      mk_baresequent (snoc H (mk_hyp x T))
                    (mk_conclax (mk_member (mk_var x) U))
    ]
    [sarg_var y, sarg_var z].

Lemma rule_widening_true {o} :
  forall lib (T U C t : NTerm)
         (x y z : NVar)
         (i : nat)
         (H J : @barehypotheses o),
    rule_true lib
              (rule_widening
                 T U C t
                 x y z
                 i
                 H J).
Proof.
  unfold rule_widening, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc H (mk_hyp x U) ++ J)
                      (mk_concl C t))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc (snoc (snoc H (mk_hyp x T)) (mk_hyp y U))
                            (mk_hyp z (mk_equality (mk_var x) (mk_var y) U)))
                      (mk_conclax (mk_equality (mk_var x) (mk_var y) T)))
                   (inr (inl eq_refl)))
             (hyps (mk_baresequent
                      (snoc H (mk_hyp x T))
                      (mk_conclax (mk_member (mk_var x) U)))
                   (inr (inr (inl eq_refl))));
    simpl; intros hyp1 hyp2 hyp3.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destruct hyp3 as [ ws3 hyp3 ].
  destseq; allsimpl; proof_irr; GC.
  clear hyps.

  assert (covered t (nh_vars_hyps (snoc H (mk_hyp x T) ++ J)))
    as co
      by (duplicate ce1 as ce2;
          allrw @nh_vars_hyps_app;
          allrw @nh_vars_hyps_snoc;
          allsimpl; sp).

  exists co; GC.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
           # !LIn x (free_vars T)
           # !LIn x (free_vars U)
           # !(x = y)
           # !LIn y (vars_hyps H)
           # !LIn y (free_vars T)
           # !LIn y (free_vars U)
           # !LIn z (vars_hyps H)
           # !LIn z (free_vars T)
           # !LIn z (free_vars U)
           # wf_term U
           # covered T (vars_hyps H)
           # covered U (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.

  sp; try (complete (unfold covered; rw subvars_prop; sp)).

  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nixT vhyps ].
  destruct vhyps as [ nixU vhyps ].
  destruct vhyps as [ nixy vhyps ].
  destruct vhyps as [ niyH vhyps ].
  destruct vhyps as [ niyT vhyps ].
  destruct vhyps as [ niyU vhyps ].
  destruct vhyps as [ nizH vhyps ].
  destruct vhyps as [ nizT vhyps ].
  destruct vhyps as [ nizU vhyps ].
  destruct vhyps as [ wfu vhyps ].
  destruct vhyps as [ covTH covUH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  (* we split s1 and s2 *)
  allrw @similarity_app; exrepd; subst; cpx.
  allrw @similarity_snoc; exrepd; subst; cpx.
  allsimpl.

  (* we use our 1st subgoal to prove that tequality *)
  vr_seq_true in hyp1.

  generalize (hyp1 (snoc s1a0 (x, t1) ++ s1b)
                   (snoc s2a0 (x, t2) ++ s2b));
    clear hyp1; intro hyp1.

  autodimp hyp1 h.

  introv sim.
  allrw @similarity_app; exrepd; subst; allsimpl; cpx.
  apply app_split in e; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  repeat (allrw @similarity_snoc; exrepd; subst; allsimpl; cpx; GC).

  rw @eq_hyps_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t3)) s2b0;
    allrw length_snoc; allrw; sp.

  assert (cover_vars U s2a1)
         as c2
         by (apply @cover_vars_dom_csub_eq with (s1 := s1a); sp;
             allrw @dom_csub_snoc; simpl;
             allapply @similarity_dom; repd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a s2a1 t0 t3 w0 p0 c2; sp.

  generalize (eqh (snoc s2a1 (x, t2) ++ s2b)); intro imp.
  autodimp imp hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t2)) s2b; repeat (rw length_snoc); sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t2 w p; sp.

  rw @eq_hyps_app in imp; exrepnd.
  apply app_split in imp0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in imp2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  rw @eq_hyps_snoc in imp5; exrepnd; sp; cpx.

  generalize (eqh (snoc s2a1 (x, t2) ++ s2b)); intro imp.
  autodimp imp hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t2)) s2b; repeat (rw length_snoc); sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t2 w p; sp.

  rw @eq_hyps_app in imp; exrepnd.
  apply app_split in imp0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in imp2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  rw @eq_hyps_snoc in imp5; exrepnd; sp; cpx; allsimpl; cpx; clear_irr.

  (* from imp0 and sequent 3 *)
  generalize (subtype_tequality lib s1a0 s2a H T U x t1 t4 w w0 p1 p0 c2 (wfh0, (wfct0, wfce1), (ct, ce)));
    intro j; repeat (autodimp j hyp).
  apply hyps_functionality_init_seg with (s3 := s2b1) in eqh; sp.

  assert (cover_vars T s2a1)
    as c2
      by (apply @cover_vars_dom_csub_eq with (s1 := s1a); sp;
          allrw @dom_csub_snoc; simpl;
          allapply @similarity_dom; repd; allrw; sp).

  generalize (eqh (snoc s2a1 (x, t3) ++ s2b0)); intro j; autodimp j hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t3)) s2b0; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t3 w p; sp.

  generalize (strong_subtype_equality lib s1a s2a1 t0 t2 t3 T U w w0 p p0 c2 H x y z
                                      (wfh0, (wfct0, wfce1), (ct, ce))
                                      (wfh1, (wfct1, wfce1), (ct0, ce0)));
    intro q; repeat (destimp q hyp).
  repnd.
  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.
  apply @equality_commutes4 with (U := lsubstc T w s2a1 c2) (a2 := t0) (a3 := t2); sp.

  rw @eq_hyps_app in j; exrepnd.
  apply app_split in j0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in j2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.

  (* we're done proving the hyps_functionality part for sequent 1 *)

  (* we now have to prove the similarity part *)

  autodimp hyp1 h.

  rw @similarity_app; simpl.
  exists (snoc s1a0 (x, t1)) s1b (snoc s2a0 (x, t2)) s2b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.

  assert (cover_vars U s1a0)
    as c1 by (allrw @cover_vars_covered; allapply @similarity_dom; exrepnd; allrw; sp).

  exists s1a0 s2a0 t1 t2 wfu c1; sp.

  generalize (subtype_equality lib t1 t2 T U  s1a0 s2a0 w wfu p c1 H x
                               (wfh0, (wfct0, wfce1), (ct, ce)));
    intro j; repeat (autodimp j hyp).
  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.

  exrepnd; clear_irr; sp.
Qed.
