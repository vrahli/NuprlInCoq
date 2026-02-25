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


Require Import rules_useful.
Require Import sequents_useful.
Require Import sequents_equality.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)

(* [15] ============ FUNCTIONALITY ============ *)

(* we need [x : Base] to be hidden because in the main sequent
   we get two substitutions x -> t1 and x -> t2 such that
   t1 = t2 in A, but in the second sequent we get
   t1 = t2 in Base.
*)

(**

  This is the functionality rule that exposes the functionality part
  of the meaning of sequents:
<<
   G, x : A, J |- C ext t

     By functionality y z

     G, [x : Base], [z : x in A], J |- C ext t
     G, x : Base, y : Base, z : x = y in A, J |- C = C[x\y]
>>
*)

Definition rule_functionality {p}
           (G J   : @barehypotheses p)
           (A C t : NTerm)
           (x y z : NVar)
           (i     : nat) :=
  mk_rule
    (mk_baresequent (snoc G (mk_hyp x A) ++ J) (mk_concl C t))
    [ mk_baresequent
        (snoc (snoc G (mk_hhyp x mk_base))
              (mk_hhyp z (mk_member (mk_var x) A))
              ++ J)
        (mk_concl C t),
      mk_baresequent
        (snoc (snoc (snoc G (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_equality (mk_var x) (mk_var y) A))
              ++ J)
        (mk_conclax (mk_equality C (subst C x (mk_var y)) (mk_uni i)))
    ]
    [].

Lemma rule_functionaliy_true {pp} :
  forall lib (G J   : @barehypotheses pp)
         (A C t : NTerm)
         (x y z : NVar)
         (i     : nat)
         (bc    : !LIn y (bound_vars C)),
    rule_true lib (rule_functionality G J A C t x y z i).
Proof.
  unfold rule_functionality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc (snoc G (mk_hhyp x mk_base))
                            (mk_hhyp z (mk_member (mk_var x) A)) ++ J)
                      (mk_concl C t))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc (snoc (snoc G (mk_hyp x mk_base)) (mk_hyp y mk_base))
                            (mk_hyp z (mk_equality (mk_var x) (mk_var y) A)) ++ J)
                      (mk_conclax (mk_equality C (subst C x (mk_var y)) (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.

  assert (covered t (nh_vars_hyps (snoc G (mk_hyp x A) ++ J))) as cv.
  clear hyp1 hyp2.
  dwfseq.
  introv j.
  discover.
  allrw in_app_iff; allrw in_snoc; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps G)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps G)
          # !LIn y (vars_hyps J)
          # !LIn z (vars_hyps G)
          # !LIn z (vars_hyps J)
          # !LIn x (free_vars A)
          # !LIn y (free_vars A)
          # !LIn y (free_vars C)
          # !LIn z (free_vars C)
          # !LIn x (free_vars t)
          # !LIn y (free_vars t)
          # !LIn z (free_vars t)
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
  destruct vhyps as [ niyC vhyps ].
  destruct vhyps as [ nizC vhyps ].
  destruct vhyps as [ nixt vhyps ].
  destruct vhyps as [ niyt vhyps ].
  destruct vhyps as [ nizt vhyps ].
  destruct vhyps as [ niyJ2 vhyps ].
  destruct vhyps as [ nizJ2 vhyps ].
  destruct vhyps as [ niyJ3 vhyps ].
  destruct vhyps as [ nizJ3 vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxz nyz ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; exrepnd; subst; allsimpl; cpx.

  dands.

  - vr_seq_true in hyp2.

    generalize (hyp2
                  (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s1b)
                  (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s2b));
      clear hyp2; intro hyp2.

    (* First we prove the hyps_functionality part of hyp2 *)
    autodimp hyp2 hyp.
    introv simil.
    rw @similarity_app in simil; exrepnd; subst; cpx.
    apply app_split in simil0; simpl; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    rw @similarity_snoc in simil5; exrepnd; subst; allsimpl; cpx.
    rw @similarity_snoc in simil5; exrepnd; subst; allsimpl; cpx.
    rw @similarity_snoc in simil6; exrepnd; subst; allsimpl; cpx.
    lsubst_tac.
    allrw @equality_in_base_iff.
    allrw @equality_in_mkc_equality; repnd.
    spcast.

    rewrite substitute_hyps_snoc_sub_weak in simil1; try (complete sp).
    rewrite substitute_hyps_snoc_sub_weak in simil1; try (complete sp).

    duplicate eqh as eqh'.
    apply hyps_functionality_init_seg with (s3 := s2b0) in eqh; try (complete sp).
    generalize (@hyps_functionality_init_seg_snoc2 pp lib s1a t2 t0 G x A w p eqh);
      intro hf; autodimp hf hyp.

    rw @eq_hyps_app.
    exists (snoc (snoc (snoc s1a (x, t2)) (y, t0)) (z, mkc_axiom))
           s1b0
           (snoc (snoc (snoc s2a1 (x, t5)) (y, t4)) (z, t3))
           s2b0;
      allrw length_snoc; dands; try (complete sp).

    assert (cover_vars (mk_equality (mk_var x) (mk_var y) A)
                       (snoc (snoc s2a1 (x, t5)) (y, t4)))
           as cv2
           by (apply cover_vars_change_sub with (sub1 := snoc (snoc s1a (x, t2)) (y, t0)); sp;
               allrw @dom_csub_snoc; simpl; sp;
               apply @similarity_dom in simil7; repnd; allrw; sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc (snoc s1a (x, t2)) (y, t0))
           (snoc (snoc s2a1 (x, t5)) (y, t4))
           (@mkc_axiom pp)
           t3
           w0
           p0
           cv2; dands; try (complete sp).

    assert (cover_vars mk_base (snoc s2a1 (x, t5))) as cv3 by (apply cover_vars_base).

    rw @eq_hyps_snoc; simpl.
    exists (snoc s1a (x, t2)) (snoc s2a1 (x, t5)) t0 t4 w1 p1 cv3;
      dands;
      try (complete sp);
      try (complete (lsubst_tac; apply tequality_base)).

    assert (cover_vars mk_base s2a1) as cv4 by (apply cover_vars_base).

    rw @eq_hyps_snoc; simpl.
    exists s1a s2a1 t2 t5 w1 p2 cv4;
      dands;
      try (complete sp);
      try (complete (lsubst_tac; apply tequality_base)).
   (* end of the eq_hyps proof *)

   (* tequality it will follow from squiggle equality*)
    lsubst_tac; GC.
    assert (tequality lib (lsubstc A w s1a p) (lsubstc A w s2a1 c7))
           as teq
           by (generalize (eqh (snoc s2a1 (x,t0))); intro imp;
               autodimp imp hyp;
               try (rw @similarity_snoc; simpl);
               try (exists s1a s2a1 t2 t0 w p; sp);
               rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx; proof_irr; sp).
    apply @tequality_equality_if_cequivc; dands; try (complete sp); sp.
    { (* sub_eq_hyps *)
    apply sub_eq_hyps_snoc_weak; sp.
    apply sub_eq_hyps_snoc_weak; sp.

    generalize (eqh' (snoc s2a1 (x,t5) ++ s2b0)); intro imp.
    autodimp imp hyp.
    rw @similarity_app.
    exists (snoc s1a (x, t2)) s1b0 (snoc s2a1 (x, t5)) s2b0; allrw length_snoc; sp.
    rw @similarity_snoc; simpl.
    exists s1a s2a1 t2 t5 w p; sp.
    apply @equality_respects_cequivc_right with (t2 := t2); sp.
    allapply @equality_refl; sp.
    rw @eq_hyps_app in imp; exrepnd.
    apply app_split in imp0; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    apply app_split in imp2; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
   }
  


    (* Now we prove the similarity part of hyp2 *)
    autodimp hyp2 hyp.
    rw @similarity_app; simpl.
    exists (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s1b
           (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s2b;
      allrw length_snoc; sp.

    assert (wf_term (mk_equality (mk_var x) (mk_var y) A))
           as wfeq by (rw <- @wf_equality_iff; sp).

    assert (cover_vars (mk_equality (mk_var x) (mk_var y) A)
                       (snoc (snoc s1a0 (x, t1)) (y, t2)))
           as cv1
           by (rw @cover_vars_equality; sp; try (apply cover_vars_var; sp);
               allrw @dom_csub_snoc; simpl; allrw in_snoc; sp;
               repeat (apply cover_vars_snoc_weak); sp).

    rw @similarity_snoc; simpl.
    exists (snoc (snoc s1a0 (x, t1)) (y, t2))
           (snoc (snoc s2a0 (x, t1)) (y, t2))
           (@mkc_axiom pp) (@mkc_axiom pp)
           wfeq cv1; sp.

    rw @similarity_snoc; simpl.
    exists (snoc s1a0 (x, t1)) (snoc s2a0 (x, t1)) t2 t2
           (@wf_base pp) (cover_vars_base (snoc s1a0 (x, t1))); sp.

    rw @similarity_snoc; simpl.
    exists s1a0 s2a0 t1 t1 (@wf_base pp) (cover_vars_base s1a0); sp.

    lsubst_tac; apply member_base.

    lsubst_tac; apply member_base.

    lsubst_tac; rw @member_eq; rw <- @member_equality_iff; sp.

    rewrite substitute_hyps_snoc_sub_weak; sp.
    rewrite substitute_hyps_snoc_sub_weak; sp.


    (* Now that we've proved hyps_functionality and similarity, we can use hyp2 *)
    exrepnd; lsubst_tac; proof_irr; GC.

    assert (cover_vars C (snoc s1a0 (x, t2) ++ s1b))
           as pC5
           by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (x, t1) ++ s1b); sp;
               allrw @dom_csub_app; allrw @dom_csub_snoc; simpl;
               allapply @similarity_dom; repnd; allrw; sp).

    assert (cover_vars C (snoc s2a0 (x, t1) ++ s2b))
           as pC6
           by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (x, t1) ++ s1b); sp;
               allrw @dom_csub_app; allrw @dom_csub_snoc; simpl;
               allapply @similarity_dom; repnd; allrw; sp).

    assert (cover_vars C (snoc s2a0 (x, t2) ++ s2b))
           as pC7
           by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (x, t1) ++ s1b); sp;
               allrw @dom_csub_app; allrw @dom_csub_snoc; simpl;
               allapply @similarity_dom; repnd; allrw; sp).

    assert (lsubstc C wfct
                    (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s1b)
                    c1
            = lsubstc C wfct (snoc s1a0 (x, t1) ++ s1b) pC1)
           as eqc1
           by (generalize (lsubstc_csubst_ex2 C (snoc s1a0 (x, t1)) s1b wfct pC1);
               intro eq; exrepnd; rw <- eq1; clear eq1;
               generalize (lsubstc_csubst_ex2 C (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s1b wfct c1);
               intro eq; exrepnd; rw <- eq1; clear eq1;
               revert w'0 p'0;
               rewrite subset_free_vars_csub_snoc; auto;
               rewrite subset_free_vars_csub_snoc; auto; intros;
               apply lsubstc_eq; auto).
    rw eqc1 in hyp0; rw eqc1 in hyp2.

    assert (lsubstc C wfct
                    (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s2b)
                    c0
            = lsubstc C wfct (snoc s2a0 (x, t1) ++ s2b) pC6)
           as eqc2
           by (generalize (lsubstc_csubst_ex2 C (snoc s2a0 (x, t1)) s2b wfct pC6);
               intro eq; exrepnd; rw <- eq1; clear eq1;
               generalize (lsubstc_csubst_ex2 C (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s2b wfct c0);
               intro eq; exrepnd; rw <- eq1; clear eq1;
               revert w'0 p'0;
               rewrite subset_free_vars_csub_snoc; auto;
               rewrite subset_free_vars_csub_snoc; auto; intros;
               apply lsubstc_eq; auto).
    rw eqc2 in hyp0.

    assert (lsubstc (subst C x (mk_var y)) w2
                    (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s1b)
                    c2
            = lsubstc C wfct (snoc s1a0 (x, t2) ++ s1b) pC5)
           as eqc3.
    (* begin proof of assert *)
    generalize (lsubstc_csubst_ex2 C (snoc s1a0 (x, t2)) s1b wfct pC5);
      intro eq; exrepnd; rw <- eq1; clear eq1;
      generalize (lsubstc_csubst_ex2 (subst C x (mk_var y)) (snoc (snoc (snoc s1a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s1b w2 c2);
      intro eq; exrepnd; rw <- eq1; clear eq1;
      apply lsubstc_eq; try (complete sp);
      rewrite subset_free_vars_csub_snoc; auto;
      try (complete (generalize (eqvars_free_vars_disjoint C [(x, mk_var y)]); intro eqv;
                     rw eqvars_prop in eqv; rw eqv; rw in_app_iff; rw in_remove_nvars; simpl;
                     boolvar; simpl; sp)).
    rw @csubst_subst_snoc_eq2;
      try (complete sp);
      try (complete (rw @dom_csub_snoc; simpl; rw in_snoc;
                     allapply @similarity_dom; repnd; allrw; sp)).
    rw @csub_filter_snoc1.
    rw @csub_filter_trivial; sp.
    rw disjoint_singleton_l; allapply @similarity_dom; repnd; allrw; sp.
    (* end proof of assert *)
    rw eqc3 in hyp0; rw eqc3 in hyp2.

    assert (lsubstc (subst C x (mk_var y)) w2
                    (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom) ++ s2b)
                    c3
            = lsubstc C wfct (snoc s2a0 (x, t2) ++ s2b) pC7)
           as eqc4.
    (* begin proof of assert *)
    generalize (lsubstc_csubst_ex2 C (snoc s2a0 (x, t2)) s2b wfct pC7);
      intro eq; exrepnd; rw <- eq1; clear eq1;
      generalize (lsubstc_csubst_ex2 (subst C x (mk_var y)) (snoc (snoc (snoc s2a0 (x, t1)) (y, t2)) (z, mkc_axiom)) s2b w2 c3);
      intro eq; exrepnd; rw <- eq1; clear eq1;
      apply lsubstc_eq; try (complete sp);
      rewrite subset_free_vars_csub_snoc; auto;
      try (complete (generalize (eqvars_free_vars_disjoint C [(x, mk_var y)]); intro eqv;
                     rw eqvars_prop in eqv; rw eqv; rw in_app_iff; rw in_remove_nvars; simpl;
                     boolvar; simpl; sp)).
    rw @csubst_subst_snoc_eq2;
      try (complete sp);
      try (complete (rw @dom_csub_snoc; simpl; rw in_snoc;
                     allapply @similarity_dom; repnd; allrw; sp)).
    rw @csub_filter_snoc1.
    rw @csub_filter_trivial; sp.
    rw disjoint_singleton_l; allapply @similarity_dom; repnd; allrw; sp.
    (* end proof of assert *)
    rw eqc4 in hyp0.

    clear eqc1 eqc2 eqc3 eqc4.
    proof_irr; GC.
    
    rw <- @member_equality_iff in hyp2.
    apply tequality_mkc_equality in hyp0. repnd.
    dup hyp2 as hh. apply equality_sym in hh. apply equality_refl in hh.
    apply hyp0 in hh.
    eapply equality_in_uni.
    eapply equality_trans; eauto.
    
  - vr_seq_true in hyp1.

    generalize (hyp1
                  (snoc (snoc s1a0 (x, t1)) (z, mkc_axiom) ++ s1b)
                  (snoc (snoc s2a0 (x, t1)) (z, mkc_axiom) ++ s2b));
      clear hyp1; intro hyp1.


    (* First we prove the hyps_functionality part of hyp1 *)
    autodimp hyp1 hyp.
    introv simil.
    rw @similarity_app in simil; exrepnd; subst; cpx.
    apply app_split in simil0; simpl; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    rw @similarity_snoc in simil5; exrepnd; subst; allsimpl; cpx.
    rw @similarity_snoc in simil5; exrepnd; subst; allsimpl; cpx.
    lsubst_tac.
    allrw @equality_in_base_iff.
    apply @equality_refl in simil2.
    rw <- @member_member_iff in simil2.
    spcast.

    rewrite substitute_hyps_snoc_sub_weak in simil1; try (complete sp).

    duplicate eqh as eqh'.
    apply hyps_functionality_init_seg with (s3 := s2b0) in eqh; try (complete sp).
    generalize (hyps_functionality_init_seg_snoc2 lib s1a t0 t2 G x A w p eqh);
      intro hf; autodimp hf hyp.

    rw @eq_hyps_app.
    exists (snoc (snoc s1a (x, t0)) (z, mkc_axiom))
           s1b0
           (snoc (snoc s2a (x, t4)) (z, t3))
           s2b0;
      allrw length_snoc; dands; try (complete sp).

    assert (cover_vars (mk_member (mk_var x) A) (snoc s2a (x, t4)))
           as cv1
           by (apply cover_vars_change_sub with (sub1 := snoc s1a (x, t0)); sp;
               allrw @dom_csub_app; allrw @dom_csub_snoc; simpl;
               allapply @similarity_dom; repnd; allrw; sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc s1a (x,t0)) (snoc s2a (x,t4)) (@mkc_axiom pp) t3 w0 p0 cv1; sp.

    rw @eq_hyps_snoc; simpl.
    exists s1a s2a t0 t4 (@wf_base pp) (cover_vars_base s1a) (cover_vars_base s2a); sp.

    lsubst_tac; apply @tequality_base.

    lsubst_tac; proof_irr; GC.
    (* tequality it will follow from squiggle equality*)
    assert (tequality lib (lsubstc A w s1a p) (lsubstc A w s2a c))
           as eqt
           by (generalize (eqh (snoc s2a (x,t2))); intro imp;
               autodimp imp hyp;
               try (rw @similarity_snoc; simpl);
               try (exists s1a s2a t0 t2 w p; sp);
               rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx; proof_irr; sp).
    apply @tequality_mkc_member_if_cequivc; dands; try (complete sp); sp.
    
    apply sub_eq_hyps_snoc_weak; sp.
    generalize (eqh' (snoc s2a (x, t4) ++ s2b0)); intro imp.
    autodimp imp hyp.
    rw @similarity_app.
    exists (snoc s1a (x,t0)) s1b0 (snoc s2a (x,t4)) s2b0; allrw length_snoc; sp.
    rw @similarity_snoc; simpl.
    exists s1a s2a t0 t4 w p; sp.
    apply @equality_respects_cequivc_right with (t2 := t0); sp.

    rw @eq_hyps_app in imp; simpl in imp; exrepnd.
    apply app_split in imp0; simpl; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).
    apply app_split in imp2; simpl; repnd; subst; allrw length_snoc; cpx;
    try (complete (allrw @similarity_dom; repnd; allrw; sp)).

 
    (* First we prove the similarity part of hyp1 *)
    autodimp hyp1 hyp.

    rw @similarity_app; simpl.
    exists (snoc (snoc s1a0 (x, t1)) (z, mkc_axiom)) s1b
           (snoc (snoc s2a0 (x, t1)) (z, mkc_axiom)) s2b;
      allrw length_snoc; sp;
      try (complete (rewrite substitute_hyps_snoc_sub_weak; sp)).

    assert (wf_term (mk_member (mk_var x) A))
           as wm
           by (unfold mk_member; apply wf_equality; sp).

    assert (cover_vars (mk_member (mk_var x) A) (snoc s1a0 (x, t1)))
           as cm
           by (unfold mk_member; rw @cover_vars_equality; sp;
               try (complete (apply cover_vars_snoc_weak_r; simpl; sp));
               apply cover_vars_snoc_weak; sp).

    rw @similarity_snoc; simpl.
    exists (snoc s1a0 (x, t1)) (snoc s2a0 (x, t1)) (@mkc_axiom pp) (@mkc_axiom pp) wm cm; sp.

    rw @similarity_snoc; simpl.
    exists s1a0 s2a0 t1 t1 (@wf_base pp) (cover_vars_base s1a0); sp.

    lsubst_tac; rw @equality_in_base_iff; spcast; sp.

    lsubst_tac; rw @member_eq; rw <- @member_member_iff.
    allapply @equality_refl; sp.

    exrepnd; lsubst_tac.
    subst_app.
    revert hyp0 hyp1.
    repeat match goal with
             | [ |- context[?x] ] =>
               match type of x with
                 | cover_vars _ _ => revert x
                 | wf_term _ => revert x
               end
           end.
    lsubst_tac.
    introv.
    proof_irr; sp.
Qed.



(* begin hide *)

Lemma lsubstc_snoc_app_weak {o} :
  forall t w s1 x u s2 c,
    !LIn x (@free_vars o t)
    -> {c' : cover_vars t (s1 ++ s2)
        & lsubstc t w (snoc s1 (x,u) ++ s2) c
          = lsubstc t w (s1 ++ s2) c'}.
Proof.
  introv ni.

  assert (cover_vars t (s1 ++ s2)) as c'.
  allrw @cover_vars_eq.
  provesv.
  allrw @dom_csub_app; allrw @dom_csub_snoc; allsimpl.
  allrw in_app_iff; allrw in_snoc; sp; subst; sp.

  assert (wf_term (csubst t (snoc s1 (x, u)))) as w1.
  apply wf_term_csubst; auto.

  assert (cover_vars (csubst t (snoc s1 (x, u))) s2) as c1.
  apply cover_vars_csubst; auto.

  assert (wf_term (csubst t s1)) as w2.
  apply wf_term_csubst; auto.

  assert (cover_vars (csubst t s1) s2) as c2.
  apply cover_vars_csubst; auto.

  exists c'.
  rewrite <- @lsubstc_csubst_eq with (w := w1) (p := c1).
  rewrite <- @lsubstc_csubst_eq with (w := w2) (p := c2).
  revert w1 c1.
  rewrite @subset_free_vars_csub_snoc with (t := t) (v := x); auto; introv.
  proof_irr; auto.
Qed.

Ltac lsubstc_snoc_app :=
  match goal with
    | [ H : context[lsubstc ?t ?w (snoc ?s1 (?x,?u) ++ ?s2) ?c] |- _ ] =>
      let h := fresh "h" in
      let e := fresh "e" in
      let c' := fresh "c'" in
      assert (!LIn x (free_vars t)) as h by eauto;
        generalize (lsubstc_snoc_app_weak t w s1 x u s2 c h);
        intro e; destruct e as [c' e];
        rewrite e in H;
        clear h e
  end.

Ltac lsubstc_app :=
  match goal with
    | [ H : context[lsubstc ?t ?w (?s1 ++ ?s2) ?c] |- _ ] =>
      let e := fresh "e" in
      let w' := fresh "w'" in
      let c' := fresh "c'" in
      generalize (lsubstc_csubst_ex2 t s1 s2 w c); intro e;
      destruct e as [w' e];
      destruct e as [c' e];
      rewrite <- e in H;
      clear e

    | [ |- context[lsubstc ?t ?w (?s1 ++ ?s2) ?c] ] =>
      let e := fresh "e" in
      let w' := fresh "w'" in
      let c' := fresh "c'" in
      generalize (lsubstc_csubst_ex2 t s1 s2 w c); intro e;
      destruct e as [w' e];
      destruct e as [c' e];
      rewrite <- e;
      clear e
  end.

Ltac csubst_subst_snoc :=
  match goal with
    | [ H : context[csubst (subst ?t ?x (mk_var ?y)) (snoc ?s (?y, ?u))] |- _ ] =>
      let e := fresh "e" in
      let h := fresh "h" in
      generalize (csubst_subst_snoc_eq2 s t x y u);
        intro e;
        autodimp e h;try (complete insub);[];
        autodimp e h;try (complete insub);[];
        autodimp e h;try (complete insub);[];
        rewrite e in H;
        clear e

    | [ |- context[csubst (subst ?t ?x (mk_var ?y)) (snoc ?s (?y, ?u))] ] =>
      let e := fresh "e" in
      let h := fresh "h" in
      generalize (csubst_subst_snoc_eq2 s t x y u);
        intro e;
        autodimp e h;try (complete insub);[];
        autodimp e h;try (complete insub);[];
        autodimp e h;try (complete insub);[];
        rewrite e;
        clear e
  end.

(* end hide *)



(* [15] ============ FUNCTIONALITY FOR EQUALITY ============ *)

(**

  This is a simpler version of the functionality rule to prove equalities:
<<
   G, x : A, J |- a = b in T

     By functionalityForEquality y z

     G, x : A, J | T in U(i)
     G, x : Base, y : Base, z : x = y in A, J |- a = b[x\y] in T
>>
*)

Definition rule_functionality_for_equality {o}
           (G J     : @barehypotheses o)
           (A a b T : NTerm)
           (x y z   : NVar)
           (i       : nat) :=
  mk_rule
    (mk_baresequent (snoc G (mk_hyp x A) ++ J) (mk_conclax (mk_equality a b T)))
    [ mk_baresequent
        (snoc G (mk_hyp x A) ++ J)
        (mk_conclax (mk_member T (mk_uni i))),
      mk_baresequent
        (snoc (snoc (snoc G (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_equality (mk_var x) (mk_var y) A))
              ++ J)
        (mk_conclax (mk_equality a (subst b x (mk_var y)) T))
    ]
    [].

Lemma rule_functionaliy_for_equality_true {o} :
  forall lib (G J     : @barehypotheses o)
         (A a b T : NTerm)
         (x y z   : NVar)
         (i       : nat)
         (bc      : !LIn y (bound_vars b)),
    rule_true lib (rule_functionality_for_equality G J A a b T x y z i).
Proof.
  unfold rule_functionality_for_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
     apply tequality_in_uni_implies_tequality in hyp0; auto.

    allrw @member_eq.
    allrw <- @member_member_iff.
    auto.

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
    eexists; eexists; eexists; eexists; dands; auto; allrw length_snoc; eauto.

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; eauto.

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; eauto;
      try (complete (lsubst_tac; apply @tequality_base)).

    rw @eq_hyps_snoc; simpl.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; eauto;
      try (complete (lsubst_tac; apply @tequality_base)).

    {
      lsubst_tac.
      apply @tequality_equality_if_cequivc; auto.
      generalize (hf1 (snoc s2a1 (x,t0))); intro k.
      autodimp k hyp.
      rw @similarity_snoc; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; auto.
      exact sim2.
      rw @eq_hyps_snoc in k; simpl in k; exrepnd; cpx; proof_irr; auto.
    }

    {
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
    }

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
    { apply cover_vars_equality; dands; auto;
        try (apply cover_vars_var); repeat (rw @dom_csub_snoc); simpl;
        repeat (rw in_snoc); sp;
        repeat (apply cover_vars_snoc_weak); auto; eauto 3 with slow.
      eapply similarity_cover_vars; eauto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
    { apply wf_equality; auto. }
    { apply cover_vars_equality; dands; auto;
        try (apply cover_vars_var); repeat (rw @dom_csub_snoc); simpl;
        repeat (rw in_snoc); sp;
        repeat (apply cover_vars_snoc_weak); auto; eauto 3 with slow. }
    { auto. }
    { auto. }
    { auto. }
    { auto. }
Qed.
