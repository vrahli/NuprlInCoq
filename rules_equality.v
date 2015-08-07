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


Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export subst_tacs.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)

(* begin hide *)




(* end hide *)


(**

  The following rule eliminates equalities between equality types:
<<
   H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i), J |- C ext e

     By equalityUniverseElim y z w

     H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i),
        [y : A = B in U(i)],
        [z : a1 = b1 in (A \/ Base)]
        [w : a2 = b2 in (A \/ Base)]
        J |- C ext e
>>
 *)
Definition rule_equality_universe_elim {o}
           (H J  : @barehypotheses o)
           (A B a1 a2 b1 b2 C e : NTerm)
           (x y z w : NVar)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality
                            (mk_equality a1 a2 A)
                            (mk_equality b1 b2 B)
                            (mk_uni i)))
             ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp x (mk_equality
                                               (mk_equality a1 a2 A)
                                               (mk_equality b1 b2 B)
                                               (mk_uni i))))
                          (mk_hhyp y (mk_equality A B (mk_uni i))))
                    (mk_hhyp z (mk_equality a1 b1 (mk_bunion A mk_base))))
              (mk_hhyp w (mk_equality a2 b2 (mk_bunion A mk_base)))
              ++ J)
        (mk_concl C e)
    ]
    [].

Lemma rule_equality_universe_elim_true {o} :
  forall lib (H J : @barehypotheses o)
         (A B a1 a2 b1 b2 C e : NTerm)
         (x y z w : NVar)
         (i : nat),
    rule_true lib (rule_equality_universe_elim H J A B a1 a2 b1 b2 C e x y z w i).
Proof.
  unfold rule_equality_universe_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract
            (snoc H
                  (mk_hyp
                     x
                     (mk_equality
                        (mk_equality a1 a2 A)
                        (mk_equality b1 b2 B)
                        (mk_uni i))) ++ J)
            (mk_concl C e)) as cex.
  clear hyp1.
  unfold closed_extract; allsimpl.
  allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc; allsimpl; auto.

  exists cex.

  (* We prove some simple facts on our sequents *)
  assert (!LIn y (free_vars C)
          # !LIn z (free_vars C)
          # !LIn w (free_vars C)

          # !LIn y (free_vars e)
          # !LIn z (free_vars e)
          # !LIn w (free_vars e)

          # !LIn x (free_vars a1)
          # !LIn y (free_vars a1)
          # !LIn z (free_vars a1)
          # !LIn w (free_vars a1)

          # !LIn x (free_vars a2)
          # !LIn y (free_vars a2)
          # !LIn z (free_vars a2)
          # !LIn w (free_vars a2)

          # !LIn x (free_vars A)
          # !LIn y (free_vars A)
          # !LIn z (free_vars A)
          # !LIn w (free_vars A)

          # !LIn x (free_vars b1)
          # !LIn y (free_vars b1)
          # !LIn z (free_vars b1)
          # !LIn w (free_vars b1)

          # !LIn x (free_vars b2)
          # !LIn y (free_vars b2)
          # !LIn z (free_vars b2)
          # !LIn w (free_vars b2)

          # !LIn x (free_vars B)
          # !LIn y (free_vars B)
          # !LIn z (free_vars B)
          # !LIn w (free_vars B)

          # !LIn w (hyps_free_vars J)
          # !LIn z (hyps_free_vars J)
          # !LIn y (hyps_free_vars J)

          # !LIn w (free_vars_hyps J)
          # !LIn z (free_vars_hyps J)
          # !LIn y (free_vars_hyps J)

          # !LIn w (vars_hyps J)
          # !LIn z (vars_hyps J)
          # !LIn y (vars_hyps J)
         ) as vhyps.

  clear hyp1.
  dwfseq.
  sp; try (complete (discover; allrw in_app_iff; allrw in_snoc; sp;
                     allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ niyC vhyps ].
  destruct vhyps as [ nizC vhyps ].
  destruct vhyps as [ niwC vhyps ].

  destruct vhyps as [ niye vhyps ].
  destruct vhyps as [ nize vhyps ].
  destruct vhyps as [ niwe vhyps ].

  destruct vhyps as [ nixa1 vhyps ].
  destruct vhyps as [ niya1 vhyps ].
  destruct vhyps as [ niza1 vhyps ].
  destruct vhyps as [ niwa1 vhyps ].

  destruct vhyps as [ nixa2 vhyps ].
  destruct vhyps as [ niya2 vhyps ].
  destruct vhyps as [ niza2 vhyps ].
  destruct vhyps as [ niwa2 vhyps ].

  destruct vhyps as [ nixA vhyps ].
  destruct vhyps as [ niyA vhyps ].
  destruct vhyps as [ nizA vhyps ].
  destruct vhyps as [ niwA vhyps ].

  destruct vhyps as [ nixb1 vhyps ].
  destruct vhyps as [ niyb1 vhyps ].
  destruct vhyps as [ nizb1 vhyps ].
  destruct vhyps as [ niwb1 vhyps ].

  destruct vhyps as [ nixb2 vhyps ].
  destruct vhyps as [ niyb2 vhyps ].
  destruct vhyps as [ nizb2 vhyps ].
  destruct vhyps as [ niwb2 vhyps ].

  destruct vhyps as [ nixB vhyps ].
  destruct vhyps as [ niyB vhyps ].
  destruct vhyps as [ nizB vhyps ].
  destruct vhyps as [ niwB vhyps ].

  destruct vhyps as [ niwJ1 vhyps ].
  destruct vhyps as [ nizJ1 vhyps ].
  destruct vhyps as [ niyJ1 vhyps ].

  destruct vhyps as [ niwJ2 vhyps ].
  destruct vhyps as [ nizJ2 vhyps ].
  destruct vhyps as [ niyJ2 vhyps ].

  destruct vhyps as [ niwJ3 vhyps ].
  destruct vhyps as [ nizJ3 niyJ3 ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx; GC.

  lsubst_tac.

  rw @equality_in_mkc_equality in sim2; repnd.
  apply @equality_mkc_equality2_sp_in_uni in sim0; repnd.
  unfold equorsq2, equorsq in sim0; repnd.

  vr_seq_true in hyp1.
  pose proof (hyp1
                (snoc (snoc (snoc (snoc s1a0 (x,t1))
                                  (y,mkc_axiom))
                            (z,mkc_axiom))
                      (w,mkc_axiom)
                      ++ s1b)
                (snoc (snoc (snoc (snoc s2a0 (x,t2))
                                  (y,mkc_axiom))
                            (z,mkc_axiom))
                      (w,mkc_axiom)
                      ++ s2b)) as h; clear hyp1; rename h into hyp1.

  autodimp hyp1 hyp.

  (* we prove the hyps_functionality part *)

  introv sim'.
  rw @similarity_app in sim'; simpl in sim'; allrw length_snoc; exrepnd; subst; cpx; GC.
  apply app_split in sim'0; [| complete (allrw length_snoc; allrw; auto)].
  rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
  rw @similarity_snoc in sim'8; simpl in sim'8; exrepnd; subst; cpx.
  rw @similarity_snoc in sim'6; simpl in sim'6; exrepnd; subst; cpx.
  rw @similarity_snoc in sim'7; simpl in sim'7; exrepnd; subst; cpx.

  (* we bring in the eq_hyps from our main goal *)
  pose proof (eqh (snoc s2a (x,t6) ++ s2b0)) as eh.
  autodimp eh hyp.
  apply similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a (x, t6)) s2b0; dands; auto;
  try (complete (repeat (rw length_snoc); allrw; auto)).
  apply similarity_snoc; simpl.
  exists s1a s2a t0 t6 w10 p3; dands; auto.
  rw @substitute_hyps_snoc_sub_weak in sim'1; auto.
  rw @substitute_hyps_snoc_sub_weak in sim'1; auto.
  rw @substitute_hyps_snoc_sub_weak in sim'1; auto.
  (* done *)

  (* we simplify eh *)
  apply eq_hyps_app in eh; simpl in eh; exrepnd.
  apply app_split in eh0; [| complete (allrw length_snoc; allrw; auto)].
  apply app_split in eh2; [| complete (allrw length_snoc; allrw; auto)].
  repnd; subst; cpx.
  dup eh5 as ehsnoc.
  apply eq_hyps_snoc in eh5; simpl in eh5; exrepnd; cpx.

  lsubst_tac.

  apply equality_in_mkc_equality in sim'6; repnd.
  apply equality_mkc_equality2_sp_in_uni in sim'0; repnd.
  apply equality_in_mkc_equality in sim'3; repnd; GC.
  apply equality_in_mkc_equality in sim'2; repnd; GC.
  apply equality_in_mkc_equality in sim'5; repnd; GC.

  lsubst_tac.

  rw @eq_hyps_app.
  exists (snoc (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, mkc_axiom))
               (w, mkc_axiom))
         s1b
         (snoc (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4)) (w, t3))
         s2b1;
    dands; auto; repeat (rw length_snoc); try (complete (allrw; auto)).

  assert (cover_vars
            (mk_equality a2 b2 (mk_bunion A mk_base))
            (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4)))
    as cv1
      by (eapply cover_vars_change_sub;[|exact p0];
          repeat (rw @dom_csub_snoc); simpl; auto;
          allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, mkc_axiom))
         (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4))
         (@mkc_axiom o) t3 w7 p0 cv1;
    dands; auto.

  assert (cover_vars
            (mk_equality a1 b1 (mk_bunion A mk_base))
            (snoc (snoc s2a1 (x, t7)) (y, t5)))
    as cv2
      by (eapply cover_vars_change_sub;[|exact p1];
          repeat (rw @dom_csub_snoc); simpl; auto;
          allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom))
         (snoc (snoc s2a1 (x, t7)) (y, t5))
         (@mkc_axiom o) t4 w8 p1 cv2;
    dands; auto.

  assert (cover_vars (mk_equality A B (mk_uni i)) (snoc s2a1 (x, t7)))
    as cv3
      by (eapply cover_vars_change_sub;[|exact p2];
          repeat (rw @dom_csub_snoc); simpl; auto;
          allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a0 (x, t1))
         (snoc s2a1 (x, t7))
         (@mkc_axiom o) t5 w9 p2 cv3;
    dands; auto.

  lsubst_tac.

  apply tequality_mkc_equality2_sp in eh0; repnd.
  apply tequality_mkc_equality2_sp; dands; auto.
  unfold equorsq2 in eh0; repnd.
  unfold equorsq2; dands.

  unfold equorsq in eh3; unfold equorsq; dorn eh3.
  left.
  apply equality_mkc_equality2_sp_in_uni in eh3; repnd; auto.
  right; spcast.
  apply cequivc_decomp_equality in eh3; repnd; auto.

  unfold equorsq in eh0; unfold equorsq; dorn eh0.
  left.
  apply equality_mkc_equality2_sp_in_uni in eh0; repnd; auto.
  right; spcast.
  apply cequivc_decomp_equality in eh0; repnd; auto.

  lsubst_tac.
  apply tequality_mkc_equality2_sp in eh0; repnd.
  unfold equorsq2, equorsq in eh0; repnd.
  apply tequality_mkc_equality2_sp; dands.

  lsubst_tac.

  apply tequality_bunion; dands; auto.
  dorn eh3.
  apply equality_mkc_equality2_sp_in_uni in eh3; repnd.
  apply equality_in_uni in eh5; auto.
  spcast.
  apply cequivc_decomp_equality in eh3; repnd.
  apply equality_in_uni in sim7; auto.
  apply tequality_refl in sim7.
  apply type_respects_cequivc_right; auto.

  unfold equorsq2; dands; lsubst_tac.

  dorn eh3.
  apply equality_mkc_equality2_sp_in_uni in eh3; repnd.
  destruct eh3 as [e1 e2].
  apply equorsq_in_bunion_left; auto.
  apply tequality_base.
  spcast.
  apply cequivc_decomp_equality in eh3; repnd.
  right; spcast; auto.

  dorn eh0.
  apply equality_mkc_equality2_sp_in_uni in eh0; repnd.
  destruct eh0 as [e1 e2].
  apply equorsq_in_bunion_left; auto.
  apply equality_in_uni in sim7.
  eapply equorsq_tequality; eauto.
  apply tequality_sym; auto.
  apply tequality_base.
  spcast.
  apply cequivc_decomp_equality in eh0; repnd.
  right; spcast; auto.

  apply tequality_mkc_equality in eh0; repnd.
  lsubst_tac.
  apply tequality_mkc_equality; dands; lsubst_tac.

  apply tequality_bunion; dands; auto.
  apply equality_in_uni in sim7.
  apply tequality_refl in sim7.
  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality in eh5; repnd; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  apply type_respects_cequivc_right; auto.

  split; intro k; lsubst_tac.

  apply equality_in_mkc_bunion in k; repnd.
  apply equality_in_mkc_bunion; dands; auto.
  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality in eh5; repnd; auto.
  apply tequality_sym in eh6; apply tequality_refl in eh6; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  apply type_respects_cequivc_left in eh5; auto.
  apply tequality_refl in eh5; auto.

  apply (equal_in_bunion_change2 lib
           (lsubstc A wT0 s1a0 cT0)
           mkc_base
           (lsubstc a2 w4 s1a0 c3)
           (lsubstc b2 w6 s1a0 c5)); auto.

  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality in eh5; repnd; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  apply type_respects_cequivc_left in eh5; auto.
  apply tequality_sym in eh5; auto.

  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality in eh5; repnd; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  rwg eh7.
  right; spcast; sp.

  dorn eh0.
  apply equality_in_uni in eh0.
  apply tequality_mkc_equality2 in eh0; repnd; auto.
  destruct eh0 as [e1 e2].
  apply (equorsq_tequality lib (lsubstc B wT1 s1a0 cT1)); auto.
  apply (tequality_trans _ _ (lsubstc A wT0 s1a0 cT0)); auto.
  apply equality_in_uni in sim7.
  apply tequality_sym; auto.
  dorn eh5.
  apply equality_mkc_equality2_sp_in_uni in eh5; repnd.
  apply equality_in_uni in eh0; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  apply cequivc_sym in eh5; rwg eh5.
  apply equality_in_uni in sim7; apply tequality_refl in sim7; auto.

  spcast.
  apply cequivc_decomp_equality in eh0; repnd.
  rwg eh7; right; spcast; sp.

  apply equality_in_mkc_bunion in k; repnd.
  apply equality_in_mkc_bunion; dands; auto.
  apply equality_in_uni in sim7.
  apply tequality_refl in sim7; auto.

  apply (equal_in_bunion_change2 lib
           (lsubstc A wT0 s2a1 cT3)
           mkc_base
           (lsubstc a2 w4 s2a1 c9)
           (lsubstc b2 w6 s2a1 c11)); auto.

  apply tequality_sym.
  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality in eh5; repnd; auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  apply cequivc_sym in eh5; rwg eh5.
  apply equality_in_uni in sim7.
  apply tequality_refl in sim7; auto.

  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality2 in eh5; repnd; auto.
  destruct eh5 as [e1 e2].
  apply equorsq_sym.
  apply (equorsq_tequality lib (lsubstc A wT0 s1a0 cT0)); auto.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  rwg eh7; right; spcast; sp.

  dorn eh0.
  apply equality_in_uni in eh0.
  apply tequality_mkc_equality2 in eh0; repnd; auto.
  destruct eh0 as [e1 e2].
  apply equorsq_sym.
  apply (equorsq_tequality lib (lsubstc B wT1 s1a0 cT1)); auto.
  apply tequality_sym; auto.
  apply equality_in_uni in sim7; auto.
  spcast.
  apply cequivc_decomp_equality in eh0; repnd.
  rwg eh7; right; spcast; sp.

  dorn eh5.
  apply equality_in_uni in eh5.
  apply tequality_mkc_equality2 in eh5; repnd; auto.
  destruct eh5 as [e1 e2].
  dorn e2.
  left; lsubst_tac.
  apply equality_in_bunion_left; auto.
  apply tequality_base.
  right; sp.
  spcast.
  apply cequivc_decomp_equality in eh5; repnd.
  right; spcast; sp.

  dorn eh0.
  apply equality_in_uni in eh0.
  apply tequality_mkc_equality2 in eh0; repnd; auto.
  destruct eh0 as [e1 e2].
  dorn e2.
  left; lsubst_tac.
  apply equality_in_bunion_left; auto.
  eapply tequality_preserving_equality; eauto.
  apply tequality_sym; auto.
  apply equality_in_uni in sim7; auto.
  apply tequality_base.
  right; sp.
  spcast.
  apply cequivc_decomp_equality in eh0; repnd.
  right; spcast; sp.


  (* Now the sub_eq_hyps *)

  apply sub_eq_hyps_snoc_weak_iff; auto.
  apply sub_eq_hyps_snoc_weak_iff; auto.
  apply sub_eq_hyps_snoc_weak_iff; auto.


  (* Now we prove the similarity *)
  autodimp hyp1 hyp.

  apply similarity_app; simpl.
  exists (snoc (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, mkc_axiom))
               (w, mkc_axiom))
         s1b
         (snoc (snoc (snoc (snoc s2a0 (x, t2)) (y, mkc_axiom)) (z, mkc_axiom))
               (w, mkc_axiom))
         s2b; repeat (rw length_snoc); dands; auto.

  assert (wf_term (mk_equality a2 b2 (mk_bunion A mk_base)))
  as wt1 by (apply wf_equality_iff; dands; auto;
             apply wf_bunion; dands; auto).

  assert (cover_vars (mk_equality a2 b2 (mk_bunion A mk_base))
                     (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, mkc_axiom)))
    as cv1 by (repeat (apply cover_vars_snoc_weak);
               apply cover_vars_equality; dands; auto;
               apply cover_vars_bunion; sp).

  apply similarity_snoc; simpl.
  exists (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, mkc_axiom))
         (snoc (snoc (snoc s2a0 (x, t2)) (y, mkc_axiom)) (z, mkc_axiom))
         (@mkc_axiom o) (@mkc_axiom o) wt1 cv1; dands; auto.

  assert (wf_term (mk_equality a1 b1 (mk_bunion A mk_base)))
  as wt2 by (apply wf_equality_iff; dands; auto;
             apply wf_bunion; dands; auto).

  assert (cover_vars (mk_equality a1 b1 (mk_bunion A mk_base))
                     (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)))
    as cv2 by (repeat (apply cover_vars_snoc_weak);
               apply cover_vars_equality; dands; auto;
               apply cover_vars_bunion; sp).

  apply similarity_snoc; simpl.
  exists (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom))
         (snoc (snoc s2a0 (x, t2)) (y, mkc_axiom))
         (@mkc_axiom o) (@mkc_axiom o) wt2 cv2; dands; auto.

  assert (wf_term (mk_equality A B (mk_uni i)))
    as wt3 by (apply wf_equality_iff; dands; auto).

  assert (cover_vars (mk_equality A B (mk_uni i)) (snoc s1a0 (x, t1)))
    as cv3
      by (repeat (apply cover_vars_snoc_weak);
          apply cover_vars_equality; dands; auto).

  apply similarity_snoc; simpl.
  exists (snoc s1a0 (x, t1))
         (snoc s2a0 (x, t2))
         (@mkc_axiom o) (@mkc_axiom o) wt3 cv3; dands; auto.

  apply similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w0 p; dands; auto.

  lsubst_tac.
  apply equality_in_mkc_equality; dands; auto.
  apply equality_mkc_equality2_sp_in_uni; dands; auto.
  split; auto.

  lsubst_tac.
  apply equality_in_mkc_equality; dands; auto;
  try (complete (spcast; apply computes_to_valc_refl; sp)).

  lsubst_tac.
  apply equality_in_mkc_equality; dands; auto;
  try (complete (spcast; apply computes_to_valc_refl; sp)).
  lsubst_tac.

  apply equality_in_mkc_bunion; dands; auto.
  apply equality_in_uni in sim7; auto.
  apply tequality_refl in sim7; auto.
  apply tequality_base.
  dorn sim8.
  apply @eq_in_bunion_eq1; auto.
  spcast.
  apply @eq_in_bunion_eq2; auto.
  apply equality_in_base_iff; spcast; sp.

  lsubst_tac.
  apply equality_in_mkc_equality; dands; auto;
  try (complete (spcast; apply computes_to_valc_refl; sp)).
  lsubst_tac.

  apply equality_in_mkc_bunion; dands; auto.
  apply equality_in_uni in sim7; auto.
  apply tequality_refl in sim7; auto.
  apply tequality_base.
  dorn sim0.
  apply @eq_in_bunion_eq1; auto.
  spcast.
  apply @eq_in_bunion_eq2; auto.
  apply equality_in_base_iff; spcast; sp.

  repeat (rw @substitute_hyps_snoc_sub_weak; auto).


  (* Now we can use our hypothesis *)

  exrepnd.
  lsubst_tac.
  repeat lsubstc_snoc_app.
  sp.
Qed.



(* begin hide *)



(**

  The following rule eliminates equalities between equality types:
<<
   H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i), J |- C ext e

     By equalityUniverseElim y z w

     H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i),
        [y : A = B in U(i)],
        [z : a1 = b1 in A \/ a1 = b1 in Base]
        [w : a2 = b2 in A \/ a2 = b2 in Base]
        J |- C ext t
>>
 *)
Definition rule_equality_universe_elim2 {o}
           (H J  : @barehypotheses o)
           (A B a1 a2 b1 b2 C e : NTerm)
           (x y z w : NVar)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality
                            (mk_equality a1 a2 A)
                            (mk_equality b1 b2 B)
                            (mk_uni i)))
             ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp x (mk_equality
                                               (mk_equality a1 a2 A)
                                               (mk_equality b1 b2 B)
                                               (mk_uni i))))
                          (mk_hhyp y (mk_equality A B (mk_uni i))))
                    (mk_hhyp z (mk_or (mk_equality a1 b1 A)
                                      (mk_equality a1 b1 mk_base))))
              (mk_hhyp w (mk_or (mk_equality a2 b2 A)
                                (mk_equality a2 b2 mk_base)))
              ++ J)
        (mk_concl C e)
    ]
    [].

Lemma rule_equality_universe_elim_true2 {o} :
  forall lib (H J : @barehypotheses o)
         (A B a1 a2 b1 b2 C e : NTerm)
         (x y z w : NVar)
         (i : nat),
    rule_true lib (rule_equality_universe_elim2 H J A B a1 a2 b1 b2 C e x y z w i).
Proof.
  unfold rule_equality_universe_elim2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract
            (snoc H
                  (mk_hyp
                     x
                     (mk_equality
                        (mk_equality a1 a2 A)
                        (mk_equality b1 b2 B)
                        (mk_uni i))) ++ J)
            (mk_concl C e)) as cex.
  clear hyp1.
  unfold closed_extract; allsimpl.
  allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc; allsimpl; auto.

  exists cex.

  (* We prove some simple facts on our sequents *)
  assert (!LIn y (free_vars C)
          # !LIn z (free_vars C)
          # !LIn w (free_vars C)

          # !LIn y (free_vars e)
          # !LIn z (free_vars e)
          # !LIn w (free_vars e)

          # !LIn x (free_vars a1)
          # !LIn y (free_vars a1)
          # !LIn z (free_vars a1)
          # !LIn w (free_vars a1)

          # !LIn x (free_vars a2)
          # !LIn y (free_vars a2)
          # !LIn z (free_vars a2)
          # !LIn w (free_vars a2)

          # !LIn x (free_vars A)
          # !LIn y (free_vars A)
          # !LIn z (free_vars A)
          # !LIn w (free_vars A)

          # !LIn x (free_vars b1)
          # !LIn y (free_vars b1)
          # !LIn z (free_vars b1)
          # !LIn w (free_vars b1)

          # !LIn x (free_vars b2)
          # !LIn y (free_vars b2)
          # !LIn z (free_vars b2)
          # !LIn w (free_vars b2)

          # !LIn x (free_vars B)
          # !LIn y (free_vars B)
          # !LIn z (free_vars B)
          # !LIn w (free_vars B)

          # !LIn w (hyps_free_vars J)
          # !LIn z (hyps_free_vars J)
          # !LIn y (hyps_free_vars J)

          # !LIn w (free_vars_hyps J)
          # !LIn z (free_vars_hyps J)
          # !LIn y (free_vars_hyps J)

          # !LIn w (vars_hyps J)
          # !LIn z (vars_hyps J)
          # !LIn y (vars_hyps J)
         ) as vhyps.

  clear hyp1.
  dwfseq.
  sp; try (complete (discover; allrw in_app_iff; allrw in_snoc; sp;
                     allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ niyC vhyps ].
  destruct vhyps as [ nizC vhyps ].
  destruct vhyps as [ niwC vhyps ].

  destruct vhyps as [ niye vhyps ].
  destruct vhyps as [ nize vhyps ].
  destruct vhyps as [ niwe vhyps ].

  destruct vhyps as [ nixa1 vhyps ].
  destruct vhyps as [ niya1 vhyps ].
  destruct vhyps as [ niza1 vhyps ].
  destruct vhyps as [ niwa1 vhyps ].

  destruct vhyps as [ nixa2 vhyps ].
  destruct vhyps as [ niya2 vhyps ].
  destruct vhyps as [ niza2 vhyps ].
  destruct vhyps as [ niwa2 vhyps ].

  destruct vhyps as [ nixA vhyps ].
  destruct vhyps as [ niyA vhyps ].
  destruct vhyps as [ nizA vhyps ].
  destruct vhyps as [ niwA vhyps ].

  destruct vhyps as [ nixb1 vhyps ].
  destruct vhyps as [ niyb1 vhyps ].
  destruct vhyps as [ nizb1 vhyps ].
  destruct vhyps as [ niwb1 vhyps ].

  destruct vhyps as [ nixb2 vhyps ].
  destruct vhyps as [ niyb2 vhyps ].
  destruct vhyps as [ nizb2 vhyps ].
  destruct vhyps as [ niwb2 vhyps ].

  destruct vhyps as [ nixB vhyps ].
  destruct vhyps as [ niyB vhyps ].
  destruct vhyps as [ nizB vhyps ].
  destruct vhyps as [ niwB vhyps ].

  destruct vhyps as [ niwJ1 vhyps ].
  destruct vhyps as [ nizJ1 vhyps ].
  destruct vhyps as [ niyJ1 vhyps ].

  destruct vhyps as [ niwJ2 vhyps ].
  destruct vhyps as [ nizJ2 vhyps ].
  destruct vhyps as [ niyJ2 vhyps ].

  destruct vhyps as [ niwJ3 vhyps ].
  destruct vhyps as [ nizJ3 niyJ3 ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx; GC.

  lsubst_tac.

  rw @equality_in_mkc_equality in sim2; repnd.
  apply @equality_mkc_equality2_sp_in_uni in sim0; repnd.
  destruct sim0 as [e1 e2].

Abort.



(**

  The following rule eliminates equalities between equality types:
<<
   H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i), J |- C ext e

     By equalityUniverseElim y z w

     H, x : (a1 = a2 in A) = (b1 = b2 in B) in U(i),
        [y : A = B in U(i)],
        [z : a1 = b1 in A \/ a1 ~ b1]
        [w : a2 = b2 in A \/ a2 ~ b2]
        J |- C ext t
>>
 *)
Definition rule_equality_universe_elim3 {o}
           (H J  : @barehypotheses o)
           (A B a1 a2 b1 b2 C e : NTerm)
           (x y z w : NVar)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality
                            (mk_equality a1 a2 A)
                            (mk_equality b1 b2 B)
                            (mk_uni i)))
             ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp x (mk_equality
                                               (mk_equality a1 a2 A)
                                               (mk_equality b1 b2 B)
                                               (mk_uni i))))
                          (mk_hhyp y (mk_equality A B (mk_uni i))))
                    (mk_hhyp z (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1))))
              (mk_hhyp w (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2)))
              ++ J)
        (mk_concl C e)
    ]
    [].

Lemma rule_equality_universe_elim_true3 {o} :
  forall lib (H J : @barehypotheses o)
         (A B a1 a2 b1 b2 C e : NTerm)
         (x y z w : NVar)
         (i : nat),
    rule_true lib (rule_equality_universe_elim3 H J A B a1 a2 b1 b2 C e x y z w i).
Proof.
  unfold rule_equality_universe_elim3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract
            (snoc H
                  (mk_hyp
                     x
                     (mk_equality
                        (mk_equality a1 a2 A)
                        (mk_equality b1 b2 B)
                        (mk_uni i))) ++ J)
            (mk_concl C e)) as cex.
  clear hyp1.
  unfold closed_extract; allsimpl.
  allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc; allsimpl; auto.

  exists cex.

  (* We prove some simple facts on our sequents *)
  assert (!LIn y (free_vars C)
          # !LIn z (free_vars C)
          # !LIn w (free_vars C)

          # !LIn y (free_vars e)
          # !LIn z (free_vars e)
          # !LIn w (free_vars e)

          # !LIn x (free_vars a1)
          # !LIn y (free_vars a1)
          # !LIn z (free_vars a1)
          # !LIn w (free_vars a1)

          # !LIn x (free_vars a2)
          # !LIn y (free_vars a2)
          # !LIn z (free_vars a2)
          # !LIn w (free_vars a2)

          # !LIn x (free_vars A)
          # !LIn y (free_vars A)
          # !LIn z (free_vars A)
          # !LIn w (free_vars A)

          # !LIn x (free_vars b1)
          # !LIn y (free_vars b1)
          # !LIn z (free_vars b1)
          # !LIn w (free_vars b1)

          # !LIn x (free_vars b2)
          # !LIn y (free_vars b2)
          # !LIn z (free_vars b2)
          # !LIn w (free_vars b2)

          # !LIn x (free_vars B)
          # !LIn y (free_vars B)
          # !LIn z (free_vars B)
          # !LIn w (free_vars B)) as vhyps.

  clear hyp1.
  dwfseq.
  sp; try (complete (discover; allrw in_app_iff; allrw in_snoc; sp;
                     allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ niyC vhyps ].
  destruct vhyps as [ nizC vhyps ].
  destruct vhyps as [ niwC vhyps ].

  destruct vhyps as [ niye vhyps ].
  destruct vhyps as [ nize vhyps ].
  destruct vhyps as [ niwe vhyps ].

  destruct vhyps as [ nixa1 vhyps ].
  destruct vhyps as [ niya1 vhyps ].
  destruct vhyps as [ niza1 vhyps ].
  destruct vhyps as [ niwa1 vhyps ].

  destruct vhyps as [ nixa2 vhyps ].
  destruct vhyps as [ niya2 vhyps ].
  destruct vhyps as [ niza2 vhyps ].
  destruct vhyps as [ niwa2 vhyps ].

  destruct vhyps as [ nixA vhyps ].
  destruct vhyps as [ niyA vhyps ].
  destruct vhyps as [ nizA vhyps ].
  destruct vhyps as [ niwA vhyps ].

  destruct vhyps as [ nixb1 vhyps ].
  destruct vhyps as [ niyb1 vhyps ].
  destruct vhyps as [ nizb1 vhyps ].
  destruct vhyps as [ niwb1 vhyps ].

  destruct vhyps as [ nixb2 vhyps ].
  destruct vhyps as [ niyb2 vhyps ].
  destruct vhyps as [ nizb2 vhyps ].
  destruct vhyps as [ niwb2 vhyps ].

  destruct vhyps as [ nixB vhyps ].
  destruct vhyps as [ niyB vhyps ].
  destruct vhyps as [ nizB niwB ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx; GC.

  lsubst_tac.

  rw @equality_in_mkc_equality in sim2; repnd.
  apply equality_in_uni in sim0.

  rw @tequality_mkc_equality2_sp in sim0; repnd.
  unfold equorsq2, equorsq in sim0; repnd.

  dorn sim0; dorn sim8.

  - vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc (snoc (snoc s1a0 (x,t1))
                                    (y,mkc_axiom))
                              (z,tt))
                        (w,tt)
                        ++ s1b)
                  (snoc (snoc (snoc (snoc s2a0 (x,t2))
                                    (y,mkc_axiom))
                              (z,tt))
                        (w,tt)
                        ++ s2b)) as h; clear hyp1; rename h into hyp1.

    autodimp hyp1 hyp.

    (* we prove the hyps_functionality part *)

    introv sim'.
    rw @similarity_app in sim'; simpl in sim'; allrw length_snoc; exrepnd; subst; cpx; GC.
    apply app_split in sim'0; [| complete (allrw length_snoc; allrw; auto)].
    rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
    rw @similarity_snoc in sim'8; simpl in sim'8; exrepnd; subst; cpx.
    rw @similarity_snoc in sim'6; simpl in sim'6; exrepnd; subst; cpx.
    rw @similarity_snoc in sim'7; simpl in sim'7; exrepnd; subst; cpx.

    (* we bring in the eq_hyps from our main goal *)
    pose proof (eqh (snoc s2a (x,t6) ++ s2b)) as eh.
    autodimp eh hyp.
    apply similarity_app; simpl.
    exists (snoc s1a (x, t0)) s1b0 (snoc s2a (x, t6)) s2b; dands; auto;
    try (complete (repeat (rw length_snoc); allrw; auto)).
    apply similarity_snoc; simpl.
    exists s1a s2a t0 t6 w10 p3; dands; auto.
    (* done *)

    (* we simplify eh *)
    apply eq_hyps_app in eh; simpl in eh; exrepnd.
    apply app_split in eh0; [| complete (allrw length_snoc; allrw; auto)].
    apply app_split in eh2; [| complete (allrw length_snoc; allrw; auto)].
    repnd; subst; cpx.
    dup eh5 as ehsnoc.
    apply eq_hyps_snoc in eh5; simpl in eh5; exrepnd; cpx.

    lsubst_tac.

    rw @eq_hyps_app.
    exists (snoc (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, tt))
              (w, tt))
           s1b
           (snoc (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4)) (w, t3)) s2b0;
      dands; auto; repeat (rw length_snoc); try (complete (allrw; auto)).

    assert (cover_vars
              (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2))
              (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4)))
      as cv1
        by (eapply cover_vars_change_sub;[|exact p0];
            repeat (rw @dom_csub_snoc); simpl; auto;
            allapply @similarity_dom; repnd; allrw; sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom)) (z, tt))
           (snoc (snoc (snoc s2a1 (x, t7)) (y, t5)) (z, t4))
           (@tt o) t3 w7 p0 cv1;
      dands; auto.

    assert (cover_vars
              (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1))
              (snoc (snoc s2a1 (x, t7)) (y, t5)))
      as cv2
        by (eapply cover_vars_change_sub;[|exact p1];
            repeat (rw @dom_csub_snoc); simpl; auto;
            allapply @similarity_dom; repnd; allrw; sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc (snoc s1a0 (x, t1)) (y, mkc_axiom))
           (snoc (snoc s2a1 (x, t7)) (y, t5))
           (@tt o) t4 w8 p1 cv2;
      dands; auto.

    assert (cover_vars (mk_equality A B (mk_uni i)) (snoc s2a1 (x, t7)))
      as cv3
        by (eapply cover_vars_change_sub;[|exact p2];
            repeat (rw @dom_csub_snoc); simpl; auto;
            allapply @similarity_dom; repnd; allrw; sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc s1a0 (x, t1))
           (snoc s2a1 (x, t7))
           (@mkc_axiom o) t5 w9 p2 cv3;
      dands; auto.

    lsubst_tac.

    apply tequality_mkc_equality2_sp in eh0; repnd.
    apply tequality_mkc_equality2_sp; dands; auto.
    unfold equorsq2 in eh0; repnd.
    unfold equorsq2; dands.

    unfold equorsq in eh3; unfold equorsq; dorn eh3.
    left.
    apply equality_mkc_equality2_sp_in_uni in eh3; repnd; auto.
    right; spcast.
    apply cequivc_decomp_equality in eh3; repnd; auto.

    unfold equorsq in eh0; unfold equorsq; dorn eh0.
    left.
    apply equality_mkc_equality2_sp_in_uni in eh0; repnd; auto.
    right; spcast.
    apply cequivc_decomp_equality in eh0; repnd; auto.


    lsubst_tac.
    apply tequality_mkc_equality2_sp in eh0; repnd.
    unfold equorsq2, equorsq in eh0; repnd.
    apply tequality_mkc_or; dands.
    apply tequality_mkc_equality2_sp.
    dands.

    dorn eh3.
    apply equality_in_uni in eh3.
    apply tequality_mkc_equality2_sp in eh3; repnd; auto.
    spcast.
    apply cequivc_decomp_equality in eh3; repnd.
    apply equality_in_mkc_equality in sim'6; repnd.
    apply equality_mkc_equality2_sp_in_uni in sim'0; repnd.
    apply equality_in_uni in sim'9.
    apply tequality_respects_cequivc_right with (T2 := lsubstc A wT0 s1a0 cT0); auto.
    apply tequality_refl in sim'9; auto.

    unfold equorsq2; dands.

    dorn eh3.
    apply equality_in_uni in eh3.
    apply tequality_mkc_equality2_sp in eh3; repnd; auto.
    unfold equorsq2 in eh3; repnd; auto.
    spcast.
    apply cequivc_decomp_equality in eh3; repnd.
    right; spcast; auto.

    dorn eh0.
    apply equality_in_uni in eh0.
    apply tequality_mkc_equality2_sp in eh0; repnd; auto.
    unfold equorsq2 in eh0; repnd; auto.
    apply equality_in_mkc_equality in sim'6; repnd.
    apply equality_mkc_equality2_sp_in_uni in sim'0; repnd.
    apply equality_in_uni in sim'9.
    eapply equorsq_tequality; eauto.
    apply tequality_sym; auto.
    spcast.
    apply cequivc_decomp_equality in eh0; repnd.
    right; spcast; auto.

    apply tequality_mkc_cequiv.

Abort.

(* end hide *)
