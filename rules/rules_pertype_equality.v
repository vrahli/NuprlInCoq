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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents_tacs.
Require Export sequents_useful.
Require Export per_props_equality.
Require Export per_props_pertype.
Require Export sequents_equality.
Require Export list. (* why *)



(**

  We now prove the truth of several rules about the PER type.

*)

(* [14] ============ PERTYPE MEMBER EQUALITY ============ *)

(**

  The following rule is called the ``pertype member equality'' rule.
  It allows one to prove that terms are well-formed partial
  equivalence relations, i.e., members of a ``pertype'' type.

  The 3rd subgoal is necessary because we have to prove [R[s1] t1[s1] t2[s2]]
  is inhabited, but from the 2nd subgoal we only know that [R[s1] t1[s1] t2[s1]]
  is inhabited and that [R[s1] t1[s1] t2[s1]] and [R[s2] t1[s2] t2[s2]] are
  equal types.  Therefore, we need to go from [R[s1] t1[s1] t2[s2]] to either
  [R[s1] t1[s1] t2[s1]] or [R[s2] t1[s2] t2[s2]].
  For that we use the 1st subgoal which says that [R[s1] x y] is inhabited iff
  [R[s2] x y] is inhabited.  We now get that [R[s2] t1[s1] t2[s2]] is inhabited.
  Finally because t1[s1] ~ t1[s2] we get that [R[s2] t1[s2] t2[s2]] is inhabited.

<<
   H |- t1 = t2 in pertype(R)

     By pertypeMemberEquality i

     H |- pertype(R) in Type(i)
     H |- R t1 t2
     H |- t1 in Base
>>
 *)


Definition rule_pertype_member_equality {o}
           (t1 t2 R e : NTerm)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality t1 t2 (mk_pertype R))))
    [ mk_baresequent H (mk_conclax (mk_member (mk_pertype R) (mk_uni i))),
      mk_baresequent H (mk_concl (mk_apply2 R t1 t2) e),
      mk_baresequent H (mk_conclax (mk_member t1 mk_base))
    ]
    [].

Lemma rule_pertype_member_equality_true {o} :
  forall lib (t1 t2 R e : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_pertype_member_equality
                 t1 t2 R e
                 i
                 H).
Proof.
  unfold rule_pertype_member_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hypa.
  rename Hyp1 into hypb.
  rename Hyp2 into hypc.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in hypa.
  pose proof (hypa s1 s2) as hypa'.
  repeat (autodimp hypa' hyp); exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  allapply @member_in_uni.
  apply tequality_in_uni_implies_tequality in hypa'0; auto.

  generalize (teq_and_eq_if_equality lib
                (mk_pertype R) t1 t2 s1 s2 H wT w1 w2 c1 c3 c2 c4 cT cT0
                eqh sim); intro k; lsubst_tac; apply k; clear k; auto.

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.

  pose proof (hypa s1 s2 hf sim) as hypa; exrepnd.

  vr_seq_true in hypb.
  pose proof (hypb s1 s2 hf sim) as hypb; exrepnd.

  vr_seq_true in hypc.
  pose proof (hypc s1 s2 hf sim) as hypc; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  allrw @tequality_mkc_member_base.
  allapply @member_in_uni.

  (* trivial hyp *)
  clear hypc1.

  apply tequality_in_uni_implies_tequality in hypa0; auto.
  allapply @inhabited_type_if_equality.
  rw @tequality_mkc_pertype in hypa0; repnd.
  spcast.

  rw @equality_in_mkc_pertype2; dands; auto.
  apply hypa4.
  apply @inhabited_type_cequivc with (a := mkc_apply2 (lsubstc R w0 s2 c0)
                                                      (lsubstc t1 w1 s2 ct2)
                                                      (lsubstc t2 w2 s2 cb2)); auto;
    [apply implies_cequivc_apply2; sp;apply cequivc_sym; auto|];[].
  apply @inhabited_type_tequality in hypb0; auto.
Qed.




(* [16] ============ PERTYPE EQUALITY ============ *)

(**

  We can state the pertype equality rule as follows:
<<
   H |- pertype(R1) = pertype(R2) in Type(i)

     By pertypeMemberEquality x y z u v

     H, x : Base, y : Base |- R1 x y in Type(i)
     H, x : Base, y : Base |- R2 x y in Type(i)
     H, x : Base, y : Base, z : R1 x y |- R2 x y
     H, x : Base, y : Base, z : R2 x y |- R1 x y
     H, x : Base, y : Base, z : R1 x y |- R1 y x
     H, x : Base, y : Base, z : Base, u : R1 z y, v : R1 y z |- R1 x z
>>
 *)

Definition rule_pertype_equality {o}
           (R1 R2 e1 e2 e3 e4 : NTerm)
           (x y z u v : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_pertype R1) (mk_pertype R2) (mk_uni i))))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
        (mk_conclax (mk_member
                       (mk_apply2 R1 (mk_var x) (mk_var y))
                       (mk_uni i))),
      mk_baresequent
        (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
        (mk_conclax (mk_member
                       (mk_apply2 R2 (mk_var x) (mk_var y))
                       (mk_uni i))),
      mk_baresequent
        (snoc (snoc (snoc H (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
        (mk_concl (mk_apply2 R2 (mk_var x) (mk_var y)) e1),
      mk_baresequent
        (snoc (snoc (snoc H (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_apply2 R2 (mk_var x) (mk_var y))))
        (mk_concl (mk_apply2 R1 (mk_var x) (mk_var y)) e2),
      mk_baresequent
        (snoc (snoc (snoc H (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
        (mk_concl (mk_apply2 R1 (mk_var y) (mk_var x)) e3),
      mk_baresequent
        (snoc (snoc (snoc (snoc (snoc H (mk_hyp x mk_base))
                                (mk_hyp y mk_base))
                          (mk_hyp z mk_base))
                    (mk_hyp u (mk_apply2 R1 (mk_var x) (mk_var y))))
              (mk_hyp v (mk_apply2 R1 (mk_var y) (mk_var z))))
        (mk_concl (mk_apply2 R1 (mk_var x) (mk_var z)) e4)
    ]
    [].

Lemma rule_pertype_equality_true {o} :
  forall lib (R1 R2 e1 e2 e3 e4 : NTerm),
  forall x y z u v : NVar,
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_pertype_equality
                 R1 R2 e1 e2 e3 e4
                 x y z u v
                 i
                 H).
Proof.
  unfold rule_pertype_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2; rename Hyp2 into hyp3;
  rename Hyp3 into hyp4; rename Hyp4 into hyp5; rename Hyp5 into hyp6.
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R1)
           # !LIn y (free_vars R1)
           # !LIn z (free_vars R1)
           # !LIn u (free_vars R1)
           # !LIn v (free_vars R1)
           # !LIn x (free_vars R2)
           # !LIn y (free_vars R2)
           # !LIn z (free_vars R2)
           # !LIn u (free_vars R2)
           # !LIn v (free_vars R2)
           # !LIn x (vars_hyps H)
           # !LIn y (vars_hyps H)
           # !LIn z (vars_hyps H)
           # !x = y
           # !x = z
           # !y = z) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4 hyp5 hyp6.
  dwfseq.
  sp.

  destruct vhyps as [ nixr1 vhyps ].
  destruct vhyps as [ niyr1 vhyps ].
  destruct vhyps as [ nizr1 vhyps ].
  destruct vhyps as [ niur1 vhyps ].
  destruct vhyps as [ nivr1 vhyps ].
  destruct vhyps as [ nixr2 vhyps ].
  destruct vhyps as [ niyr2 vhyps ].
  destruct vhyps as [ nizr2 vhyps ].
  destruct vhyps as [ niur2 vhyps ].
  destruct vhyps as [ nivr2 vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ niyh vhyps ].
  destruct vhyps as [ nizh vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxz nyz ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_uni i) (mk_pertype R1) (mk_pertype R2) s1 s2 H
                wT w1 w2 c1 c4 c2 c5 cT cT0
                eqh sim);
    intro k; repeat (autodimp k hyp); lsubst_tac; auto; try (apply tequality_mkc_uni).

  clear dependent s1; clear dependent s2.
  introv hf sim; lsubst_tac.

  assert (cover_vars R1 s2)
    as cvr12
      by (apply cover_vars_change_sub with (sub1 := s1); auto;
          allapply @similarity_dom; repnd; allrw; sp).

  assert (cover_vars R2 s1)
    as cvr21
      by (apply cover_vars_change_sub with (sub1 := s2); auto;
          allapply @similarity_dom; repnd; allrw; sp).

  assert (hyps_functionality lib s2 H)
    as hf2 by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  assert (similarity lib s2 s1 H) as sim2 by (apply @similarity_sym; auto).

  generalize (membership_apply2
                lib H R1 x y i s1 s2 w0 c1 cvr12
                (wfh5, (wfct5, wfce), (ct4, ce4))
                hyp1 hf sim);
    introv fty1.
  repeat (autodimp fty1 hyp).

  generalize (membership_apply2
                lib H R2 x y i s2 s1 w3 c0 cvr21
                (wfh5, (wfct4, wfce), (ct3, ce4))
                hyp2 hf2 sim2);
    introv fty2.
  repeat (autodimp fty2 hyp).

  rw @mkc_pertype_equality_in_uni; dands; auto.

  introv.
  generalize (fty1 x0 y0); intro k; repnd; auto.

  introv.
  generalize (fty2 x0 y0); intro k; repnd; auto.

  introv; split; intro inh.

  generalize (implies_inhabited_apply2
                lib H x y z x0 y0 R1 R2 i e1 s2 s2 w0 w3 cvr12 c0
                (wfh5, (wfct5, wfce), (ct4, ce4))
                (wfh3, (wfct3, wfce3), (ct2, ce2)));
    intro impinh; repeat (autodimp impinh hyp).
  apply @similarity_refl in sim2; auto.
  generalize (fty1 x0 y0); intro k; repnd.
  apply iff_inhabited_type_if_tequality_mem in k0; rw <- k0; auto.

  generalize (implies_inhabited_apply2
                lib H x y z x0 y0 R2 R1 i e2 s2 s2 w3 w0 c0 cvr12
                (wfh5, (wfct4, wfce), (ct3, ce4))
                 (wfh2, (wfct2, wfce2), (ct1, ce1)));
    intro impinh; repeat (autodimp impinh hyp).
  apply @similarity_refl in sim2; auto.
  generalize (fty1 x0 y0); intro k; repnd.
  apply iff_inhabited_type_if_tequality_mem in k0; rw k0; auto.

  unfold is_per_type; repnd; dands.

  generalize (is_sym_type
                lib R1 H i x y z e3 s1 s2 w0 c1
                (wfh5, (wfct5, wfce), (ct4, ce4))
                (wfh3, (wfct1, wfce1), (ct0, ce0))).
  intro j; repeat (autodimp j hyp).

  generalize (is_trans_type
                lib R1 H i x y z u v e4 s1 s2 w0 c1
                (wfh5, (wfct5, wfce), (ct4, ce4))
                (wfh0, (wfct0, wfce0), (ct, ce))).
  intro j; repeat (autodimp j hyp).
Qed.
