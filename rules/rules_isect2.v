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


Require Export sequents_tacs.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export sequents_equality.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)

(* end hide *)


(* [3] ============ ISECT MEMBER EQUALITY ============ *)

(**

  We state the intersection member equality rule as follows:
<<
   H |- b1 = b2 in isect x:A. B

     By isect_memberEquality lvl(i) z ()

     H, z : A |- b1 = b2 in subst B x z
     H |- A = A in Type(i)
>>
 *)

Definition rule_isect_member_equality {o}
           (A B b1 b2 : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality b1 b2 (mk_isect A x B))))
    [ mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_equality b1 b2 (subst B x (mk_var z)))),
      mk_baresequent H (mk_conclax (mk_member A (mk_uni i)))
    ]
    [sarg_var z].

Lemma rule_isect_member_equality_true {o} :
  forall lib (A B b1 b2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_isect_member_equality A B b1 b2 x z i H).
Proof.
  intros.
  unfold rule_isect_member_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  clear cargs.
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (!LIn z (vars_hyps H)
          # !LIn z (free_vars b1)
          # !LIn z (free_vars b2)
          # !LIn z (free_vars A)
          # (z <> x -> !LIn z (free_vars B))) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
    try (complete (generalize (cg z); sp;
                   allrw in_remove_nvars; allsimpl; sp;
                   discover; sp)).

  destruct vhyps as [nizH vhyps].
  destruct vhyps as [nizb1 vhyps].
  destruct vhyps as [nizb2 vhyps].
  destruct vhyps as [nizA nizB].
  (* done with proving these simple facts *)

  vr_seq_true.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality lib
                (mk_isect A x B) b1 b2 s1 s2 H
                wT w1 w2 c1 c0 c2 c3 cT cT0
                eqh sim); intro k.
  lsubst_tac.
  apply k; clear k.


  (* - tequality part - *)
  apply tequality_isect; dands.

  (* -- A is a type -- *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_member_iff in hyp2.
  apply member_in_uni in hyp2.
  apply tequality_in_uni_implies_tequality in hyp0; auto.

  (* -- B is a family over A -- *)
  introv ea.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))); clear hyp1; intro hyp1.

  (* --- hyps_functionality --- *)
  autodimp hyp1 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' eqh sim'); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  apply member_in_uni in hyp1.
  apply tequality_in_uni_implies_tequality in hyp0; auto.

  (* --- similarity --- *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' w0 c4; dands; auto.

  (* --- we use hyp1 --- *)
  exrepnd.
  lsubst_tac.
  clear hyp1.
  apply tequality_mkc_equality in hyp0; repnd.
  generalize (lsubstc_subst_snoc_eq s1 B x z a wT0 w3 cT1 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw <- eq1.
  generalize (lsubstc_subst_snoc_eq s2 B x z a' wT0 w3 cT2 c7); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw <- eq2.
  auto.


  (* - equality part - *)
  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply equality_in_isect; dands.

  (* -- A is a type -- *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_member_iff in hyp2.
  apply member_in_uni in hyp2; auto.

  (* -- B is a type family over A -- *)
  introv ea.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z,a)) (snoc s1 (z,a'))); clear hyp1; intro hyp1.

  (* --- hyps_functionality --- *)
  autodimp hyp1 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' hf sim'); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  apply member_in_uni in hyp1.
  apply tequality_in_uni_implies_tequality in hyp0; auto.

  (* --- similarity --- *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a a' w0 c1; dands; auto.
  apply similarity_refl in sim; auto.

  (* --- we use hyp1 --- *)
  exrepnd.
  lsubst_tac.
  clear hyp1.
  apply tequality_mkc_equality in hyp0; repnd.
  generalize (lsubstc_subst_snoc_eq s1 B x z a wT0 w3 cT c2); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw <- eq1.
  generalize (lsubstc_subst_snoc_eq s1 B x z a' wT0 w3 cT0 c2); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw <- eq2.
  auto.


  (* -- equality of b1 and b2 -- *)
  introv ea.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))); clear hyp1; intro hyp1.

  (* --- hyps_functionality --- *)
  autodimp hyp1 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' hf sim'); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  apply member_in_uni in hyp1.
  apply tequality_in_uni_implies_tequality in hyp0; auto.

  (* --- similarity --- *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' w0 c1; dands; auto.

  (* --- we use hyp1 --- *)
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  generalize (lsubstc_subst_snoc_eq s1 B x z a wT0 w3 cT c2); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw <- eq1; clear eq1.
  apply equality_commutes4 in hyp0; auto.
Qed.

(* begin hide *)

(* end hide *)
