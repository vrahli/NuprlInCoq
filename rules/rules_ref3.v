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

  Authors: Vincent Rahli

*)


Require Export rules_ref2.


Lemma implies_ccequivc_ext_add {o} :
  forall lib (f g a b : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_add f a) (mkc_add g b).
Proof.
  introv ceqa ceqb x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  simpl in *; spcast.
  apply implies_cequivc_mkc_add; auto.
Qed.
Hint Resolve implies_ccequivc_ext_add : slow.

Lemma ccequivc_ext_mkc_add_nat {o} :
  forall (lib : @library o) m n,
    ccequivc_ext lib (mkc_add (mkc_nat m) (mkc_nat n)) (mkc_nat (m + n)).
Proof.
  introv ext; spcast.
  apply computes_to_valc_implies_cequivc.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
  rewrite <- Nat2Z.inj_add; auto.
Qed.


(**

<<
   H |- n + m ∈ QT(ℕ)

     By QTNat_subtype Nat

     H |- n ∈ QT(ℕ)
     H |- m ∈ QT(ℕ)
>>

 *)


Definition rule_add_qtnat {o}
           (lib   : @library o)
           (n m   : NTerm)
           (e1 e2 : NTerm)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_add n m) mk_qtnat)))
    [
      mk_baresequent H (mk_concl (mk_member n mk_tnat) e1),
      mk_baresequent H (mk_concl (mk_member m mk_tnat) e2)
    ]
    [].

Lemma rule_add_qtnat_true {o} :
  forall lib (n m e1 e2 : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true lib (rule_add_qtnat lib n m e1 e2 H).
Proof.
  unfold rule_add_qtnat, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (@covered o mk_axiom (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  lsubst_tac.

  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member
                lib' mk_qtnat (mk_add n m) s1 s2 H wT wt ct1 ct2 cT cT0) as q.
  lsubst_tac; autorewrite with slow in *.
  repeat (autodimp q hyp); eauto 2 with slow.

  clear dependent s1.
  clear dependent s2.
  introv eqh sim.

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 lib' ext s1 s2 eqh sim) as hyp1; exrepnd.
  pose proof (hyp2 lib' ext s1 s2 eqh sim) as hyp2; exrepnd.

  lsubst_tac.
  apply member_if_inhabited in hyp1.
  apply member_if_inhabited in hyp2.
  apply tequality_mkc_member_implies_sp in hyp0; auto;[].
  apply tequality_mkc_member_implies_sp in hyp3; auto;[].
  autorewrite with slow in *.

  clear hyp1 hyp2.
  apply equality_in_tnat in hyp0.
  apply equality_in_tnat in hyp3.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact hyp0|exact hyp3]; clear hyp0 hyp3; introv y hyp0 hyp3.
  unfold per_props_nat.equality_of_nat in *; exrepnd.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp1.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp3.

  eapply equality_respects_cequivc_left; [apply ccequivc_ext_sym;apply implies_ccequivc_ext_add;eauto |].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_add;eauto |].

  eapply equality_respects_cequivc_left; [apply ccequivc_ext_sym;apply ccequivc_ext_mkc_add_nat|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_ext_mkc_add_nat|].
  eauto 3 with slow.
Qed.
