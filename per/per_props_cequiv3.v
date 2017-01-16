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


Require Export sequents.
Require Export csubst3.
Require Export per_props_cequiv.


Lemma teq_and_eq_if_cequiv {o} :
  forall lib (a b : @NTerm o) s1 s2 H wa wb ca1 ca2 cb1 cb2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> ccequivc lib (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1)
    -> ccequivc lib (lsubstc a wa s2 ca2) (lsubstc b wb s2 cb2)
    -> (tequality lib
          (mkc_cequiv (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1))
          (mkc_cequiv (lsubstc a wa s2 ca2) (lsubstc b wb s2 cb2))
        # (ccequivc lib (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1))).
Proof.
  introv hf sim ceq1 ceq2.

  assert (hyps_functionality lib s2 H)
    as hf2
      by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  assert (similarity lib s2 s1 H) as sim21 by (apply similarity_sym; auto).
  assert (similarity lib s1 s1 H) as sim11 by (apply similarity_refl in sim; auto).
  assert (similarity lib s2 s2 H) as sim22 by (apply similarity_refl in sim21; auto).

  dands; auto.
  apply tequality_mkc_cequiv; split; intro h; auto.
Qed.

Lemma equality_in_mkc_cequiv_ax {o} :
  forall lib (t1 t2 : @CTerm o),
    equality lib mkc_axiom mkc_axiom (mkc_cequiv t1 t2)
    <=> t1 ~=~(lib) t2.
Proof.
  introv.
  rw @equality_in_mkc_cequiv; split; intro h; repnd; dands; auto; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma implies_approx_can_test {o} :
  forall lib c (a1 b1 c1 a2 b2 c2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib (mk_can_test c a1 b1 c1) (mk_can_test c a2 b2 c2).
Proof.
  introv apa apb apc.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  applydup @approx_relates_only_progs in apc.
  repnd.
  unfold mk_can_test.
  repeat prove_approx; sp.
Qed.

Lemma implies_cequivc_can_test {o} :
  forall lib c (a1 b1 c1 a2 b2 c2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib (mkc_can_test c a1 b1 c1) (mkc_can_test c a2 b2 c2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  split; apply implies_approx_can_test; auto.
Qed.

Lemma mkc_isint_as_can_test {o} :
  forall (a b c : @CTerm o),
    mkc_isint a b c = mkc_can_test CanIsint a b c.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Hint Resolve isprogram_isint : slow.

Lemma cequivc_mkc_int_integer {o} :
  forall lib k (a b : @CTerm o),
    cequivc lib (mkc_isint (mkc_integer k) a b) a.
Proof.
  introv; destruct_cterms; unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 4 with slow.
Qed.
