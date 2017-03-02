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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_image.
Require Export sequents.


Lemma equality_in_mkc_squash {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 (mkc_squash T)
    <=> (t1 ===>(lib) mkc_axiom
         # t2 ===>(lib) mkc_axiom
         # inhabited_type lib T).
Proof.
  intros.
  rw @equality_in_mkc_image; split; intro e; exrepnd; spcast.

  - applydup @equal_in_image_prop in e; exrepnd; spcast.

    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) a1); intro c1.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) a2); intro c2.

    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var.

    assert (cequivc lib t1 mkc_axiom) as c3.
    eapply cequivc_trans.
    exact e2.
    sp.

    assert (cequivc lib t2 mkc_axiom) as c4.
    eapply cequivc_trans.
    exact e3.
    sp.

    generalize (cequivc_axiom lib mkc_axiom t1); intro i1.
    dest_imp i1 hyp.
    apply computes_to_valc_refl; apply isvalue_axiom.
    dest_imp i1 hyp.
    apply cequivc_sym; sp.

    generalize (cequivc_axiom lib mkc_axiom t2); intro i2.
    dest_imp i2 hyp.
    apply computes_to_valc_refl; apply isvalue_axiom.
    dest_imp i2 hyp.
    apply cequivc_sym; sp.

    sp; try (complete (spcast; sp)).
    exists a1.
    allapply @equality_refl; sp.

  - unfold inhabited_type in e; exrepnd.
    applydup @inhabited_implies_tequality in e2; dands; auto.
    apply eq_in_image_eq with (a1 := t) (a2 := t); auto; spcast.

    apply cequivc_trans with (b := mkc_axiom).
    apply computes_to_valc_implies_cequivc; sp.
    apply cequivc_sym.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var; sp.

    apply cequivc_trans with (b := mkc_axiom).
    apply computes_to_valc_implies_cequivc; sp.
    apply cequivc_sym.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var; sp.
Qed.

Lemma tequality_mkc_squash {p} :
  forall lib (T1 T2 : @CTerm p),
    tequality lib (mkc_squash T1) (mkc_squash T2)
    <=> tequality lib T1 T2.
Proof.
  introv.
  rw @tequality_mkc_image; split; sp; spcast.
  apply cequivc_refl.
Qed.

Lemma implies_tequality_equality_mkc_squash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> inhabited_type lib t1
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv teq inh.
  rw @equality_in_mkc_squash.
  rw @tequality_mkc_squash.
  dands; auto; spcast;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma implies_tequality_equality_mkc_squash_and {o} :
  forall lib (t1 t2 : @CTerm o),
    (tequality lib t1 t2 # inhabited_type lib t1)
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv h.
  apply implies_tequality_equality_mkc_squash; sp.
Qed.

Lemma equality_in_mkc_squash_ax {o} :
  forall lib (t : @CTerm o),
    equality lib mkc_axiom mkc_axiom (mkc_squash t)
    <=> inhabited_type lib t.
Proof.
  introv.
  rw @equality_in_mkc_squash; split; intro h; repnd; dands; auto; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma teq_and_eq_if_squash {o} :
  forall lib (a : @NTerm o) s1 s2 H wa ca1 ca2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> inhabited_type lib (lsubstc a wa s1 ca1)
    -> tequality lib (lsubstc a wa s1 ca1) (lsubstc a wa s2 ca2)
    -> (tequality lib
          (mkc_squash (lsubstc a wa s1 ca1))
          (mkc_squash (lsubstc a wa s2 ca2))
        # (inhabited_type lib (lsubstc a wa s1 ca1))).
Proof.
  introv hf sim ceq1 ceq2.

  assert (hyps_functionality lib s2 H)
    as hf2
      by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  assert (similarity lib s2 s1 H) as sim21 by (apply similarity_sym; auto).
  assert (similarity lib s1 s1 H) as sim11 by (apply similarity_refl in sim; auto).
  assert (similarity lib s2 s2 H) as sim22 by (apply similarity_refl in sim21; auto).

  dands; auto.
  rw @tequality_mkc_squash; auto.
Qed.
