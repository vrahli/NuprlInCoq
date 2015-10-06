(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export computation9.
Require Export stronger_continuity_rule2.


Lemma hasvalue_likec_implies_or {o} :
  forall lib (t : @CTerm o),
    hasvalue_likec lib t
    -> (hasvaluec lib t [+] raises_exceptionc lib t).
Proof.
  introv; destruct_cterms.
  unfold hasvalue_likec, hasvaluec, raises_exceptionc; simpl.
  introv hv; apply hasvalue_like_implies_or in hv; eauto 3 with slow.
Qed.

Lemma computes_to_valc_mkc_try_if_exc {o} :
  forall lib (t : @CTerm o) a c e n x v,
    computes_to_excc lib n t x
    -> computes_to_valc lib (mkc_try t a c e) v
    -> computes_to_valc lib (mkc_atom_eq a n (substc x c e) (mkc_exception n x)) v.
Proof.
  introv ce cv.
  destruct_cterms.
  allunfold @computes_to_excc.
  allunfold @computes_to_valc; allsimpl.
  pose proof (implies_reduces_to_trycatch lib x1 x2 x3 x c x4) as h.
  repeat (autodimp h hyp).
  eapply reduces_to_value_eq in cv;[|exact h]; auto.
Qed.

Lemma spM_cond2 {o} :
  forall lib (F f : @CTerm o) n k,
    member lib F (mkc_fun nat2nat mkc_tnat)
    -> member lib f nat2nat
    -> cequivc lib (mkc_apply2 (spM_c F) (mkc_nat n) f) (mkc_nat k)
    -> cequivc lib (mkc_apply F f) (mkc_nat k).
Proof.
  introv mF mf ceq.
  eapply cequivc_trans in ceq;
    [|apply cequivc_sym; apply cequivc_apply2_spM_c].
  rw @test_c_eq in ceq.

  destruct (fresh_atom o (getc_utokens F ++ getc_utokens f)) as [a nia].
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cequivc_fresh_nat_implies
                lib nvare
                (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f)
                a k) as ceq1.
  repeat (autodimp ceq1 hyp).
  { destruct_cterms; allunfold @getc_utokens; allsimpl.
    allunfold @getcv_utokens; allsimpl; allrw app_nil_r; allrw in_app_iff; sp. }

  rw @substc_test_try2_cv in ceq1.

  eapply cequivc_trans in ceq1;
    [|apply simpl_cequivc_mkc_try;
       [apply implies_cequivc_apply;
         [apply cequivc_refl|apply cequivc_sym; apply cequiv_bound2_c_cbv]
       |apply cequivc_refl]
    ].
  apply cequivc_nat_implies in ceq1.

  pose proof (hasvalue_likec_try
                lib
                (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                (mkc_utoken a) nvarc (mkcv_axiom nvarc)) as hv.
  autodimp hv hyp.
  { eapply computes_to_valc_implies_hasvalue_likec;exact ceq1. }

  apply hasvalue_likec_implies_or in hv; repndors.

  - apply hasvaluec_computes_to_valc_implies in hv; exrepnd.

    pose proof (computes_to_valc_mkc_try
                  lib
                  (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                  (mkc_utoken a) nvarc (mkcv_axiom nvarc)
                  b (PKa a)) as comp.
    repeat (autodimp comp hyp).
    { apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc. }

    computes_to_eqval.

    pose proof (equality_lam_force_nat_c_in_nat2nat lib nvarx nvarz f mf) as h.
    apply equality_in_fun in mF; repnd; clear mF0 mF1.
    apply mF in h; clear mF.
    apply equality_in_tnat in h.
    apply equality_of_nat_imp_tt in h.
    unfold equality_of_nat_tt in h; exrepnd.

    applydup @computes_to_valc_implies_hasvalue_likec in hv0.

    pose proof (computes_to_valc_differ_force2
                  lib (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                  (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                  n a f k0) as h.
    repeat (autodimp h hyp);[|].
    { destruct_cterms; simpl.
      clear ceq1 h1 h0 hv0 hv1 mf.
      allunfold @getc_utokens; allsimpl.
      apply differ_force_oterm; simpl; tcsp.
      introv j; repndors; tcsp; ginv; constructor.
      - apply differ_force_refl; auto.
      - apply differ_force_oterm; simpl; tcsp.
        introv j; repndors; tcsp; ginv; constructor.
        apply differ_force_nat; auto. }

    repndors.

    + computes_to_eqval.
      allapply @eq_mkc_nat_implies; subst; auto.
      apply computes_to_valc_implies_cequivc; auto.

    + provefalse.
      apply cequivc_spexcc in h; exrepnd.
      eapply computes_to_valc_and_excc_false in h2; eauto.

  - provefalse.

    apply raises_exceptionc_as_computes_to_excc in hv; exrepnd.
    eapply computes_to_valc_mkc_try_if_exc in ceq1;[|exact hv1].
    apply computes_to_valc_mkc_atom_eq_pk_implies in ceq1; exrepnd.
    allrw @substc_mkcv_axiom.
    boolvar.

    + apply computes_to_valc_isvalue_eq in ceq1; eauto 3 with slow; ginv.

    + eapply computes_to_valc_and_excc_false in ceq1; tcsp.
      apply computes_to_excc_iff_reduces_toc.
      apply reduces_to_symm.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
