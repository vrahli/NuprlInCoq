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


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.

Require Export close_util_qnat.
Require Export close_util_qlt.
Require Export close_util1.
Require Export close_util2.


Lemma equality_of_qlt_bar_implies_eq_term_equals_equality_of_qlt_bar {o} :
  forall (ts : cts(o)) lib T T' eq (a b : @CTerm o),
    ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> per_bar (per_qlt ts) lib T T' eq
    -> eq <=2=> (equality_of_qlt_bar lib a b).
Proof.
  introv comp per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1.
    unfold per_qlt in *; exrepnd.
    apply per1 in h; clear per1.

    eapply in_open_bar_pres; try exact h; clear h; introv h; introv.
    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qlt_right in ceq; repnd.
    apply ccequivc_ext_preserves_equality_of_qlt; eauto 3 with slow.

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_qlt in per1; exrepnd.
    apply per1; clear per1.
    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qlt_right in ceq; repnd.
    eapply sub_per_equality_of_qlt_bar in h; eauto.
    eapply implies_eq_term_equals_per_qlt_bar2; try exact h; eauto 3 with slow.
Qed.

Lemma per_bar_per_qlt_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_qlt (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.
  apply CL_qlt; auto.
Qed.

Lemma cequiv_mk_qlt {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_qlt a b)
    -> cequiv lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_qlt a' b')
         # cequiv lib a a'
         # cequiv lib b b'}.
Proof.
  prove_cequiv_mk; allrw <- @isprogram_qlt_iff; sp.
Qed.

Lemma cequivc_mkc_qlt {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_qlt a b)
    -> cequivc lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_qlt a' b')
         # cequivc lib a a'
         # cequivc lib b b'}.
Proof.
  unfold computes_to_valc, cequivc; intros; destruct_cterms; allsimpl.
  generalize (cequiv_mk_qlt lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_qlt_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma ccequivc_ext_qkt {o} :
  forall lib (T T' : @CTerm o) A B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_qlt A B)
    -> ccomputes_to_valc_ext lib T' (mkc_qlt A B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma equality_of_qnat_implies_ccequivc_ext {o} :
  forall (lib : @library o) a b,
    equality_of_qnat lib a b
    -> ccequivc_ext lib a b.
Proof.
  introv equ ext.
  apply equ in ext; exrepnd; spcast.
  apply computes_to_valc_implies_cequivc in ext1.
  apply computes_to_valc_implies_cequivc in ext0.
  eapply cequivc_trans;eauto.
  apply cequivc_sym; auto.
Qed.
Hint Resolve equality_of_qnat_implies_ccequivc_ext : slow.

Lemma per_qlt_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) equ,
    per_qlt ts lib T1 T2 equ
    -> per_qlt ts lib T2 T1 equ.
Proof.
  introv per.
  unfold per_qlt in *; exrepnd.
  eexists; eexists; eexists; eexists; dands; eauto; eauto 3 with slow.
  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  apply implies_eq_term_equals_per_qlt_bar2; eauto 3 with slow.
Qed.

Lemma equality_of_qnat_ccequivc_ext_trans {o} :
  forall (lib : @library o) a b c,
    equality_of_qnat lib a b
    -> ccequivc_ext lib b c
    -> equality_of_qnat lib a c.
Proof.
  introv equ ceq ext.
  applydup equ in ext.
  applydup ceq in ext.
  exrepnd; spcast.
  apply computes_to_valc_implies_cequivc in ext2.
  apply cequivc_sym in ext1.
  eapply cequivc_trans in ext2; eauto.
  apply cequivc_sym in ext2.
  apply @cequivc_nat_implies_computes_to_valc in ext2.
  exists n; dands; spcast; auto.
Qed.
Hint Resolve equality_of_qnat_ccequivc_ext_trans : slow.

Lemma ccequivc_ext_equality_of_qnat_trans {o} :
  forall (lib : @library o) a b c,
    ccequivc_ext lib a b
    -> equality_of_qnat lib b c
    -> equality_of_qnat lib a c.
Proof.
  introv ceq equ ext.
  applydup equ in ext.
  applydup ceq in ext.
  exrepnd; spcast.
  apply computes_to_valc_implies_cequivc in ext0.
  eapply cequivc_trans in ext0; eauto.
  apply cequivc_sym in ext0.
  apply @cequivc_nat_implies_computes_to_valc in ext0.
  exists n; dands; spcast; auto.
Qed.
Hint Resolve ccequivc_ext_equality_of_qnat_trans : slow.

Lemma equality_of_qnat_trans {o} :
  forall lib (a b c : @CTerm o),
    equality_of_qnat lib a b
    -> equality_of_qnat lib b c
    -> equality_of_qnat lib a c.
Proof.
  introv h q ext; applydup h in ext; applydup q in ext; exrepnd.
  spcast.
  eapply computes_to_valc_eq in ext3; try exact ext1.
  apply mkc_nat_eq_implies in ext3; subst.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve equality_of_qnat_trans : slow.

Lemma per_qlt_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2,
    per_qlt ts lib T T2 eq2
    -> per_qlt ts lib T1 T eq1
    -> per_qlt ts lib T1 T2 eq1.
Proof.
  introv pera perb.
  unfold per_qlt in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq; repnd.

  eexists; eexists; eexists; eexists; dands; eauto 3 with slow.
Qed.

Lemma per_qlt_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2,
    per_qlt ts lib T T2 eq2
    -> per_qlt ts lib T1 T eq1
    -> per_qlt ts lib T1 T2 eq2.
Proof.
  introv pera perb.
  unfold per_qlt in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq; repnd.
  eexists; eexists; eexists; eexists; dands; eauto 3 with slow.
  eapply eq_term_equals_trans; eauto.
  apply implies_eq_term_equals_per_qlt_bar2; eauto with slow.
Qed.

Lemma equality_of_qlt_bar_symmetric {o} :
  forall lib (a b : @CTerm o) t1 t2,
    equality_of_qlt_bar lib a b t1 t2
    -> equality_of_qlt_bar lib a b t2 t1.
Proof.
  introv per; tcsp.
Qed.

Lemma equality_of_qlt_bar_transitive {o} :
  forall lib (a b : @CTerm o) t1 t2 t3,
    equality_of_qlt_bar lib a b t1 t2
    -> equality_of_qlt_bar lib a b t2 t3
    -> equality_of_qlt_bar lib a b t1 t3.
Proof.
  introv pera perb; tcsp.
Qed.

Lemma ccequivc_ext_qlt {o} :
  forall lib (T T' : @CTerm o) A B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_qlt A B)
    -> ccomputes_to_valc_ext lib T' (mkc_qlt A B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_qlt1 {o} :
  forall lib (ts : cts(o)) T T1 T2 a b a' b' eq,
    ccomputes_to_valc_ext lib T1 (mkc_qlt a' b')
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> per_bar (per_qlt ts) lib T1 T2 eq
    -> per_bar (per_qlt ts) lib T T2 eq.
Proof.
  introv comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_qlt in *; exrepnd.

  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].
  eapply lib_extends_preserves_ccequivc_ext in ceqa; eauto.
  eapply lib_extends_preserves_ccequivc_ext in ceqb; eauto.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq; repnd.
  eexists; eexists; eexists; eexists; dands; eauto 3 with slow;[].
  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  apply implies_eq_term_equals_per_qlt_bar2; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_qlt2 {o} :
  forall lib (ts : cts(o)) T T1 T2 a b a' b' eq,
    ccomputes_to_valc_ext lib T1 (mkc_qlt a' b')
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> per_bar (per_qlt ts) lib T2 T1 eq
    -> per_bar (per_qlt ts) lib T T2 eq.
Proof.
  introv comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_qlt in *; exrepnd.

  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].
  eapply lib_extends_preserves_ccequivc_ext in ceqa; eauto.
  eapply lib_extends_preserves_ccequivc_ext in ceqb; eauto.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq; repnd.
  eapply lib_extends_preserves_ccequivc_ext in ceqa; eauto.
  eapply lib_extends_preserves_ccequivc_ext in ceqb; eauto.
  eexists; eexists; eexists; eexists; dands; eauto; eauto 4 with slow.
  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  apply implies_eq_term_equals_per_qlt_bar2; eauto 5 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_qlt {o} :
  forall ts lib T T' eq (a b a' b' : @CTerm o),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_qlt a b)
    -> T' ===>( lib) (mkc_qlt a' b')
    -> ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> (eq <=2=> (equality_of_qlt_bar lib a b))
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tysys dou c1 c2 ceqa ceqb eqiff.
  introv h ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt1;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt1;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt2;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt2;
      try exact h; try exact c2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_qlt3 {o} :
  forall lib (ts : cts(o)) T T1 T2 a u eq,
    ccomputes_to_valc_ext lib T (mkc_qlt a u)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_qlt ts) lib T T1 eq
    -> per_bar (per_qlt ts) lib T T2 eq.
Proof.
  introv comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_qlt in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq; repnd.
  eapply lib_extends_preserves_ccequivc_ext in ceqa; eauto.
  eapply ccequivc_ext_ccomputes_to_valc_ext in ceqa; eauto.
  eexists; eexists; eexists; eexists; dands; eauto; eauto 4 with slow.
  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  apply implies_eq_term_equals_per_qlt_bar2; eauto 4 with slow.
Qed.

Lemma per_bar_per_qlt_sym_rev {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_qlt ts) lib T' T eq
    -> per_bar (per_qlt ts) lib T T' eq.
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.
  apply per_qlt_sym; auto.
Qed.

Lemma implies_type_value_respecting_trans2_per_qlt {o} :
  forall ts lib T T' eq (a b u v : @CTerm o),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_qlt a u)
    -> T' ===>( lib) (mkc_qlt b v)
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib u v
    -> (eq <=2=> (equality_of_qlt_bar lib a u))
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tysys dou c1 c2 ceqa ceqb eqiff.
  introv h cl ceq.
  repndors; subst.

  {
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt3;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt3;
      try exact c1; try exact tsa; try exact tsb; eauto 3 with slow.
    eapply per_bar_per_qlt_sym_rev; try exact c1; try exact tsa; try exact tsb; auto.
  }

  {
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qlt3;
      try exact c2; try exact tsa'; try exact tsb'; eauto 3 with slow.
    eapply per_bar_per_qlt_sym_rev; try exact c2; try exact tsa'; try exact tsb'; auto.
  }
Qed.

Lemma per_bar_per_qlt_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 eq1 eq2,
    per_bar (per_qlt ts) lib T1 T eq1
    -> per_bar (per_qlt ts) lib T T2 eq2
    -> per_bar (per_qlt ts) lib T1 T2 eq1.
Proof.
  introv pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.
  eapply per_qlt_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_qlt_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 eq1 eq2,
    per_bar (per_qlt ts) lib T1 T eq1
    -> per_bar (per_qlt ts) lib T T2 eq2
    -> per_bar (per_qlt ts) lib T1 T2 eq2.
Proof.
  introv pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.
  eapply per_qlt_trans2; try exact comp; eauto.
Qed.
