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

Require Export close_util_ffdefs.
Require Export close_util1.
Require Export close_util2.


Lemma per_bar_per_ffdefs_implies_eq_term_equals_per_ffdefs_eq_bar {o} :
  forall (ts : cts(o)) lib T T' eq (eqa : lib-per(lib,o)) A a A',
    computes_to_valc lib T (mkc_free_from_defs A a)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_bar (per_ffdefs ts) lib T T' eq
    -> eq <=2=> (per_ffdefs_eq_bar lib eqa a).
Proof.
  introv comp tsa per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per1.

  introv; split; intro h.

  - unfold per_ffdefs_eq_bar, per_ffdefs_eq.
    apply collapse2bars_ext.
    { introv; split; intro q; introv; repnd; dands; eauto 3 with slow. }

    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *.
    exrepnd.

    apply collapse2bars_ext.
    { introv; split; intro q; introv; repnd; dands; eauto 3 with slow. }

    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    assert (lib_extends lib'2 lib') as xt1 by eauto 3 with slow.
    pose proof (per0 _ br lib'2 xt1 (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_ffdefs in per0; exrepnd.
    apply per1 in h0; clear per1.
    unfold per_ffdefs_eq_bar, per_ffdefs_eq in h0; exrepnd.

    exists bar0.
    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x3) as h1; simpl in *.

    assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.

    spcast.
    apply (lib_extends_preserves_computes_to_valc _ _ xt2) in comp.
    computes_to_eqval.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ xt2) in eqas;[|exact tsa].

    dands; eauto 3 with slow.

  - introv br ext; introv.
    exists (raise_bar bar x); introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (per0 _ br'1 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_ffdefs in per0; exrepnd; spcast.
    apply (lib_extends_preserves_computes_to_valc _ _ (lib_extends_trans x0 x)) in comp.
    computes_to_eqval.
    apply per1.

    assert (lib_extends lib'2 lib) as xt by eauto 3 with slow.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ (lib_extends_trans x0 x)) in eqas;[|exact tsa].

    apply (sub_per_per_ffdefs_eq_bar _ _ (lib_extends_trans x0 x)) in h.
    eapply (implies_eq_term_equals_per_ffdefs_bar _ (trivial_bar lib'2));
      try exact h; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per; apply eqas; eauto.
Qed.

Lemma per_bar_per_ffdefs_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_ffdefs (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_ffdefs; auto.
Qed.

Lemma cequiv_mk_free_from_defs {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_free_from_defs a b)
    -> cequiv lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_free_from_defs a' b')
         # cequiv lib a a'
         # cequiv lib b b'}.
Proof. prove_cequiv_mk; allrw <- isprogram_free_from_defs_iff; sp.
Qed.

Lemma cequivc_mkc_free_from_defs {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_free_from_defs a b)
    -> cequivc lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_free_from_defs a' b')
         # cequivc lib a a'
         # cequivc lib b b'}.
Proof.
  unfold computes_to_valc, cequivc; intros; destruct_cterms; allsimpl.
  generalize (cequiv_mk_free_from_defs lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_free_from_defs_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma ccequivc_ext_ffdefs {o} :
  forall lib (T T' : @CTerm o) A B,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> {A' : CTerm , {B' : CTerm ,
        ccomputes_to_valc lib T' (mkc_free_from_defs A' B')
        # ccequivc_ext lib A A'
        # ccequivc_ext lib B B' }}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_free_from_defs in ceq';[|eauto]; exrepnd.
  exists a' b'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_free_from_defs A B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_free_from_defs a' b') ceq'0) as z.
    eapply cequivc_mkc_free_from_defs in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_free_from_defs A B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_free_from_defs a' b') ceq'0) as z.
    eapply cequivc_mkc_free_from_defs in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq1 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' B D (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x v z)
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.
  pose proof (ieqa  _ e) as ieqa.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  simpl in *.
  eapply trans;[|eauto].
  apply symm.
  eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
  eapply trans;[eauto|]; apply symm;auto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq1 : slow.

Lemma in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar1 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' B D (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x v z)
    -> (per_ffdefs_eq_bar lib eqa1 u) <=2=> (per_ffdefs_eq_bar lib eqa1 v).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.

  split; intro h; unfold per_ffdefs_eq_bar in *; exrepnd;
    exists bar; introv br xt; introv; pose proof (h0 _ br _ xt x) as h0;
      simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
        unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
          pose proof (ieqa  _ x) as ieqa;
          pose proof (resp  _ x) as resp;
          pose proof (symm  _ x) as symm;
          pose proof (trans _ x) as trans;
          simpl in *.

  {
    eapply trans;[|eauto].
    apply symm.
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }

  {
    eapply trans;[|eauto].
    apply symm.
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar1 : slow.

Lemma type_value_respecting_trans_per_bar_per_ffdefs1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A b A' b' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> computes_to_valc lib T1 (mkc_free_from_defs A' b')
    -> computes_to_valc lib T (mkc_free_from_defs A b)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib b b'
    -> per_bar (per_ffdefs ts) lib T1 T2 eq
    -> per_bar (per_ffdefs ts) lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_ffdefs in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  spcast; computes_to_eqval.

  exists A A2 b x2 eqa1; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq1; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar1; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq2 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' D B (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x z v)
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.
  pose proof (ieqa  _ e) as ieqa.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  simpl in *.
  eapply trans;[|eauto].
  apply symm.
  eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
  eapply trans;[eauto|]; apply symm;auto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq2 : slow.

Lemma in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' D B (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x z v)
    -> (per_ffdefs_eq_bar lib eqa1 u) <=2=> (per_ffdefs_eq_bar lib eqa1 z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.

  split; intro h; unfold per_ffdefs_eq_bar in *; exrepnd;
    exists bar; introv br xt; introv; pose proof (h0 _ br _ xt x) as h0;
      simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
        unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
          pose proof (ieqa  _ x) as ieqa;
          pose proof (resp  _ x) as resp;
          pose proof (symm  _ x) as symm;
          pose proof (trans _ x) as trans;
          simpl in *.

  {
    eapply trans;[|eauto].
    eapply trans;[eauto|].
    apply symm.
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }

  {
    eapply trans;[|eauto].
    apply symm.
    eapply trans;[exact ieqa|].
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2 : slow.

Lemma type_value_respecting_trans_per_bar_per_ffdefs2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> computes_to_valc lib T1 (mkc_free_from_defs A' B')
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_ffdefs ts) lib T2 T1 eq
    -> per_bar (per_ffdefs ts) lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_ffdefs in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  spcast; computes_to_eqval.

  exists A A1 B x1 eqa1; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans2; eauto; eauto 3 with slow));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq2; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq3 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' B D (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x z v)
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.
  pose proof (ieqa  _ e) as ieqa.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  simpl in *.
  eapply trans;[|eauto].
  apply symm.
  eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
  eapply trans;[eauto|]; apply symm;auto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq3 : slow.

Lemma in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar3 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' B D (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x z v)
    -> (per_ffdefs_eq_bar lib eqa1 u) <=2=> (per_ffdefs_eq_bar lib eqa1 z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.

  split; intro h; unfold per_ffdefs_eq_bar in *; exrepnd;
    exists bar; introv br xt; introv; pose proof (h0 _ br _ xt x) as h0;
      simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
        unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
          pose proof (ieqa  _ x) as ieqa;
          pose proof (resp  _ x) as resp;
          pose proof (symm  _ x) as symm;
          pose proof (trans _ x) as trans;
          simpl in *.

  {
    eapply trans;[|eauto].
    eapply trans;[eauto|].
    apply symm.
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }

  {
    eapply trans;[|eauto].
    apply symm.
    eapply trans;[exact ieqa|].
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar3 : slow.

Lemma per_ffdefs_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B equ (eqa : lib-per(lib,o)),
    computes_to_valc lib T1 (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T1 T2 equ
    -> per_ffdefs ts lib T2 T1 equ.
Proof.
  introv comp tspa per.

  unfold per_ffdefs in *; exrepnd.
  spcast; computes_to_eqval.
  exists A2 A x2 B eqa0; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq3; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar3; eauto; eauto 3 with slow.
Qed.

Lemma per_ffdefs_sym_rev {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B equ (eqa : lib-per(lib,o)),
    computes_to_valc lib T1 (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T2 T1 equ
    -> per_ffdefs ts lib T1 T2 equ.
Proof.
  introv comp tspa per.

  unfold per_ffdefs in *; exrepnd.
  spcast; computes_to_eqval.
  exists A A1 B x1 eqa0; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props4_in_ext_ext_sym_rev; eauto));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq2; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2; eauto; eauto 3 with slow.
Qed.

Lemma per_bar_per_ffdefs_sym {o} :
  forall (ts : cts(o)) lib T T' A B A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) lib T T' eq
    -> per_bar (per_ffdefs ts) lib T' T eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A B A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) lib T' T eq
    -> per_bar (per_ffdefs ts) lib T T' eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_sym_rev; try exact comp; eauto.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq4 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' A D (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z)
    -> in_ext_ext lib (fun lib' x => eqa2 lib' x z v)
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u v).
Proof.
  introv tsp its1 its2 ieqa1 ieqa2.

  dup its1 as resp.
  dup its1 as symm.
  dup its1 as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 in trans; eauto; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props4_trans_implies_eq_term_equals1 in tsp; eauto; eauto 3 with slow.

  clear ts A B C D its1 its2.

  introv.
  pose proof (tsp   _ e) as tsp.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  pose proof (ieqa1 _ e) as ieqa1.
  pose proof (ieqa2 _ e) as ieqa2.
  simpl in *.

  apply tsp in ieqa2; clear tsp.
  eapply trans; eauto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq4 : slow.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq5 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' A D (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z)
    -> in_ext_ext lib (fun lib' x => eqa2 lib' x z v)
    -> in_ext_ext lib (fun lib' x => eqa2 lib' x u v).
Proof.
  introv tsp its1 its2 ieqa1 ieqa2.

  dup its1 as resp.
  dup its1 as symm.
  dup its1 as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 in trans; eauto; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props4_trans_implies_eq_term_equals1 in tsp; eauto; eauto 3 with slow.

  clear ts A B C D its1 its2.

  introv.
  pose proof (tsp   _ e) as tsp.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  pose proof (ieqa1 _ e) as ieqa1.
  pose proof (ieqa2 _ e) as ieqa2.
  simpl in *.

  apply tsp in ieqa2; apply tsp; clear tsp.
  eapply trans; eauto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq5 : slow.

Lemma per_ffdefs_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A B A',
    computes_to_valc lib T (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T T2 eq2
    -> per_ffdefs ts lib T1 T eq1
    -> per_ffdefs ts lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists A1 A3 x1 x3 eqa0; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto. }
  { eapply in_ext_type_sys_props4_implies_ceq_change_eq4; eauto. }
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' A D (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u v)
    -> (per_ffdefs_eq_bar lib eqa2 u) <=2=> (per_ffdefs_eq_bar lib eqa2 v).
Proof.
  introv tsp its1 its2 ieqa1.

  dup its1 as resp.
  dup its1 as symm.
  dup its1 as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 in trans; eauto; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props4_trans_implies_eq_term_equals1 in tsp; eauto; eauto 3 with slow.

  clear ts A B C D its1 its2.

  split; intro h; unfold per_ffdefs_eq_bar in *; exrepnd;
    exists bar; introv br xt; introv; pose proof (h0 _ br _ xt x) as h0;
      simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
        unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
          pose proof (tsp   _ x) as tsp;
          pose proof (resp  _ x) as resp;
          pose proof (symm  _ x) as symm;
          pose proof (trans _ x) as trans;
          pose proof (ieqa1 _ x) as ieqa1;
          simpl in *;
          apply tsp in h0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5 : slow.

Lemma per_ffdefs_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A B A',
    computes_to_valc lib T (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T T2 eq2
    -> per_ffdefs ts lib T1 T eq1
    -> per_ffdefs ts lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists A1 A3 x1 x3 eqa1; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsa; eauto. }
  { eapply in_ext_type_sys_props4_implies_ceq_change_eq5; eauto. }
  { eapply eq_term_equals_trans;[eauto|]; apply eq_term_equals_sym.
    eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5; eauto. }
Qed.

Lemma per_ffdefs_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' B',
    computes_to_valc lib T (mkc_free_from_defs A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T T2 eq2
    -> per_ffdefs ts lib T1 T eq1
    -> per_ffdefs ts lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists A1 A3 x1 x3 eqa0; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto. }
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_type_sys_props4_implies_ceq_change_eq4; eauto. }
Qed.

Lemma per_ffdefs_trans4 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' B',
    computes_to_valc lib T (mkc_free_from_defs A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_ffdefs ts lib T T2 eq2
    -> per_ffdefs ts lib T1 T eq1
    -> per_ffdefs ts lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists A1 A3 x1 x3 eqa1; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto. }
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_type_sys_props4_implies_ceq_change_eq5; eauto. }
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply eq_term_equals_trans;[eauto|]; apply eq_term_equals_sym.
    eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5; eauto. }
Qed.

Lemma per_bar_per_ffdefs_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) lib T1 T eq1
    -> per_bar (per_ffdefs ts) lib T T2 eq2
    -> per_bar (per_ffdefs ts) lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) lib T1 T eq1
    -> per_bar (per_ffdefs ts) lib T T2 eq2
    -> per_bar (per_ffdefs ts) lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans3 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' B' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A' B')
    -> per_bar (per_ffdefs ts) lib T1 T eq1
    -> per_bar (per_ffdefs ts) lib T T2 eq2
    -> per_bar (per_ffdefs ts) lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans4 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' B' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A' B')
    -> per_bar (per_ffdefs ts) lib T1 T eq1
    -> per_bar (per_ffdefs ts) lib T T2 eq2
    -> per_bar (per_ffdefs ts) lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  eapply per_ffdefs_trans4; try exact comp; eauto.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq6 {o} :
  forall ts (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccequivc_ext lib u z
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts lib' B D (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u v)
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x u z).
Proof.
  introv tsp ceq1 ceq2 its ieqa.
  eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsp;[|eauto].
  clear ceq2.
  dup its as resp.
  dup its as symm.
  dup its as trans.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 in resp;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3  in symm;  eauto; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 in trans; eauto; eauto 3 with slow.

  clear ts A B C D its tsp.

  introv.
  pose proof (ieqa  _ e) as ieqa.
  pose proof (resp  _ e) as resp.
  pose proof (symm  _ e) as symm.
  pose proof (trans _ e) as trans.
  simpl in *.

  eapply resp; eauto 3 with slow.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_eq6 : slow.

Lemma per_ffdefs_eq_bar_symmetric {p} :
  forall lib (bar : BarLib lib) (eqa : lib-per(lib,p)) x1 t1 t2,
    all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t2 t1.
Proof.
  introv tes per.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *.
  exrepnd; exists (intersect_bars bar bar0); introv br ext; introv; simpl in *; exrepnd.
  pose proof (per0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as per0; simpl in *.
  pose proof (tes lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tes; simpl in *.
  repnd; dands; eauto 3 with slow.
Qed.

Lemma per_ffdefs_eq_bar_transitive {p} :
  forall lib (bar : BarLib lib) (eqa : lib-per(lib,p)) x1 t1 t2 t3,
    all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t2 t3
    -> per_ffdefs_eq_bar lib eqa x1 t1 t3.
Proof.
  introv teta pera perb.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *.
  exrepnd.
  exists (intersect3bars bar bar0 bar1); introv br ext; introv.
  simpl in *; exrepnd.

  pose proof (pera0 lib3 br5 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br2) x) as q; simpl in q.
  pose proof (perb0 lib0 br4 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br6) x) as h; simpl in h.
  pose proof (teta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as teta; simpl in *.
  repnd; dands; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_axiom {o} :
  forall lib (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> computes_to_valc lib T mkc_axiom
    -> ccomputes_to_valc lib T' mkc_axiom.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_axiom in ceq';[|eauto]; exrepnd; auto.
Qed.
Hint Resolve ccequivc_ext_axiom : slow.

Lemma per_ffdefs_eq_bar_cequiv {p} :
  forall lib (bar1 : BarLib lib) (eqa : lib-per(lib,p)) x1 t1 t2,
    all_in_bar_ext bar1 (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> all_in_bar_ext bar1 (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar1 (fun lib' x => term_equality_transitive (eqa lib' x))
    -> ccequivc_ext lib t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t1 t1
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2.
Proof.
  introv tera tesa teta ceq per.

  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *; exrepnd.
  exists (intersect_bars bar1 bar).
  introv br ext; introv; simpl in *; exrepnd.

  pose proof (tera _ br0 lib'0 (lib_extends_trans ext br3) x) as tera; simpl in *.
  pose proof (per0 _ br2 lib'0 (lib_extends_trans ext br1) x) as per0; simpl in *.
  pose proof (teta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as teta; simpl in *.
  pose proof (tesa lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tesa; simpl in *.
  apply (lib_extends_preserves_ccequivc_ext _ lib'0) in ceq; eauto 4 with slow;[].
  spcast.

  repnd; dands; uncast; eauto 3 with slow.
Qed.
