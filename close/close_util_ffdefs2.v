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


Lemma in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals5 {o} :
  forall ts uk lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts uk lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib' A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals5 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals5 {o} :
  forall ts uk lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts uk lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib' A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals5 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals5 {o} :
  forall ts uk lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts uk lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib' A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals5 : slow.

Lemma implies_eq_term_equals_per_ffdefs_bar2 {p} :
  forall lib (eqa1 eqa2 : lib-per(lib,p)) t1 t2,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa1 lib' x))
    -> in_open_bar_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> ccequivc_ext lib t1 t2
    -> (per_ffdefs_eq_bar lib eqa1 t1) <=2=> (per_ffdefs_eq_bar lib eqa2 t2).
Proof.
  introv trans sym resp eqta ceq ; introv.
  unfold per_ffdefs_eq_bar; split; introv h; exrepnd;
      eapply in_open_bar_ext_comb; try exact eqta; clear eqta;
        eapply in_open_bar_ext_pres; eauto; clear h; introv h eqta;
          unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow.
  eapply ex_nodefsc_change_per_ceq; try exact h; eauto 3 with slow.
  apply eq_term_equals_sym; eauto 3 with slow.
Qed.

Lemma per_bar_per_ffdefs_implies_eq_term_equals_per_ffdefs_eq_bar {o} :
  forall (ts : cts(o)) uk lib T T' eq (eqa : lib-per(lib,o)) A a A',
    ccomputes_to_valc_ext lib T (mkc_free_from_defs A a)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_bar (per_ffdefs ts) uk lib T T' eq
    -> eq <=2=> (per_ffdefs_eq_bar lib eqa a).
Proof.
  introv comp tsa per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_ffdefs_eq_bar, per_ffdefs_eq.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    unfold per_ffdefs in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.
    apply per0 in h; clear per0.

    unfold per_ffdefs_eq_bar, per_ffdefs in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow;[].

    unfold per_ffdefs_eq in *.
    repnd; dands; tcsp; eauto 3 with slow.

    eapply ex_nodefsc_change_per_ceq; try exact h;
      try (apply ccequivc_ext_sym; eapply lib_extends_preserves_ccequivc_ext; try exact ceq; try exact e0);
      eauto 3 with slow.

    { eapply in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals5 in per3; try exact tsa; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals5 in per3; try exact ceq0; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals5 in per3; try exact ceq0; eauto 3 with slow. }
    { pose proof (eqas _ e0) as eqas; simpl in *; eapply eq_term_equals_trans;[eauto|]; apply lib_per_cond. }

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_ffdefs in per1; exrepnd.
    apply per0; clear per0.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow.

    apply (sub_per_per_ffdefs_eq_bar _ _ e) in h.
    eapply implies_eq_term_equals_per_ffdefs_bar2; try exact h; simpl; eauto 3 with slow.
Qed.

Lemma per_bar_per_ffdefs_implies_close {o} :
  forall (ts : cts(o)) uk lib T T' eq,
    per_bar (per_ffdefs (close ts)) uk lib T T' eq
    -> close ts uk lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.
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
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> ccomputes_to_valc_ext lib T' (mkc_free_from_defs A B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq1 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' B D (eqa1 lib' x))
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
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' B D (eqa1 lib' x))
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
      eapply in_open_bar_ext_pres; try exact h; clear h;
        introv h; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
          unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
            pose proof (ieqa  _ e) as ieqa;
            pose proof (resp  _ e) as resp;
            pose proof (symm  _ e) as symm;
            pose proof (trans _ e) as trans;
            simpl in *.

  {
    eapply trans;[|eauto].
    apply symm.
    eapply resp;[|apply ccequivc_ext_sym;eauto 3 with slow].
    eapply trans;[eauto|]; apply symm;auto.
  }
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar1 : slow.

Lemma type_value_respecting_trans_per_bar_per_ffdefs1 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A b A' b' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_free_from_defs A' b')
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A b)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib b b'
    -> per_bar (per_ffdefs ts) uk lib T1 T2 eq
    -> per_bar (per_ffdefs ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_ffdefs in *; exrepnd.

  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.

  exists A A2 b x2 eqa1; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq1; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar1; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq2 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' D B (eqa1 lib' x))
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
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' D B (eqa1 lib' x))
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
      eapply in_open_bar_ext_pres; try exact h; clear h; introv h;
        unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
        unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
          pose proof (ieqa  _ e) as ieqa;
          pose proof (resp  _ e) as resp;
          pose proof (symm  _ e) as symm;
          pose proof (trans _ e) as trans;
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
  forall uk lib (ts : cts(o)) T T1 T2 A B A' B' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_free_from_defs A' B')
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_ffdefs ts) uk lib T2 T1 eq
    -> per_bar (per_ffdefs ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_ffdefs in *; exrepnd.

  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.

  exists A A1 B x1 eqa1; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans2; eauto; eauto 3 with slow));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq2; eauto; eauto 3 with slow)).

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq3 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' B D (eqa1 lib' x))
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
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' B D (eqa1 lib' x))
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
      eapply in_open_bar_ext_pres; try exact h; clear h; introv h;
        simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
          unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
            pose proof (ieqa  _ e) as ieqa;
            pose proof (resp  _ e) as resp;
            pose proof (symm  _ e) as symm;
            pose proof (trans _ e) as trans;
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
  forall ts uk lib (T1 T2 : @CTerm o) A A' B equ (eqa : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T1 T2 equ
    -> per_ffdefs ts uk lib T2 T1 equ.
Proof.
  introv comp tspa per.

  unfold per_ffdefs in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  exists A2 A x2 B eqa0; dands; spcast; auto.

  { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tspa; eauto; eauto 3 with slow. }

  { eapply in_ext_type_sys_props4_implies_ceq_change_eq3; eauto; eauto 3 with slow.
    eapply in_ext_type_sys_props4_implies_ceq_change_eq1; eauto; eauto 3 with slow. }

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar3; eauto; eauto 3 with slow.
Qed.

Lemma per_ffdefs_sym_rev {o} :
  forall ts uk lib (T1 T2 : @CTerm o) A A' B equ (eqa : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T2 T1 equ
    -> per_ffdefs ts uk lib T1 T2 equ.
Proof.
  introv comp tspa per.

  unfold per_ffdefs in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  exists A A1 B x1 eqa0; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props4_in_ext_ext_sym_rev; eauto));
    try (complete (eapply in_ext_type_sys_props4_implies_ceq_change_eq2; eauto; eauto 3 with slow)).

  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tspa; eauto; eauto 3 with slow. }

  eapply eq_term_equals_trans;[eauto|];[];apply eq_term_equals_sym.
  eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar2; eauto; eauto 3 with slow.
Qed.

Lemma per_bar_per_ffdefs_sym {o} :
  forall (ts : cts(o)) uk lib T T' A B A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) uk lib T T' eq
    -> per_bar (per_ffdefs ts) uk lib T' T eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_sym_rev {o} :
  forall (ts : cts(o)) uk lib T T' A B A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) uk lib T' T eq
    -> per_bar (per_ffdefs ts) uk lib T T' eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_sym_rev; try exact comp; eauto.
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_eq4 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' A D (eqa2 lib' x))
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
  forall ts uk (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' A D (eqa2 lib' x))
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

Lemma in_ext_type_sys_props4_implies_ceq_change_eq6 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 : lib-per(lib,o)) u v z,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccequivc_ext lib u z
    -> ccequivc_ext lib A B
    -> in_ext_ext lib (fun lib' x => ts uk lib' B D (eqa1 lib' x))
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

Lemma per_ffdefs_trans1 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A B A',
    ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T T2 eq2
    -> per_ffdefs ts uk lib T1 T eq1
    -> per_ffdefs ts uk lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0; repnd.

  exists A1 A3 x1 x3 eqa0; dands; spcast; auto; eauto 3 with slow.

  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { eapply in_ext_type_sys_props4_implies_ceq_change_eq4; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

     { eapply in_ext_type_sys_props4_implies_ceq_change_eq3;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
Qed.

Lemma in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5 {o} :
  forall ts uk (lib : @library o) A B C D (eqa eqa1 eqa2 : lib-per(lib,o)) u v,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' B A (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts uk lib' A D (eqa2 lib' x))
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
      eapply in_open_bar_ext_pres; try exact h; clear h; introv h;
        simpl in *; unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow;
          unfold ex_nodefsc in *; exrepnd; exists u0; dands; auto;
            pose proof (tsp   _ e) as tsp;
            pose proof (resp  _ e) as resp;
            pose proof (symm  _ e) as symm;
            pose proof (trans _ e) as trans;
            pose proof (ieqa1 _ e) as ieqa1;
            simpl in *; apply tsp in h3; apply tsp; eauto.
Qed.
Hint Resolve in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5 : slow.

Lemma per_ffdefs_trans2 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A B A',
    ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T T2 eq2
    -> per_ffdefs ts uk lib T1 T eq1
    -> per_ffdefs ts uk lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0; repnd.
  exists A1 A3 x1 x3 eqa1; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsa; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { eapply in_ext_type_sys_props4_implies_ceq_change_eq5; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

    { eapply in_ext_type_sys_props4_implies_ceq_change_eq3;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { eapply eq_term_equals_trans;[eauto|]; apply eq_term_equals_sym.
    eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

    { eapply in_ext_type_sys_props4_implies_ceq_change_eq2 in perb4;
        try exact tsa; try exact perb3; try apply ccequivc_ext_sym; eauto 3 with slow.
      eapply in_ext_type_sys_props4_implies_ceq_change_eq2;
        try exact tsa; try exact perb3; eauto; eauto with slow. }
  }
Qed.

Lemma per_ffdefs_trans3 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' B',
    ccomputes_to_valc_ext lib T (mkc_free_from_defs A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T T2 eq2
    -> per_ffdefs ts uk lib T1 T eq1
    -> per_ffdefs ts uk lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0; repnd.

  exists A1 A3 x1 x3 eqa0; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto.

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_type_sys_props4_implies_ceq_change_eq4; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

    { eapply in_ext_type_sys_props4_implies_ceq_change_eq2 in perb4;
        try exact tsa; try exact perb3; try apply ccequivc_ext_sym; eauto 3 with slow. }
 }
Qed.

Lemma per_ffdefs_trans4 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' B',
    ccomputes_to_valc_ext lib T (mkc_free_from_defs A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib T T2 eq2
    -> per_ffdefs ts uk lib T1 T eq1
    -> per_ffdefs ts uk lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_ffdefs in *; exrepnd.
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0; repnd.

  exists A1 A3 x1 x3 eqa1; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto.

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_type_sys_props4_implies_ceq_change_eq5; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

    { eapply in_ext_type_sys_props4_implies_ceq_change_eq2 in perb4;
        try exact tsa; try exact perb3; try apply ccequivc_ext_sym; eauto 3 with slow. }
  }

  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply eq_term_equals_trans;[eauto|]; apply eq_term_equals_sym.
    eapply in_ext_type_sys_props4_implies_ceq_change_term_per_ffdefs_eq_bar5; eauto.

    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }

    { eapply in_ext_type_sys_props4_implies_ceq_change_eq2 in perb4;
        try exact tsa; try exact perb3; try apply ccequivc_ext_sym; eauto 3 with slow.
      eapply in_ext_type_sys_props4_implies_ceq_change_eq2;
        try exact tsa; try exact perb3; eauto; eauto with slow. }
  }
Qed.

Lemma per_bar_per_ffdefs_trans1 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A B A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) uk lib T1 T eq1
    -> per_bar (per_ffdefs ts) uk lib T T2 eq2
    -> per_bar (per_ffdefs ts) uk lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans2 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A B A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A B)
    -> per_bar (per_ffdefs ts) uk lib T1 T eq1
    -> per_bar (per_ffdefs ts) uk lib T T2 eq2
    -> per_bar (per_ffdefs ts) uk lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans3 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A A' B' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A' B')
    -> per_bar (per_ffdefs ts) uk lib T1 T eq1
    -> per_bar (per_ffdefs ts) uk lib T T2 eq2
    -> per_bar (per_ffdefs ts) uk lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_ffdefs_trans4 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A A' B' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A' B')
    -> per_bar (per_ffdefs ts) uk lib T1 T eq1
    -> per_bar (per_ffdefs ts) uk lib T T2 eq2
    -> per_bar (per_ffdefs ts) uk lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; try exact pera1; clear pera1.
  introv pera1 perb1.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_ffdefs_trans4; try exact comp; eauto.
Qed.

Lemma per_ffdefs_eq_bar_symmetric {p} :
  forall lib (eqa : lib-per(lib,p)) x1 t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t2 t1.
Proof.
  introv tes per.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *.
  eapply in_open_bar_ext_comb; try exact per; clear per.
  eapply in_open_bar_ext_pres; try exact tes; clear tes.
  introv tes per; repnd; dands; tcsp.
Qed.

Lemma per_ffdefs_eq_bar_transitive {p} :
  forall lib (eqa : lib-per(lib,p)) x1 t1 t2 t3,
    in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t2 t3
    -> per_ffdefs_eq_bar lib eqa x1 t1 t3.
Proof.
  introv teta pera perb.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *.
  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  eapply in_open_bar_ext_pres; try exact teta; clear teta.
  introv teta perb pera; repnd; dands; tcsp.
Qed.

Lemma ccequivc_ext_axiom {o} :
  forall lib (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T mkc_axiom
    -> ccomputes_to_valc_ext lib T' mkc_axiom.
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_axiom : slow.

Lemma per_ffdefs_eq_bar_cequiv {p} :
  forall lib (eqa : lib-per(lib,p)) x1 t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> ccequivc_ext lib t1 t2
    -> per_ffdefs_eq_bar lib eqa x1 t1 t1
    -> per_ffdefs_eq_bar lib eqa x1 t1 t2.
Proof.
  introv tera tesa teta ceq per.

  unfold per_ffdefs_eq_bar, per_ffdefs_eq in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact per; clear per.
  eapply in_open_bar_ext_comb; try exact tera; clear tera.
  eapply in_open_bar_ext_comb; try exact teta; clear teta.
  eapply in_open_bar_ext_pres; try exact tesa; clear tesa.
  introv tesa peta tera per; repnd; dands; tcsp; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_ffdefs {o} :
  forall ts uk lib T T' eq A B u v (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_free_from_defs A u)
    -> T' ===>( lib) (mkc_free_from_defs B v)
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => eqa lib' x u v)
    -> (eq <=2=> (per_ffdefs_eq_bar lib eqa u))
    -> type_equality_respecting_trans1 (close ts) uk lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa  eqau eqiff.
  introv h ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_ffdefs in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs1;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_ffdefs in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs1;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_ffdefs in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs2;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_ffdefs in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs2;
      try exact h; try exact c2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_ffdefs3 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A A' u (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A u)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_ffdefs ts) uk lib T T1 eq
    -> per_bar (per_ffdefs ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_ffdefs in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.

  exists A A2 u x2 eqa1; dands; spcast; auto; eauto 3 with slow.

  { pose proof (in_ext_ext_type_sys_props_type_value_respecting_trans1
                  ts uk lib' A A1 A2 A' (raise_lib_per eqa e) eqa1) as w; tcsp. }

  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 2 with slow. }
Qed.

Lemma implies_type_value_respecting_trans2_per_ffdefs {o} :
  forall ts uk lib T T' eq A B u v (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_free_from_defs A u)
    -> T' ===>( lib) (mkc_free_from_defs B v)
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => eqa lib' x u v)
    -> (eq <=2=> (per_ffdefs_eq_bar lib eqa u))
    -> type_equality_respecting_trans2 (close ts) uk lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa eqau eqiff.
  introv h cl ceq.
  repndors; subst.

  {
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs3;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs3;
      try exact c1; try exact tsa; try exact tsb; eauto 3 with slow.
    eapply per_bar_per_ffdefs_sym_rev; try exact c1; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_ffdefs_implies_close.
    eapply type_value_respecting_trans_per_bar_per_ffdefs3;
      try exact c2; try exact tsa'; try exact tsb'; eauto 3 with slow.
    eapply per_bar_per_ffdefs_sym_rev; try exact c2; try exact tsa'; try exact tsb'; auto.
  }
Qed.
