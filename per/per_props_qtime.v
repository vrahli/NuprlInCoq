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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export per_props_util2.
Require Export per_props_fam2.
Require Export per_props_tacs.


Lemma type_extensionality_per_qtime_nuprl {o} :
  @type_extensionality o (per_qtime nuprl).
Proof.
  introv per e.
  unfold per_qtime in *; exrepnd.
  exists eqa A B; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_qtime_nuprl : slow.

Lemma type_extensionality_per_qtime_nuprli {o} :
  forall i, @type_extensionality o (per_qtime (nuprli i)).
Proof.
  introv per e.
  unfold per_qtime in *; exrepnd.
  exists eqa A B; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_qtime_nuprli : slow.

Lemma uniquely_valued_per_qtime_nuprl {o} :
  @uniquely_valued o (per_qtime nuprl).
Proof.
  introv pera perb.
  unfold per_qtime in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq.
  apply cequivc_ext_mkc_qtime_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_qtime_eq_bar.
  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprl_refl in pera3.
  apply nuprl_refl in perb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_qtime_nuprl : slow.

Lemma uniquely_valued_per_qtime_nuprli {o} :
  forall i, @uniquely_valued o (per_qtime (nuprli i)).
Proof.
  introv pera perb.
  unfold per_qtime in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq.
  apply cequivc_ext_mkc_qtime_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprli_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_qtime_eq_bar.
  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprli_refl in pera3.
  apply nuprli_refl in perb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_qtime_nuprli : slow.

Lemma local_per_bar_per_qtime_nuprl {o} :
  @local_ts o (per_bar (per_qtime nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_qtime_nuprl : slow.

Lemma local_per_bar_per_qtime_nuprli {o} :
  forall i, @local_ts o (per_bar (per_qtime (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_qtime_nuprli : slow.

Lemma dest_nuprl_per_qtime_l {o} :
  forall (ts : cts(o)) lib T A T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca; apply reca; tcsp; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_qtime_l {o} :
  forall i (ts : cts(o)) lib T A T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca; apply reca; tcsp; eauto 3 with slow.
Qed.

Lemma dest_nuprl_qtime {o} :
  forall (lib : @library o) A B eq,
    nuprl lib (mkc_qtime A) (mkc_qtime B) eq
    -> per_bar (per_qtime nuprl) lib (mkc_qtime A) (mkc_qtime B) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_qtime_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_qtime {o} :
  forall i (lib : @library o) A B eq,
    nuprli i lib (mkc_qtime A) (mkc_qtime B) eq
    -> per_bar (per_qtime (nuprli i)) lib (mkc_qtime A) (mkc_qtime B) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_qtime_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_qtime2 {o} :
  forall lib (eq : per(o)) A B,
    nuprl lib (mkc_qtime A) (mkc_qtime B) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_qtime_eq_bar_lib_per lib eqa)))
        # in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x)).
Proof.
  introv u.
  apply dest_nuprl_qtime in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A B (eqa0 lib'' y))
               # (eqa lib' x) <=2=> (per_qtime_eq_bar lib' eqa0) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_qtime in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.

  exists (fun_lib_dep_eqa Feqa).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply implies_eq_term_equals_per_qtime_eq_bar.
    introv; simpl; unfold raise_ext_per; split; intro q.

    { exists lib' e lib'0 e0 z e2; auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    pose proof (h0 _ e2) as h0; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e3.
    eapply nuprl_uniquely_valued in h0; try exact e3; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e2.
    eapply nuprl_uniquely_valued in h0; try exact e2; apply h0; auto.
  }
Qed.

Lemma dest_nuprli_qtime2 {o} :
  forall i lib (eq : per(o)) A B,
    nuprli i lib (mkc_qtime A) (mkc_qtime B) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_qtime_eq_bar_lib_per lib eqa)))
        # in_open_bar_ext lib (fun lib' x => nuprli i lib' A B (eqa lib' x)).
Proof.
  introv u.
  apply dest_nuprli_qtime in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A B (eqa0 lib'' y))
               # (eqa lib' x) <=2=> (per_qtime_eq_bar lib' eqa0) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_qtime in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.

  exists (fun_lib_dep_eqa Feqa).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply implies_eq_term_equals_per_qtime_eq_bar.
    introv; simpl; unfold raise_ext_per; split; intro q.

    { exists lib' e lib'0 e0 z e2; auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    pose proof (h0 _ e2) as h0; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e3.
    eapply nuprli_uniquely_valued in h0; try exact e3; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e2.
    eapply nuprli_uniquely_valued in h0; try exact e2; apply h0; auto.
  }
Qed.




Lemma tequality_mkc_qtime {p} :
  forall lib (A B : @CTerm p),
    tequality lib (mkc_qtime A) (mkc_qtime B)
    <=> tequality lib A B.
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_qtime2 in teq0; exrepnd.
    dands; eauto 3 with slow.

  - unfold tequality in teq; exrepnd.
    rename eq into eqa.

    pose proof (nuprl_monotone_func lib A B eqa teq0) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_qtime_eq_bar lib eqa'); apply CL_qtime; unfold per_qtime.
    exists eqa' A B; sp; spcast; eauto 3 with slow.
    introv; apply tya0.
Qed.

Lemma per_bar_eq_per_qtime_eq_bar_lib_per_iff {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) p1 p2,
    (per_bar_eq lib (per_qtime_eq_bar_lib_per lib eqa) p1 p2)
      <=>
      in_open_bar_ext
          lib
          (fun lib' x => per_qtime_eq lib' (eqa lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    introv.
    eapply implies_eq_term_equals_per_qtime_eq; try exact h;
      try (apply lib_per_cond).

  - apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    eapply implies_eq_term_equals_per_qtime_eq; try exact h;
      try (apply lib_per_cond).
Qed.

Lemma equality_mkc_qtime {p} :
  forall lib (t1 t2 A : @CTerm p),
    equality lib t1 t2 (mkc_qtime A)
    <=> (type lib A
         # in_open_bar lib (fun lib => {a1, a2 : CTerm
             , ccequivc lib t1 a1
             # ccequivc lib t2 a2
             # ccequivc_ext lib t1 t2
             # equality lib a1 a2 A})).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_qtime2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.
    dands; eauto 3 with slow;[].

    apply per_bar_eq_per_qtime_eq_bar_lib_per_iff in e0; exrepnd.
    eapply in_open_bar_comb2; try exact e2; clear e2.
    eapply in_open_bar_ext_pres; try exact e0; clear e0; introv e0 e2.

    unfold per_qtime_eq in *; exrepnd.
    eexists; eexists; dands; eauto.
    apply (equality_eq1 lib' A A x y (eqa lib' e)); auto.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.
    pose proof (nuprl_monotone_func lib A A eqa e1) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_qtime_eq_bar lib eqa'); dands.

    {
      apply CL_qtime; unfold per_qtime.
      exists eqa' A A; dands; spcast; eauto 3 with slow.
      introv; apply tya0.
    }

    unfold per_qtime_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_comb2; eauto; clear e.
    eapply in_ext_ext_implies_in_open_bar_ext; introv h; exrepnd.
    unfold per_qtime_eq.
    exists a1 a2; dands; auto.
    apply (equality_eq1 lib' A A a1 a2 (eqa' lib' e)); eauto 3 with slow.
    apply tya0.
Qed.
