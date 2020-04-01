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


Require Export per_props_util.
Require Export per_props_util2.
Require Export per_props_tacs.
Require Export per_props_fam2.
Require Export csubst6.



Lemma type_extensionality_per_ffdefs_nuprl {o} :
  @type_extensionality o (per_ffdefs nuprl).
Proof.
  introv per e.
  unfold per_ffdefs in *; exrepnd.
  exists A1 A2 x1 x2 eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_ffdefs_nuprl : slow.

Lemma type_extensionality_per_ffdefs_nuprli {o} :
  forall i, @type_extensionality o (per_ffdefs (nuprli i)).
Proof.
  introv per e.
  unfold per_ffdefs in *; exrepnd.
  exists A1 A2 x1 x2 eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_ffdefs_nuprli : slow.

Lemma uniquely_valued_per_ffdefs_nuprl {o} :
  @uniquely_valued o (per_ffdefs nuprl).
Proof.
  introv pera perb.
  unfold per_ffdefs in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  computes_to_eqval_ext.
  hide_hyp perb1.
  apply cequivc_ext_mkc_free_from_defs_right in ceq1; repnd.

  apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  eapply nuprl_value_respecting_left in perb3;[|eapply lib_extends_preserves_ccequivc_ext; eauto].
  apply nuprl_refl in pera3.
  apply nuprl_refl in perb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_ffdefs_nuprl : slow.

Lemma uniquely_valued_per_ffdefs_nuprli {o} :
  forall i, @uniquely_valued o (per_ffdefs (nuprli i)).
Proof.
  introv pera perb.
  unfold per_ffdefs in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  spcast.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_free_from_defs_right in ceq; repnd.
  computes_to_eqval_ext.
  hide_hyp perb1.
  apply cequivc_ext_mkc_free_from_defs_right in ceq1; repnd.

  apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  eapply nuprli_value_respecting_left in perb3;[|eapply lib_extends_preserves_ccequivc_ext; eauto].
  apply nuprli_refl in pera3.
  apply nuprli_refl in perb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_ffdefs_nuprli : slow.

Lemma local_per_bar_per_ffdefs_nuprl {o} :
  @local_ts o (per_bar (per_ffdefs nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_ffdefs_nuprl : slow.

Lemma local_per_bar_per_ffdefs_nuprli {o} :
  forall i, @local_ts o (per_bar (per_ffdefs (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_ffdefs_nuprli : slow.

Lemma dest_nuprl_per_ffdefs_l {o} :
  forall (ts : cts(o)) uk lib T A f T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A f)
    -> close ts uk lib T T' eq
    -> per_bar (per_ffdefs (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  repeat (autodimp reca hyp); eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_ffdefs_l {o} :
  forall i (ts : cts(o)) uk lib T A f T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A f)
    -> close ts uk lib T T' eq
    -> per_bar (per_ffdefs (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  repeat (autodimp reca hyp); eauto 3 with slow.
Qed.

Lemma iscvalue_ffdefs {o} :
  forall (A f : @CTerm o), iscvalue (mkc_free_from_defs A f).
Proof.
  introv.
  split; eauto 3 with slow.
  destruct_cterms; simpl; auto.
Qed.
Hint Resolve iscvalue_ffdefs : slow.

Lemma dest_nuprl_ffdefs {o} :
  forall uk (lib : @library o) A f B g eq,
    nuprl uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    -> per_bar (per_ffdefs nuprl) uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_ffdefs_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_ffdefs {o} :
  forall i uk (lib : @library o) A f B g eq,
    nuprli i uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    -> per_bar (per_ffdefs (nuprli i)) uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_ffdefs_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma nuprl_per_value_respecting_left {p} :
  forall uk lib (t1 t2 a b c : @CTerm p) eq,
    nuprl uk lib t1 t2 eq
    -> eq a b
    -> ccequivc_ext lib a c
    -> eq c b.
Proof.
  introv h q ceq.
  nts.
  pose proof (nts_tev uk lib t1 eq) as w1.
  autodimp w1 hyp; eauto 3 with slow;[].
  pose proof (nts_tet uk lib t1 t2 eq) as w2.
  autodimp w2 hyp; eauto 3 with slow;[].
  pose proof (nts_tes uk lib t1 t2 eq) as w3.
  autodimp w3 hyp; eauto 3 with slow;[].
  eapply w2;[|eauto]; apply w3.
  eapply w1; auto.
  eapply w2; eauto.
Qed.

Lemma nuprl_per_value_respecting_right {p} :
  forall uk lib (t1 t2 a b c : @CTerm p) eq,
    nuprl uk lib t1 t2 eq
    -> eq a b
    -> ccequivc_ext lib b c
    -> eq a c.
Proof.
  introv h q ceq.
  nts.
  pose proof (nts_tev uk lib t1 eq) as w1.
  autodimp w1 hyp; eauto 3 with slow;[].
  pose proof (nts_tet uk lib t1 t2 eq) as w2.
  autodimp w2 hyp; eauto 3 with slow;[].
  pose proof (nts_tes uk lib t1 t2 eq) as w3.
  autodimp w3 hyp; eauto 3 with slow;[].
  eapply w2;[eauto|]; apply w3.
  eapply w3; auto.
  apply w1; auto.
  eapply w2; eauto.
Qed.

Lemma nuprli_per_value_respecting_left {p} :
  forall i uk lib (t1 t2 a b c : @CTerm p) eq,
    nuprli i uk lib t1 t2 eq
    -> eq a b
    -> ccequivc_ext lib a c
    -> eq c b.
Proof.
  introv h q ceq.
  ntsi.
  pose proof (nts_tev uk lib t1 eq) as w1.
  autodimp w1 hyp; eauto 3 with slow;[].
  pose proof (nts_tet uk lib t1 t2 eq) as w2.
  autodimp w2 hyp; eauto 3 with slow;[].
  pose proof (nts_tes uk lib t1 t2 eq) as w3.
  autodimp w3 hyp; eauto 3 with slow;[].
  eapply w2;[|eauto]; apply w3.
  eapply w1; auto.
  eapply w2; eauto.
Qed.

Lemma nuprli_per_value_respecting_right {p} :
  forall i uk lib (t1 t2 a b c : @CTerm p) eq,
    nuprli i uk lib t1 t2 eq
    -> eq a b
    -> ccequivc_ext lib b c
    -> eq a c.
Proof.
  introv h q ceq.
  ntsi.
  pose proof (nts_tev uk lib t1 eq) as w1.
  autodimp w1 hyp; eauto 3 with slow;[].
  pose proof (nts_tet uk lib t1 t2 eq) as w2.
  autodimp w2 hyp; eauto 3 with slow;[].
  pose proof (nts_tes uk lib t1 t2 eq) as w3.
  autodimp w3 hyp; eauto 3 with slow;[].
  eapply w2;[eauto|]; apply w3.
  eapply w3; auto.
  apply w1; auto.
  eapply w2; eauto.
Qed.

Lemma in_ext_ext_nuprl_per_value_respecting_left {o} :
  forall uk lib (t1 t2 a b c : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprl uk lib t1 t2 (eq lib x))
    -> in_ext_ext lib (fun lib x => eq lib x a b)
    -> ccequivc_ext lib a c
    -> in_ext_ext lib (fun lib x => eq lib x c b).
Proof.
  introv h p ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  pose proof (p _ e) as p; simpl in p.
  eapply nuprl_per_value_respecting_left; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprl_per_value_respecting_right {o} :
  forall uk lib (t1 t2 a b c : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprl uk lib t1 t2 (eq lib x))
    -> in_ext_ext lib (fun lib x => eq lib x a b)
    -> ccequivc_ext lib b c
    -> in_ext_ext lib (fun lib x => eq lib x a c).
Proof.
  introv h p ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  pose proof (p _ e) as p; simpl in p.
  eapply nuprl_per_value_respecting_right; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprli_per_value_respecting_left {o} :
  forall i uk lib (t1 t2 a b c : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprli i uk lib t1 t2 (eq lib x))
    -> in_ext_ext lib (fun lib x => eq lib x a b)
    -> ccequivc_ext lib a c
    -> in_ext_ext lib (fun lib x => eq lib x c b).
Proof.
  introv h p ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  pose proof (p _ e) as p; simpl in p.
  eapply nuprli_per_value_respecting_left; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprli_per_value_respecting_right {o} :
  forall i uk lib (t1 t2 a b c : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprli i uk lib t1 t2 (eq lib x))
    -> in_ext_ext lib (fun lib x => eq lib x a b)
    -> ccequivc_ext lib b c
    -> in_ext_ext lib (fun lib x => eq lib x a c).
Proof.
  introv h p ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  pose proof (p _ e) as p; simpl in p.
  eapply nuprli_per_value_respecting_right; eauto; eauto 3 with slow.
Qed.

Lemma dest_nuprl_ffdefs2 {o} :
  forall uk lib (eq : per(o)) A f B g,
    nuprl uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_ffdefs_eq_bar_lib_per lib eqa f)))
        # in_open_bar_ext lib (fun lib' x => nuprl uk lib' A B (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => eqa lib' x f g).
Proof.
  introv u.
  apply dest_nuprl_ffdefs in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl uk lib'' A B (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => eqa0 lib'' y f g)
               # (eqa lib' x) <=2=> (per_ffdefs_eq_bar lib' eqa0 f) })) as e.
  {
    eapply in_open_bar_ext_pres; try exact u1; clear u1; introv u1.
    unfold per_ffdefs in *; exrepnd.
    spcast.
    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    exists eqa0; dands; auto.
    { eapply in_ext_ext_nuprl_per_value_respecting_left; eauto;[|apply ccequivc_ext_sym;eauto].
      eapply in_ext_ext_nuprl_per_value_respecting_right; eauto.
      apply ccequivc_ext_sym;eauto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;
      [apply implies_eq_term_equals_per_ffdefs_eq_bar;
       try apply ccequivc_ext_sym;eauto;eauto 3 with slow|].
    eapply eq_term_equals_trans;
      [|apply implies_eq_term_equals_per_ffdefs_eq_bar;
        try apply ccequivc_ext_sym;eauto;eauto 3 with slow].
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
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
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro q.

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

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto.
  }
Qed.

Lemma dest_nuprli_ffdefs2 {o} :
  forall i uk lib (eq : per(o)) A f B g,
    nuprli i uk lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_ffdefs_eq_bar_lib_per lib eqa f)))
        # in_open_bar_ext lib (fun lib' x => nuprli i uk lib' A B (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => eqa lib' x f g).
Proof.
  introv u.
  apply dest_nuprli_ffdefs in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i uk lib'' A B (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => eqa0 lib'' y f g)
               # (eqa lib' x) <=2=> (per_ffdefs_eq_bar lib' eqa0 f) })) as e.
  {
    eapply in_open_bar_ext_pres; try exact u1; clear u1; introv u1.
    unfold per_ffdefs in *; exrepnd.
    spcast.
    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    exists eqa0; dands; auto.
    { eapply in_ext_ext_nuprli_per_value_respecting_left; eauto;[|apply ccequivc_ext_sym;eauto].
      eapply in_ext_ext_nuprli_per_value_respecting_right; eauto.
      apply ccequivc_ext_sym;eauto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;
      [apply implies_eq_term_equals_per_ffdefs_eq_bar;
       try apply ccequivc_ext_sym;eauto;eauto 3 with slow|].
    eapply eq_term_equals_trans;
      [|apply implies_eq_term_equals_per_ffdefs_eq_bar;
        try apply ccequivc_ext_sym;eauto;eauto 3 with slow].
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
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
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro q.

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

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto.
  }
Qed.

Lemma per_bar_eq_per_ffdefs_eq_bar_lib_per_iff {o} :
  forall {lib} (eqa : lib-per(lib,o)) f p1 p2,
    (per_bar_eq lib (per_ffdefs_eq_bar_lib_per lib eqa f) p1 p2)
      <=>
      in_open_bar_ext
          lib
          (fun lib' x => per_ffdefs_eq lib' (eqa lib' x) f p1 p2).
Proof.
  introv; split; intro h.

  - apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    introv.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h;
      try (apply lib_per_cond).

  - apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h;
      try (apply lib_per_cond).
Qed.

Definition ex_nodefsc_eq {o} uk (lib : library) (t T : @CTerm o) :=
  {u : @CTerm o , equality uk lib t u T # nodefsc u}.

Definition ex_nodefsc_eq_bar {o} uk (lib : library) (t T : @CTerm o) :=
  in_open_bar lib (fun lib' => ex_nodefsc_eq uk lib' t T).

Lemma equality_in_mkc_ffdefs {p} :
  forall uk lib (t1 t2 T t : @CTerm p),
    equality uk lib t1 t2 (mkc_free_from_defs T t)
    <=> (computes_to_valc_ex_bar lib t1 mkc_axiom
         # computes_to_valc_ex_bar lib t2 mkc_axiom
         # ex_nodefsc_eq_bar uk lib t T
         # member uk lib t T).
Proof.
  introv; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_ffdefs2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.
    apply per_bar_eq_per_ffdefs_eq_bar_lib_per_iff in e0.
    dands.

    { eapply in_open_bar_comb2; try exact e0.
      apply in_ext_ext_implies_in_open_bar_ext; introv w; unfold per_ffdefs_eq in *; tcsp. }

    { eapply in_open_bar_comb2; try exact e0.
      apply in_ext_ext_implies_in_open_bar_ext; introv w; unfold per_ffdefs_eq in *; tcsp. }

    { eapply in_open_bar_comb2; try exact e0; clear e0.
      eapply in_open_bar_ext_pres; try exact e3; clear e3.
      introv n w; unfold per_ffdefs_eq in *; tcsp; repnd.
      unfold ex_nodefsc, ex_nodefsc_eq in *; exrepnd.
      exists u; dands; auto.
      eapply eq_equality2; eauto. }

    { apply all_in_ex_bar_member_implies_member.
      eapply in_open_bar_comb2; try exact e2; clear e2.
      eapply in_open_bar_ext_pres; try exact e3; clear e3.
      introv w h; eapply eq_equality1; eauto. }

  - exrepnd.
    unfold member, equality in e; exrepnd.
    pose proof (nuprl_monotone_func uk lib T T eq e4) as tya; exrepnd.
    rename eq' into eqa.
    exists (per_ffdefs_eq_bar lib eqa t); dands; auto; eauto 3 with slow.

    { apply CL_ffdefs; unfold per_ffdefs.
      exists T T t t eqa; dands; spcast; eauto 3 with slow;
        introv; apply tya0; auto. }

    unfold per_ffdefs_eq_bar.
    eapply in_open_bar_ext_comb2; try exact e0; clear e0.
    eapply in_open_bar_ext_comb2; try exact e1; clear e1.
    eapply in_open_bar_ext_comb2; try exact e2; clear e2.
    apply in_ext_ext_implies_in_open_bar_ext; introv h q w.
    unfold per_ffdefs_eq; dands; auto.
    unfold ex_nodefsc, ex_nodefsc_eq in *; exrepnd; exists u; dands; auto.
    pose proof (tya0 _ e) as tya0; repnd.
    eapply equality_eq1; eauto.
Qed.

Lemma tequality_mkc_ffdefs {o} :
  forall uk lib (T1 T2 t1 t2 : @CTerm o),
    tequality uk lib (mkc_free_from_defs T1 t1) (mkc_free_from_defs T2 t2)
    <=> (tequality uk lib T1 T2 # equality uk lib t1 t2 T1).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_ffdefs2 in teq0; exrepnd.
    dands; eauto 3 with slow.
    exists (per_bar_eq lib eqa); dands; eauto 3 with slow.

    apply CL_bar; exists eqa; dands; eauto 3 with slow.
    eapply in_open_bar_ext_pres; try exact teq2; introv h.
    apply nuprl_refl in h; auto.

  - unfold tequality in teq0; exrepnd.
    pose proof (nuprl_monotone_func uk lib T1 T2 eq teq1) as tya; exrepnd.
    rename eq' into eqa.

    exists (per_ffdefs_eq_bar lib eqa t1).
    apply CL_ffdefs.
    exists T1 T2 t1 t2 eqa; dands; spcast; eauto 3 with slow.

    { introv; eapply tya0. }

    introv; pose proof (tya0 _ e) as tya0; repnd.
    eapply equality_eq1; eauto; eauto 3 with slow.
Qed.
