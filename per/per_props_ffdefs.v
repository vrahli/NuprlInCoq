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
  spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ x) as pera3.
  pose proof (perb3 _ x) as perb3.
  simpl in *.
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
  spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ x) as pera3.
  pose proof (perb3 _ x) as perb3.
  simpl in *.
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
  forall (ts : cts(o)) lib T A f T' eq,
    ts = univ
    -> computes_to_valc lib T (mkc_free_from_defs A f)
    -> close ts lib T T' eq
    -> per_bar (per_ffdefs (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_ffdefs_l {o} :
  forall i (ts : cts(o)) lib T A f T' eq,
    ts = univi_bar i
    -> computes_to_valc lib T (mkc_free_from_defs A f)
    -> close ts lib T T' eq
    -> per_bar (per_ffdefs (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs_nuprli; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
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
  forall (lib : @library o) A f B g eq,
    nuprl lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    -> per_bar (per_ffdefs nuprl) lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_ffdefs_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_ffdefs {o} :
  forall i (lib : @library o) A f B g eq,
    nuprli i lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    -> per_bar (per_ffdefs (nuprli i)) lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_ffdefs_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_ffdefs2 {o} :
  forall lib (eq : per(o)) A f B g,
    nuprl lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_ffdefs_eq_bar_lib_per lib eqa f)))
        # all_in_bar_ext bar (fun lib' x => nuprl lib' A B (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => eqa lib' x f g).
Proof.
  introv u.
  apply dest_nuprl_ffdefs in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A B (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => eqa0 lib'' y f g)
               # (eqa lib' x) <=2=> (per_ffdefs_eq_bar lib' eqa0 f) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_ffdefs in *; exrepnd.
    spcast; computes_to_value_isvalue.
    exists eqa0; dands; auto.
  }
  clear u0.

  eapply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.

  exists bar (bar_lib_per2lib_per feqa).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].

    simpl.
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans x0 ext) (lib_extends_trans x0 x).
      unfold type_family_ext in u0; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (u0 _ x0) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as q.
      unfold type_family_ext in q; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprl_refl in q0.
      apply nuprl_refl in u0.
      eapply nuprl_uniquely_valued in q0; try exact u0.
      apply q0; auto.

    - exrepnd.
      pose proof (u0 _ x0) as u0; simpl in *.

      pose proof (e0 lib1 br0 _ ext0 x1) as q; repnd.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprl_refl in q0.
      apply nuprl_refl in u0.
      eapply nuprl_uniquely_valued in q0; try exact u0.
      apply q0; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h0 _ (lib_extends_refl lib'0)) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e1 _ (lib_extends_refl lib'0)) as e1; simpl in *.
      apply nuprl_refl in e1.
      apply nuprl_refl in h0.
      eapply nuprl_uniquely_valued in e1; try exact h0.
      apply e1; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd; auto.
    pose proof (h1 lib'0 (lib_extends_refl _)) as h1; simpl in *; eauto.
  }
Qed.

Lemma dest_nuprli_ffdefs2 {o} :
  forall i lib (eq : per(o)) A f B g,
    nuprli i lib (mkc_free_from_defs A f) (mkc_free_from_defs B g) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_ffdefs_eq_bar_lib_per lib eqa f)))
        # all_in_bar_ext bar (fun lib' x => nuprli i lib' A B (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => eqa lib' x f g).
Proof.
  introv u.
  apply dest_nuprli_ffdefs in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A B (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => eqa0 lib'' y f g)
               # (eqa lib' x) <=2=> (per_ffdefs_eq_bar lib' eqa0 f) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_ffdefs in *; exrepnd.
    spcast; computes_to_value_isvalue.
    exists eqa0; dands; auto.
  }
  clear u0.

  eapply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.

  exists bar (bar_lib_per2lib_per feqa).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].

    simpl.
    apply implies_eq_term_equals_per_ffdefs_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans x0 ext) (lib_extends_trans x0 x).
      unfold type_family_ext in u0; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (u0 _ x0) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as q.
      unfold type_family_ext in q; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprli_refl in q0.
      apply nuprli_refl in u0.
      eapply nuprli_uniquely_valued in q0; try exact u0.
      apply q0; auto.

    - exrepnd.
      pose proof (u0 _ x0) as u0; simpl in *.

      pose proof (e0 lib1 br0 _ ext0 x1) as q; repnd.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprli_refl in q0.
      apply nuprli_refl in u0.
      eapply nuprli_uniquely_valued in q0; try exact u0.
      apply q0; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h0 _ (lib_extends_refl lib'0)) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e1 _ (lib_extends_refl lib'0)) as e1; simpl in *.
      apply nuprli_refl in e1.
      apply nuprli_refl in h0.
      eapply nuprli_uniquely_valued in e1; try exact h0.
      apply e1; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd; auto.
    pose proof (h1 lib'0 (lib_extends_refl _)) as h1; simpl in *; eauto.
  }
Qed.

Lemma per_bar_eq_per_ffdefs_eq_bar_lib_per_iff {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) f p1 p2,
    (per_bar_eq bar (per_ffdefs_eq_bar_lib_per lib eqa f) p1 p2)
      <=>
      exists bar,
        all_in_bar_ext
          bar
          (fun lib' x => per_ffdefs_eq lib' (eqa lib' x) f p1 p2).
Proof.
  introv; split; intro h.

  - apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_ffdefs_eq; apply lib_per_cond. }
    unfold per_bar_eq in *; simpl in *.
    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.

    apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_ffdefs_eq; apply lib_per_cond. }
    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.
    unfold per_ffdefs_eq_bar in h0; exrepnd.
    exists bar0; simpl in *.
    unfold raise_ext_per_fam in *; simpl in *.
    unfold raise_ext_per in *.

    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h1; apply lib_per_cond.

  - unfold per_bar_eq; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x).
    introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h0 _ br'1 lib'3 (lib_extends_trans (lib_extends_trans e ext') br'2) (lib_extends_trans (lib_extends_trans e x0) x)) as h0; simpl in *.
    eapply implies_eq_term_equals_per_ffdefs_eq; try exact h0; apply lib_per_cond.
Qed.

Definition ex_nodefsc_eq {o} (lib : library) (t T : @CTerm o) :=
  {u : @CTerm o , equality lib t u T # nodefsc u}.

Definition ex_nodefsc_eq_bar {o} (lib : library) (t T : @CTerm o) :=
  all_in_ex_bar lib (fun lib' => ex_nodefsc_eq lib' t T).

Lemma equality_in_mkc_ffdefs {p} :
  forall lib (t1 t2 T t : @CTerm p),
    equality lib t1 t2 (mkc_free_from_defs T t)
    <=> (computes_to_valc_ex_bar lib t1 mkc_axiom
         # computes_to_valc_ex_bar lib t2 mkc_axiom
         # ex_nodefsc_eq_bar lib t T
         # member lib t T).
Proof.
  introv; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_ffdefs2 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.
    apply per_bar_eq_per_ffdefs_eq_bar_lib_per_iff in e0.
    exrepnd.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in e3.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in e1.
    apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in e2.

    remember (intersect_bars bar bar0) as b.
    clear dependent bar.
    clear dependent bar0.

    dands;[| | |].

    { exists b; introv br ext.
      assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
      pose proof (e2 _ br _ ext xt) as e2; simpl in *.
      unfold per_ffdefs_eq in *; tcsp. }

    { exists b; introv br ext.
      assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
      pose proof (e2 _ br _ ext xt) as e2; simpl in *.
      unfold per_ffdefs_eq in *; tcsp. }

    { exists b; introv br ext.
      assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
      pose proof (e1 _ br _ ext xt) as e1; simpl in *.
      pose proof (e2 _ br _ ext xt) as e2; simpl in *.
      pose proof (e3 _ br _ ext xt) as e3; simpl in *.
      unfold per_ffdefs_eq in *; repnd.
      unfold ex_nodefsc, ex_nodefsc_eq in *; exrepnd; exists u; dands; auto.
      eapply eq_equality2; eauto. }

    exists (per_bar_eq b eqa).
    dands.

    { apply CL_bar; eauto 3 with slow.
      exists b eqa; dands; eauto 3 with slow. }

    introv br ext; introv.
    exists (trivial_bar lib'0); introv br' ext'; introv; simpl in *.
    eapply e1; eauto; eauto 3 with slow.

  - exrepnd.
    unfold member, equality in e; exrepnd.

    pose proof (nuprl_monotone_func lib T T eq e4) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_ffdefs_eq_bar lib eqa' t); dands; auto; eauto 3 with slow.

    {
      apply CL_ffdefs; unfold per_ffdefs.
      exists T T t t eqa'; dands; spcast; eauto 3 with slow;
        introv; apply tya0; auto.
    }

    unfold computes_to_valc_ex_bar in *.
    unfold ex_nodefsc_eq_bar in *; exrepnd.
    unfold all_in_ex_bar in *; exrepnd.
    exists (intersect3bars bar bar0 bar1); introv br ext; introv; simpl in *; exrepnd.
    pose proof (e1 _ br5 _ (lib_extends_trans ext (lib_extends_trans br1 br2))) as e1.
    pose proof (e2 _ br4 _ (lib_extends_trans ext (lib_extends_trans br1 br6))) as e2.
    pose proof (e5 _ br0 _ (lib_extends_trans ext br3)) as e5.
    simpl in *.
    split; dands; auto.

    unfold ex_nodefsc_eq, ex_nodefsc in *; exrepnd; exists u; dands; auto.
    eapply equality_eq1; eauto; eapply tya0.
Qed.

Lemma tequality_mkc_ffdefs {o} :
  forall lib (T1 T2 t1 t2 : @CTerm o),
    tequality lib (mkc_free_from_defs T1 t1) (mkc_free_from_defs T2 t2)
    <=> (tequality lib T1 T2 # equality lib t1 t2 T1).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_ffdefs2 in teq0; exrepnd.
    dands; eauto 3 with slow.
    exists (per_bar_eq bar eqa); dands; eauto 3 with slow.

    { apply CL_bar; exists bar eqa; dands; eauto 3 with slow.
      introv br ext; introv.
      pose proof (teq2 _ br _ ext x) as teq2; simpl in *; eauto 3 with slow.
      apply nuprl_refl in teq2; auto. }

    introv br ext; introv.
    exists (trivial_bar lib'0); introv br' ext'; introv; simpl in *.
    pose proof (teq0 _ br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as teq0; simpl in *; auto.

  - unfold tequality in teq0; exrepnd.
    pose proof (nuprl_monotone_func lib T1 T2 eq teq1) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_ffdefs_eq_bar lib eqa' t1).
    apply CL_ffdefs.
    exists T1 T2 t1 t2 eqa'; dands; spcast; eauto 3 with slow.

    { introv; eapply tya0. }

    { introv; pose proof (tya0 _ e) as tya0; repnd.
      eapply equality_eq1; eauto; eauto 3 with slow. }
Qed.
