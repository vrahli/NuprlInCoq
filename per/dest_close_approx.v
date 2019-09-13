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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.
Require Export local.


Lemma local_equality_of_approx_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => per_approx_eq_bar lib' a b t1 t2)
    -> per_approx_eq_bar lib a b t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.

(*Lemma per_approx_bar_eq {o} :
  forall ts lib (T1 T2 : @CTerm o) eq,
    per_approx_bar ts lib T1 T2 eq
    <=>
    {bar : BarLib lib
    , {a, b, c, d : CTerm
    , T1 ==b==>(bar) (mkc_approx a b)
    # T2 ==b==>(bar) (mkc_approx c d)
    # all_in_bar bar (fun lib => (a ~<~(lib) b <=> c ~<~(lib) d))
    # eq <=2=> (per_approx_eq_bar lib a b) }}.
Proof.
  introv; unfold per_approx_bar; split; intro h; exrepnd.
  { eexists; eexists; eexists; eexists; eexists; dands; eauto. }
  { eexists; eexists; eexists; eexists; dands; eauto. }
Qed.

Lemma all_in_bar_ext_per_approx_bar_eq {o} :
  forall ts lib (bar : @BarLib o lib) (T1 T2 : @CTerm o) eqa,
    all_in_bar_ext bar (fun lib' x => per_approx_bar ts lib' T1 T2 (eqa lib' x))
    <=>
    (all_in_bar_ext
       bar
       (fun lib' x =>
          {bar : BarLib lib'
          , {a, b, c, d : CTerm
          , T1 ==b==>(bar) (mkc_approx a b)
          # T2 ==b==>(bar) (mkc_approx c d)
          # all_in_bar bar (fun lib => (a ~<~(lib) b <=> c ~<~(lib) d))
          # (eqa lib' x) <=2=> (per_approx_eq_bar lib' a b) }})).
Proof.
  introv; split; introv h br ext; introv.
  { pose proof (h lib' br lib'0 ext x) as h; simpl in h.
    apply per_approx_bar_eq in h; auto. }
  { apply per_approx_bar_eq; eapply h; eauto. }
Qed.*)

(*Lemma local_per_approx_bar {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => per_approx_bar ts lib' T T' (eqa lib' x))
    -> per_approx_bar ts lib T T' eq.
Proof.
  introv eqiff alla.
  allrw @per_approx_bar_eq.
  allrw @all_in_bar_ext_per_approx_bar_eq.
  apply all_in_bar_ext_exists_bar_implies in alla.
  exrepnd.

  exists (bar_of_bar_fam fbar).

  dands; introv br ext; simpl in *; exrepnd; eapply alla1; eauto.
  }

  eapply eq_term_equals_trans;[eauto|].
  introv.
  split; introv h.

  {
    eapply per_bar_eq_preserves_all_in_bar_ext_eq_term_equals in alla;[|eauto].
    eapply local_equality_of_approx_bar; eauto.
  }

  {
    introv br ext; introv.
    eapply alla; eauto.
    eapply sub_per_equality_of_approx_bar; eauto.
  }
Qed.*)

(*Definition per_approx_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_approx_bar ts lib T T' eq
  {+} per_bar (per_approx_bar ts) lib T T' eq.*)

Lemma per_bar_eq_per_approx_eq_bar_lib_per {o} :
  forall (lib : @library o) a b,
    (per_bar_eq lib (per_approx_eq_bar_lib_per lib a b))
    <=2=> (per_approx_eq_bar lib a b).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_approx_eq_bar; apply e_all_in_ex_bar_as.
    apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_approx_eq_bar in h; apply e_all_in_ex_bar_as in h.
    eapply in_open_bar_pres; eauto; clear h.
    introv ext h; introv; simpl in *; auto.

  - unfold per_approx_eq_bar in h; apply e_all_in_ex_bar_as in h.
    apply in_open_bar_ext_in_open_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_approx_eq_bar; apply e_all_in_ex_bar_as.
    eapply in_open_bar_pres; eauto; clear h.
    introv ext h; introv; simpl in *; auto.
Qed.

Lemma per_approx_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx ts lib T T' eq
    -> per_bar (per_approx ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per lib a b).
  dands; auto.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    exists a b c d; dands; tcsp; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_approx_eq_bar_lib_per.
Qed.
Hint Resolve per_approx_implies_per_bar : slow.

Definition per_approx_eq_to_lib_per {o}
           (lib : library)
           (T : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t t' =>
            {a : CTerm , {b : CTerm , T ===>(lib') (mkc_approx a b) # per_approx_eq_bar lib' a b t t' }}).
  introv x y; introv; simpl; tcsp.
Defined.

Lemma per_approx_eq_bar_respects_ccequivc_ext {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) t1 t2,
    per_approx_eq_bar lib a1 b1 t1 t2
    -> ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> per_approx_eq_bar lib a2 b2 t1 t2.
Proof.
  introv per ceqa ceqb.
  unfold per_approx_eq_bar in *; exrepnd.
  apply e_all_in_ex_bar_as in per; apply e_all_in_ex_bar_as.
  eapply in_open_bar_pres; eauto; clear per; introv ext h.
  unfold per_approx_eq in *; repnd.
  dands; eauto 3 with slow.
  pose proof (ceqa lib') as ceqa; autodimp ceqa hyp; eauto 3 with slow.
  pose proof (ceqb lib') as ceqb; autodimp ceqb hyp; eauto 3 with slow.
  simpl in *; spcast.
  eapply cequivc_approxc_trans;[|eapply approxc_cequivc_trans;[eauto|] ]; eauto.
  apply cequivc_sym; auto.
Qed.
Hint Resolve per_approx_eq_bar_respects_ccequivc_ext : slow.

Lemma local_per_bar_per_approx {o} :
  forall (ts : cts(o)), local_ts (per_bar (per_approx ts)).
Proof.
  introv eqiff alla.
  unfold per_bar in *.

  exists (per_approx_eq_to_lib_per lib T); simpl in *.
  dands.

  { eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear alla; introv alla; exrepnd.
    eapply in_open_bar_ext_pres; eauto; clear alla1; introv alla1; exrepnd.
    introv ext.
    unfold per_approx in *; exrepnd.
    exists a b c d; dands; auto.
    introv; dands; split; intro h; exrepnd.
    - computes_to_eqval_ext.
      apply cequivc_ext_mkc_approx_right in ceq; repnd; eauto 3 with slow.
    - exists a b; dands; auto. }

  eapply eq_term_equals_trans;[eauto|]; clear eqiff.


XXXXXXXXXXXX

  apply in_open_bar_ext_choice in alla; exrepnd.
  apply in_open_bar_eqa_choice in alla0; exrepnd.
  apply in_open_data_open_choice in alla1; exrepnd.
  exists (lib_fun_dep_eqa Feqa Flib2).
  dands.

  {
    introv ext.
    pose proof (alla0 _ ext) as alla1; simpl in *.
    apply in_ext_ext_implies in alla1.
    pose proof (alla1 (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)) as alla1; repnd.
    pose proof (alla2 _ (lib_extends_refl _)) as alla2; simpl in *.

    assert (lib_extends
              (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                     (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                     (lib_extends_refl (Flib lib' ext))) lib') as xta by eauto 3 with slow.

    exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                  (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                  (lib_extends_refl (Flib lib' ext))) xta.
    introv xtb xtc.
    assert (lib_extends lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
    pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

    unfold per_func_ext in *; exrepnd.
    exists eqa1 eqb0; dands; tcsp;[].

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl lib'0); auto.
      apply alla2; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx0 in w0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].

    unfold type_family_ext in alla3, xx1; exrepnd.

    computes_to_eqval_ext.
    hide_hyp xx3.
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

    eapply (per_func_ext_eq_change_pers
              ts lib lib'0 A A' v B v' B'
              A1 A'1 A0 A'0
              v1 B1 v'1 B'1
              v0 B0 v'0 B'0); eauto.
  }

  {
    rename alla0 into imp.
    eapply eq_term_equals_trans;[eauto|].
    introv.
    split; intro h; exrepnd.

    { eapply eq_per_bar_eq_lib_fun_dep_eqa_part1; eauto. }

    unfold per_bar_eq in *.
    introv ext; simpl in *.

    pose proof (h (Flib lib' ext)) as h; exrepnd; simpl in *.
    autodimp h hyp; eauto 3 with slow;[]; exrepnd.

    assert (lib_extends lib'' lib') as xta by eauto 3 with slow.
    exists lib'' xta; introv xtb; introv.

    assert (lib_extends lib'' lib) as xtc by eauto 3 with slow.
    pose proof (imp _ ext lib'0 (lib_extends_trans xtb y) z) as imp'; simpl in *; repnd.
    apply imp'; clear imp'.
    introv xtd.

    exists (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd).
    exists (lib_ext_ext (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd)).
    introv xte; introv.

    pose proof (h1 lib'2) as h1; simpl in *.
    repeat (autodimp h1 hyp); eauto 3 with slow.
    exrepnd.

    pose proof (imp'0 lib'1 xtd _ xte z0) as imp'0; simpl in *.

    pose proof (imp lib1 ext1 lib2 ext2 extz) as imp; simpl in *; repnd; clear imp.
    pose proof (imp0 lib3 ext3 lib'2 (lib_extends_trans w ext4) z1) as imp0; simpl in *.

    eapply (per_func_ext_eq_change_pers2 ts lib lib'2 T T' A A' v v' B B');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }


XXXXXXXXXXXXXx
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  exists (per_approx_eq_to_lib_per lib T).
  dands.

  {
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (alla0 _ br _ ext0 x0) as alla0; exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext bb lib' br0))) as alla0; simpl in *.
    unfold per_approx in *; exrepnd.
    exists a b c d; dands; auto.
    introv; split; intro h; exrepnd; dands; auto.
    - computes_to_eqval_ext.
      apply cequivc_ext_mkc_approx_right in ceq; repnd; eauto 3 with slow.
    - exists a b; dands; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear eqiff.
    introv.
    split; intro h; exrepnd.

    - rw @per_bar_eq_iff in h; unfold per_bar_eq_bi in h; exrepnd.
      apply per_bar_eq_iff2.
      exists bar'.
      introv br ext; introv; simpl in *; exrepnd.

      pose proof (h0 lib') as h0; simpl in *; autodimp h0 hyp.
      { eexists; eexists; dands; eauto 4 with slow. }
      pose proof (h0 _ ext x) as h0; simpl in *.

      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.

      pose proof (alla0 _ br lib'0 xt1 x) as allb; exrepnd.
      apply allb0 in h0; clear allb0.
      rw @per_bar_eq_iff in h0; unfold per_bar_eq_bi in *; exrepnd.

      exists (intersect_bars (fbar lib0 br lib'0 xt1 x) bar'0).
      introv br' ext' x'.
      pose proof (h1 _ br' _ ext' x') as h1; simpl in h1.
      simpl in *; exrepnd.

      assert (lib_extends lib'2 lib4) as xt2 by eauto 3 with slow.
      pose proof (allb1 _ br'0 lib'2 xt2 x') as allb1; simpl in *.
      unfold per_approx in allb1; exrepnd.
      apply allb1 in h1; clear allb1.
      exists a b; dands; auto.

    - rw @per_bar_eq_iff.
      exists (bar_of_bar_fam fbar).
      introv br ext; introv; simpl in *; exrepnd.
      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.
      pose proof (alla0 _ br lib'0 xt1 x) as allb; simpl in *; exrepnd.
      apply allb0; clear allb0.

      introv br' ext'; introv.
      pose proof (h lib'1) as h; simpl in *; autodimp h hyp.
      { eexists; eexists; eexists; eexists; eexists; eauto. }
      assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.
      pose proof (h lib'2 ext' xt2) as h; simpl in h; exrepnd.
      exists bar'.

      introv br'' ext''; introv.
      pose proof (h0 _ br'' _ ext'' x2) as h0; simpl in *; exrepnd.

      assert (lib_extends lib'4 lib'1) as xt3 by eauto 3 with slow.
      assert (lib_extends lib'4 lib'0) as xt4 by eauto 3 with slow.
      pose proof (allb1 _ br' lib'4 xt3 xt4) as allb0; simpl in *.

      unfold per_approx in allb0; exrepnd.
      eapply (lib_per_cond _ eqa0); apply allb0.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_approx_right in ceq; repnd; eauto 4 with slow.
  }
Qed.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_approx_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_approx; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_approx; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

(*
Lemma dest_close_per_approx_l_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_approx; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_approx_r_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_approx; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
 *)
