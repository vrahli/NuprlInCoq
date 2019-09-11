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


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.
Require Export local.


Lemma local_equality_of_csname_bar {o} :
  forall {lib} (bar : @BarLib o lib) n t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => equality_of_csname_bar lib' n t1 t2)
    -> equality_of_csname_bar lib n t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.
Hint Resolve local_equality_of_csname_bar : slow.

Lemma per_bar_eq_equality_of_csname_bar_implies {o} :
  forall {lib} (bar : @BarLib o lib) n t1 t2,
    per_bar_eq bar (equality_of_csname_bar_lib_per lib n) t1 t2
    -> equality_of_csname_bar lib n t1 t2.
Proof.
  introv alla.
  unfold per_bar_eq in alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd; simpl in *.
  apply all_in_bar_ext_exists_fbar_implies in alla0; exrepnd; simpl in *.

  exists (bar_of_bar_fam_fam ffbar).
  introv br ext; simpl in *; exrepnd.
  pose proof (alla1 _ br _ ext0 x _ br' _ ext' x') as alla0; simpl in *.
  eapply alla0; eauto.
Qed.
Hint Resolve per_bar_eq_equality_of_csname_bar_implies : slow.

Lemma all_in_bar_ext_equal_equality_of_csname_bar_implies_per_bar_eq_implies_equality_of_csname_bar {o} :
  forall lib (bar : @BarLib o lib) (eqa : lib-per(lib,o)) n,
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (equality_of_csname_bar lib' n))
    -> (per_bar_eq bar eqa) <=2=> (equality_of_csname_bar lib n).
Proof.
  introv alla; introv; split; introv h.

  - pose proof (all_in_bar_ext_eq_term_equals_preserves_per_bar_eq
                  _ bar eqa (equality_of_csname_bar_lib_per lib n) t1 t2 alla h) as q.
    eauto 3 with slow.

  - introv br ext; introv.
    exists (trivial_bar lib'0).
    introv br' ext'; introv; simpl in *.
    apply (alla _ br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)).
    eapply sub_per_equality_of_csname_bar;[|eauto]; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_equal_equality_of_csname_bar_implies_per_bar_eq_implies_equality_of_csname_bar : slow.

Definition equality_of_csname_bar_to_lib_per {o}
           (lib : library)
           (T : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t t' =>
            {n : nat , T ===>(lib') (mkc_csname n) # equality_of_csname_bar lib' n t t' }).
  introv x y; introv; simpl; tcsp.
Defined.

Lemma local_per_csname_bar {o} :
  forall (ts : cts(o)), local_ts (per_bar (per_csname ts)).
Proof.
  introv eqiff alla.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  exists (equality_of_csname_bar_to_lib_per lib T).
  dands.

  {
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (alla0 _ br _ ext0 x0) as alla0; exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext bb lib' br0))) as alla0; simpl in *.
    unfold per_csname in *; exrepnd.
    exists n; dands; auto.
    introv; split; intro h; exrepnd; dands; auto.
    - spcast; computes_to_eqval; apply_cequivc_val; auto.
    - exists n; dands; auto.
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
      unfold per_csname in allb1; exrepnd.
      apply allb0 in h1; clear allb0.
      exists n; dands; auto.

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

      unfold per_csname in allb0; exrepnd.
      eapply (lib_per_cond _ eqa0); apply allb2.
      spcast; computes_to_eqval; apply_cequivc_val; auto.
  }
Qed.

Lemma per_csname_implies_per_bar_per_csname {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_csname ts lib T T' eq
    -> per_bar (per_csname ts) lib T T' eq.
Proof.
  introv per.
  unfold per_csname in per; exrepnd.
  exists (trivial_bar lib) (equality_of_csname_bar_lib_per lib n).
  dands; auto.
  - introv br ext; introv; simpl in *.
    exists n; dands; tcsp; eauto 3 with slow.
  - eapply eq_term_equals_trans;[eauto|].
    introv; split; introv h.
    + introv br ext; introv; simpl in *.
      exists (trivial_bar lib'0).
      introv br' ext' x'.
      eapply sub_per_equality_of_csname_bar;[|eauto]; eauto 3 with slow.
    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
      exrepnd.
      apply all_in_bar_ext_exists_bar_implies in h0; exrepnd.
      exists (bar_of_bar_fam fbar).
      introv br ext; simpl in *; exrepnd.
      eapply h1; eauto.
Qed.
Hint Resolve per_csname_implies_per_bar_per_csname : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_csname_l {p} :
  forall (ts : cts(p)) lib T T' eq n,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T (mkc_csname n)
    -> close ts lib T T' eq
    -> per_bar (per_csname (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x); eauto 3 with slow.
Qed.

Lemma dest_close_per_csname_r {p} :
  forall (ts : cts(p)) lib T T' eq n,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' (mkc_csname n)
    -> close ts lib T T' eq
    -> per_bar (per_csname (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x); eauto 3 with slow.
Qed.

(*Lemma dest_close_per_csname_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_csname)
    -> close ts lib T T' eq
    -> per_csname_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_csname_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_csname)
    -> close ts lib T T' eq
    -> per_csname_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_csname_ceq_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) mkc_csname
    -> close ts lib T T' eq
    -> per_csname_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_csname_ceq_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T' ==b==>(bar) mkc_csname
    -> close ts lib T T' eq
    -> per_csname_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_csname_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
 *)
