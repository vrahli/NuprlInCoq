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


Lemma local_equality_of_cequiv_bar {o} :
  forall {lib : SL} (bar : @BarLib o lib) a b t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => per_cequiv_eq_bar lib' a b t1 t2)
    -> per_cequiv_eq_bar lib a b t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.

(*Lemma per_cequiv_bar_eq {o} :
  forall ts lib (T1 T2 : @CTerm o) eq,
    per_cequiv_bar ts lib T1 T2 eq
    <=>
    {bar : BarLib lib
    , {a, b, c, d : CTerm
    , T1 ==b==>(bar) (mkc_cequiv a b)
    # T2 ==b==>(bar) (mkc_cequiv c d)
    # all_in_bar bar (fun lib => (a ~=~(lib) b <=> c ~=~(lib) d))
    # eq <=2=> (per_cequiv_eq_bar lib a b) }}.
Proof.
  introv; unfold per_cequiv_bar; split; intro h; exrepnd.
  { eexists; eexists; eexists; eexists; eexists; dands; eauto. }
  { eexists; eexists; eexists; eexists; dands; eauto. }
Qed.

Lemma all_in_bar_ext_per_cequiv_bar_eq {o} :
  forall ts lib (bar : @BarLib o lib) (T1 T2 : @CTerm o) eqa,
    all_in_bar_ext bar (fun lib' x => per_cequiv_bar ts lib' T1 T2 (eqa lib' x))
    <=>
    (all_in_bar_ext
       bar
       (fun lib' x =>
          {bar : BarLib lib'
          , {a, b, c, d : CTerm
          , T1 ==b==>(bar) (mkc_cequiv a b)
          # T2 ==b==>(bar) (mkc_cequiv c d)
          # all_in_bar bar (fun lib => (a ~=~(lib) b <=> c ~=~(lib) d))
          # (eqa lib' x) <=2=> (per_cequiv_eq_bar lib' a b) }})).
Proof.
  introv; split; introv h br ext; introv.
  { pose proof (h lib' br lib'0 ext x) as h; simpl in h.
    apply per_cequiv_bar_eq in h; auto. }
  { apply per_cequiv_bar_eq; eapply h; eauto. }
Qed.*)

(*Definition per_cequiv_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_cequiv_bar ts lib T T' eq
  {+} per_bar ts lib T T' eq.*)

Lemma per_cequiv_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_cequiv ts lib T T' eq
    -> per_bar (per_cequiv ts) lib T T' eq.
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (trivial_bar lib) (per_cequiv_eq_bar_lib_per lib a b).
  dands; auto.
  - introv br ext; introv; simpl in *.
    exists a b c d; dands; tcsp; eauto 3 with slow.
  - eapply eq_term_equals_trans;[eauto|].
    introv; split; introv h.
    + introv br ext; introv; simpl in *.
      exists (trivial_bar lib'0).
      introv br' ext' x'.
      eapply sub_per_cequiv_eq_bar;[|eauto]; eauto 3 with slow.
    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
      exrepnd.
      apply all_in_bar_ext_exists_bar_implies in h0; exrepnd.
      exists (bar_of_bar_fam fbar).
      introv br ext; simpl in *; exrepnd.
      eapply h1; eauto.
Qed.
Hint Resolve per_cequiv_implies_per_bar : slow.

(*Lemma type_extensionality_per_cequiv_bar {o} :
  forall (ts : cts(o)),
    type_extensionality (per_cequiv_bar ts).
Proof.
  introv h e.
  unfold per_cequiv_bar in *; exrepnd.
  exists a b c d; dands; eauto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_cequiv_bar : slow.

Lemma uniquely_valued_per_cequiv_bar {o} :
  forall (ts : cts(o)), uniquely_valued (per_cequiv_bar ts).
Proof.
  introv h q.
  unfold per_cequiv_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  eapply eq_per_cequiv_eq_bar; eapply two_computes_to_valc_ceq_bar_mkc_cequiv; eauto.
Qed.
Hint Resolve uniquely_valued_per_cequiv_bar : slow.*)

Definition per_cequiv_eq_to_lib_per {o}
           (lib : SL)
           (T : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun (lib' : SL) (x : lib_extends lib' lib) t t' =>
            {a : CTerm , {b : CTerm , T ===>(lib') (mkc_cequiv a b) # per_cequiv_eq_bar lib' a b t t' }}).
  introv x y; introv; simpl; tcsp.
Defined.

Lemma per_cequiv_eq_bar_respects_ccequivc_ext {o} :
  forall (lib : SL) (a1 a2 b1 b2 : @CTerm o) t1 t2,
    per_cequiv_eq_bar lib a1 b1 t1 t2
    -> ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> per_cequiv_eq_bar lib a2 b2 t1 t2.
Proof.
  introv per ceqa ceqb.
  unfold per_cequiv_eq_bar in *; exrepnd.
  exists bar; introv br ext.
  pose proof (per0 _ br _ ext) as per0; simpl in *.
  unfold per_cequiv_eq in *; repnd.
  dands; eauto 3 with slow.
  pose proof (ceqa lib'0) as ceqa; autodimp ceqa hyp; eauto 3 with slow.
  pose proof (ceqb lib'0) as ceqb; autodimp ceqb hyp; eauto 3 with slow.
  simpl in *; spcast.
  eapply cequivc_trans;[apply cequivc_sym;eauto|].
  eapply cequivc_trans;[exact per0|]; auto.
Qed.
Hint Resolve per_cequiv_eq_bar_respects_ccequivc_ext : slow.

Lemma local_per_bar_per_cequiv {o} :
  forall (ts : cts(o)), local_ts (per_bar (per_cequiv ts)).
Proof.
  introv eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  exists (per_cequiv_eq_to_lib_per lib T).
  dands.

  {
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (alla0 _ br _ ext0 x0) as alla0; exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext bb lib' br0))) as alla0; simpl in *.
    unfold per_cequiv in *; exrepnd.
    exists a b c d; dands; auto.
    introv; split; intro h; exrepnd; dands; auto.
    - computes_to_eqval_ext.
      apply cequivc_ext_mkc_cequiv_right in ceq; repnd; eauto 3 with slow.
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
      unfold per_cequiv in allb1; exrepnd.
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

      unfold per_cequiv in allb0; exrepnd.
      eapply (lib_per_cond _ eqa0); apply allb0.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_cequiv_right in ceq; repnd; eauto 4 with slow.
  }
Qed.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_cequiv_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_bar (per_cequiv (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_cequiv_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_bar (per_cequiv (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

(*
Lemma dest_close_per_cequiv_l_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_bar (per_cequiv (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_cequiv_r_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T' (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_bar (per_cequiv (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
 *)
