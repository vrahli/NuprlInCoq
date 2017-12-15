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


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.


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

Lemma per_approx_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx ts lib T T' eq
    -> per_bar (per_approx ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (trivial_bar lib) (per_approx_eq_bar_lib_per lib a b).
  dands; auto.
  - introv br ext; introv; simpl in *.
    exists a b c d; dands; tcsp; eauto 3 with slow.
  - eapply eq_term_equals_trans;[eauto|].
    introv; split; introv h.
    + introv br ext; introv; simpl in *.
      exists (trivial_bar lib'0).
      introv br' ext' x'.
      eapply sub_per_approx_eq_bar;[|eauto]; eauto 3 with slow.
    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
      exrepnd.
      apply all_in_bar_ext_exists_bar_implies in h0; exrepnd.
      exists (bar_of_bar_fam fbar).
      introv br ext; simpl in *; exrepnd.
      eapply h1; eauto.
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

(*Lemma local_per_bar_per_approx {o} :
  forall (ts : cts(o)), local_ts (per_bar (per_approx ts)).
Proof.
  introv eqiff alla.
  unfold per_bar in *.

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
    - spcast; computes_to_eqval; auto.
    - exists a b; dands; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear eqiff.
    introv.
    repeat (rw @per_bar_eq_iff).
    split; intro h; exrepnd.

    - exists bar'.
      introv br ext; introv; simpl in *; exrepnd.

      pose proof (alla0 _ br _ ext0 x0) as alla; exrepnd.
      remember (fbar _ br _ ext0 x0) as bb.
      pose proof (alla2 _ br4 _ (lib_extends_trans ext br3) (lib_extends_trans ext (lib_extends_trans br3 (bar_lib_ext _ _ br4)))) as alla2; simpl in *.
      unfold per_approx in *; exrepnd.
      exists a b; dands; auto.
      apply alla2; clear alla2.

      pose proof (h _ br _ ext0 x0) as h; simpl in *.




      exrepnd.
      exists bar'.




      apply alla1 in h.
      pose proof (h _ br0 _ ext (lib_extends_trans ext (bar_lib_ext bb lib' br0))) as h; simpl in *.
      unfold per_approx in alla0; exrepnd.
      apply alla0 in h.
      exists a b; dands; auto.

    - pose proof (alla0 _ br _ ext x) as alla0; exrepnd.
      apply alla1; clear alla1.
      introv br' ext'; introv.
      pose proof (alla0 _ br' _ ext' x0) as alla0; simpl in *.
      pose proof (h lib'1) as h; simpl in h; autodimp h hyp;
        [eexists; eexists; eexists; eexists; eexists; eauto|].
      pose proof (h lib'2 ext') as h; simpl in *; autodimp h hyp; eauto 3 with slow;[].
      exrepnd.
      unfold per_approx in *; exrepnd.
      spcast; computes_to_eqval; auto.
      apply alla0; auto.
  }
Qed.*)


(* ====== dest lemmas ====== *)

Lemma dest_close_per_approx_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_approx A B)
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
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_approx; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

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
