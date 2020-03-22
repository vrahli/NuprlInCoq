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
Require Export local.


(*Lemma local_equality_of_qnat_bar {o} :
  forall {lib} (bar : @BarLib o lib) t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => equality_of_qnat_bar lib' t1 t2)
    -> equality_of_qnat_bar lib t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.
Hint Resolve local_equality_of_qnat_bar : slow.*)

Lemma per_bar_eq_equality_of_qnat_bar_implies {o} :
  forall (lib : @library o) c t1 t2,
    per_bar_eq lib (equality_of_qnat_bar_lib_per lib c) t1 t2
    -> equality_of_qnat_bar lib c t1 t2.
Proof.
  introv alla.
  unfold per_bar_eq in alla.
  unfold equality_of_int_bar.
  apply in_open_bar_ext_in_open_bar.
  eapply in_open_bar_ext_pres; eauto; clear alla; introv h; simpl in *.
  unfold equality_of_qnat_bar in h; auto.
Qed.
Hint Resolve per_bar_eq_equality_of_qnat_bar_implies : slow.

Lemma all_in_bar_ext_equal_equality_of_qnat_bar_implies_per_bar_eq_implies_equality_of_qnat_bar {o} :
  forall (lib : @library o) c (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (equality_of_qnat_bar lib' c))
    -> (per_bar_eq lib eqa) <=2=> (equality_of_qnat_bar lib c).
Proof.
  introv alla; introv; split; introv h.

  - pose proof (in_open_bar_ext_eq_term_equals_preserves_per_bar_eq
                  _ eqa (equality_of_qnat_bar_lib_per lib c) t1 t2 alla h) as q.
    eauto 3 with slow.

  - eapply in_open_bar_ext_pres;[|exact alla]; clear alla; introv alla; apply alla; clear alla.
    unfold equality_of_qnat_bar; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_equal_equality_of_qnat_bar_implies_per_bar_eq_implies_equality_of_qnat_bar : slow.

Definition equality_of_qnat_bar_to_lib_per {o}
           (lib : library)
           (T : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t t' =>
            {c : qnat_cond , T ===>(lib') (mkc_qnat c) # equality_of_qnat_bar lib' c t t' }).
  introv x y; introv; simpl; tcsp.
Defined.

Lemma local_per_qnat_bar {o} :
  forall (ts : cts(o)), local_ts (per_bar (per_qnat ts)).
Proof.
  introv eqiff alla.
  unfold per_bar in *.
  exists (equality_of_qnat_bar_to_lib_per lib T).
  dands.

  { apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear alla; introv alla; exrepnd.
    eapply in_open_bar_ext_pres; eauto; clear alla1; introv alla; exrepnd.
    introv.
    unfold per_qnat in *; exrepnd.
    exists c; dands; simpl; auto.
    introv; split; intro h; exrepnd; dands; auto.
    - spcast; computes_to_eqval; apply_cequivc_val; auto.
    - exists c; dands; auto. }

  eapply eq_term_equals_trans;[exact eqiff|]; clear eqiff.
  unfold per_bar_eq; introv; split; intro h.

  { apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv alla h; exrepnd.
    apply alla0 in h; clear alla0.
    unfold per_bar_eq in *; simpl in *.

    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla1]; clear alla1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv alla h ext; exrepnd.

    unfold per_qnat in *; exrepnd.
    apply alla0 in h.
    exists c; dands; auto. }

  { eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv alla h; exrepnd.
    apply alla0; clear alla0.
    unfold per_bar_eq in *; simpl in *; exrepnd.
    unfold equality_of_qnat_bar in *.

    apply in_open_bar_ext_in_open_bar in h0.

    eapply in_open_bar_ext_comb2;[|exact h0]; clear h0.
    eapply in_open_bar_ext_comb;[|exact alla1]; clear alla1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv alla h; exrepnd.

    unfold per_qnat in *; exrepnd.
    eapply lib_extends_preserves_ccomputes_to_valc in h1; eauto.
    computes_to_eqval; apply_cequivc_val; auto.
    apply alla0; auto.
    repeat (autodimp h hyp). }
Qed.

Lemma per_qnat_implies_per_bar_per_qnat {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qnat ts lib T T' eq
    -> per_bar (per_qnat ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qnat in per; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib c).
  dands; auto; simpl.

  - apply in_ext_ext_implies_in_open_bar_ext; introv ext.
    exists c; dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[exact per0|]; clear per0.
    eapply eq_term_equals_trans;
      [|apply eq_term_equals_sym;
        apply all_in_bar_ext_equal_equality_of_qnat_bar_implies_per_bar_eq_implies_equality_of_qnat_bar];
      [apply eq_term_equals_refl|]; simpl.
    apply in_ext_ext_implies_in_open_bar_ext; introv; tcsp.
Qed.
Hint Resolve per_qnat_implies_per_bar_per_qnat : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_qnat_l {p} :
  forall (ts : cts(p)) lib T T' eq c,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T (mkc_qnat c)
    -> close ts lib T T' eq
    -> per_bar (per_qnat (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_qnat_bar; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca; apply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_qnat_r {p} :
  forall (ts : cts(p)) lib T T' eq c,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' (mkc_qnat c)
    -> close ts lib T T' eq
    -> per_bar (per_qnat (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 2 with slow.
  eapply local_per_qnat_bar; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca; apply reca; eauto 3 with slow.
Qed.
