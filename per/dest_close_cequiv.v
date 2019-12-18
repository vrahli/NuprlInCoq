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


(*Lemma local_equality_of_cequiv_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => per_cequiv_eq_bar lib' a b t1 t2)
    -> per_cequiv_eq_bar lib a b t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.*)

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

Lemma per_bar_eq_per_cequiv_eq_bar_lib_per {o} :
  forall inh (lib : @library o) a b,
    (per_bar_eq inh lib (per_cequiv_eq_bar_lib_per inh lib a b))
    <=2=> (per_cequiv_eq_bar inh lib a b).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_cequiv_eq_bar.
    apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_cequiv_eq_bar in h.
    eapply in_open_bar_pres; eauto; clear h.
    introv ext h; introv; simpl in *; auto.

  - unfold per_cequiv_eq_bar in h.
    apply in_open_bar_ext_in_open_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_cequiv_eq_bar.
    eapply in_open_bar_pres; eauto; clear h.
    introv ext h; introv; simpl in *; auto.
Qed.

Lemma per_cequiv_implies_per_bar {o} :
  forall inh ts lib (T T' : @CTerm o) eq,
    per_cequiv inh ts lib T T' eq
    -> per_bar inh (per_cequiv inh ts) lib T T' eq.
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per inh lib a b).
  dands; auto.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    exists a b c d; dands; tcsp; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_cequiv_eq_bar_lib_per.
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
           inh
           (lib : library)
           (T : @CTerm o) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) t t' =>
            {a : CTerm , {b : CTerm , T ===>(inh,lib') (mkc_cequiv a b) # per_cequiv_eq_bar inh lib' a b t t' }}).
  introv x y; introv; simpl; tcsp.
Defined.

Lemma per_cequiv_eq_bar_respects_ccequivc_ext {o} :
  forall inh lib (a1 a2 b1 b2 : @CTerm o) t1 t2,
    per_cequiv_eq_bar inh lib a1 b1 t1 t2
    -> ccequivc_ext inh lib a1 a2
    -> ccequivc_ext inh lib b1 b2
    -> per_cequiv_eq_bar inh lib a2 b2 t1 t2.
Proof.
  introv per ceqa ceqb.
  unfold per_cequiv_eq_bar in *; exrepnd.
  eapply in_open_bar_pres; eauto; clear per; introv ext h.
  unfold per_cequiv_eq in *; repnd.
  dands; eauto 3 with slow.
  pose proof (ceqa lib') as ceqa; autodimp ceqa hyp; eauto 3 with slow.
  pose proof (ceqb lib') as ceqb; autodimp ceqb hyp; eauto 3 with slow.
  simpl in *; spcast.
  eapply cequivc_trans;[|eauto].
  eapply cequivc_trans;[|eauto].
  eapply cequivc_sym;auto.
Qed.
Hint Resolve per_cequiv_eq_bar_respects_ccequivc_ext : slow.

Lemma two_ccomputes_to_valc_ext_cequiv_implies {o} :
  forall inh (lib : @library o) T a1 b1 a2 b2,
    (T ===>(inh,lib) (mkc_cequiv a1 b1))
    -> (T ===>(inh,lib) (mkc_cequiv a2 b2))
    -> (ccequivc_ext inh lib a1 a2 # ccequivc_ext inh lib b1 b2).
Proof.
  introv comp1 comp2; split; introv ext;
    eapply lib_extends_preserves_ccomputes_to_valc in comp1; eauto;
      eapply lib_extends_preserves_ccomputes_to_valc in comp2; eauto;
        ccomputes_to_eqval;
        apply cequivc_decomp_cequiv in eqt; spcast; repnd; auto;
          apply cequivc_sym; auto.
Qed.

Lemma local_per_bar_per_cequiv {o} :
  forall inh (ts : cts(o)), local_ts inh (per_bar inh (per_cequiv inh ts)).
Proof.
  introv eqiff alla.
  unfold per_bar in *.

  exists (per_cequiv_eq_to_lib_per inh lib T); simpl in *.
  dands.

  { eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear alla; introv alla; exrepnd.
    eapply in_open_bar_ext_pres; eauto; clear alla1; introv alla1; exrepnd.
    introv ext.
    unfold per_cequiv in *; exrepnd.
    exists a b c d; dands; auto.
    introv; dands; split; intro h; exrepnd.
    - computes_to_eqval_ext.
      apply cequivc_ext_mkc_cequiv_right in ceq; repnd; eauto 3 with slow.
    - exists a b; dands; auto. }

  eapply eq_term_equals_trans;[eauto|]; clear eqiff.
  unfold per_bar_eq in *; introv; split; intro h.

  { eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h; exrepnd.
    apply alla0 in h; clear alla0.

    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla1]; clear alla1.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h; exrepnd.
    introv; simpl.
    unfold per_cequiv in *; exrepnd.
    apply alla1 in h.
    exists a b; dands; auto. }

  { eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h; exrepnd.
    apply alla0; clear alla0; simpl in *; exrepnd.

    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact alla1]; clear alla1.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h; exrepnd.
    unfold per_cequiv in *; exrepnd.
    apply alla1.
    eapply two_ccomputes_to_valc_ext_cequiv_implies in h0; try exact alla0; repnd.
    eapply per_cequiv_eq_bar_respects_ccequivc_ext; eauto 3 with slow. }
Qed.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_cequiv_l {p} :
  forall inh (ts : cts(p)) lib T A B T' eq,
    type_system inh ts
    -> defines_only_universes inh ts
    -> ccomputes_to_valc_ext inh lib T (mkc_cequiv A B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_cequiv inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_cequiv_r {p} :
  forall inh (ts : cts(p)) lib T A B T' eq,
    type_system inh ts
    -> defines_only_universes inh ts
    -> ccomputes_to_valc_ext inh lib T' (mkc_cequiv A B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_cequiv inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar_per_cequiv; eauto; eauto 3 with slow.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply reca; eauto 3 with slow.
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
