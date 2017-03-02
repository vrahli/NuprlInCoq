(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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

  Authors: Abhishek Anand & Vincent Rahli

*)

(*
Require Export nuprl_props.
Require Export choice.
Require Export cvterm.

Require Export alphaeq5.
Require Export cvterm.
Require Export nat_defs.
Require Export types_converge.

Require Export sequents_tacs.
Require Import cequiv_tacs.
Require Import subst_tacs.

Require Export per_props_set.
Require Export per_props_union.
Require Export per_props3.

Require Export subst_per.

Require Export list.  (* ??? *)
 *)


Require Export cequiv_props4.
Require Export continuity_defs_ceq.
Require Export cequiv_seq_util.

Require Export per_props_nat0.
Require Export per_props_product.


Lemma zero_as_integer {o} :
  @mkc_zero o = mkc_integer (Z.of_nat 0).
Proof.
  rw @mkc_zero_eq; rw @mkc_nat_eq; auto.
Qed.

Lemma inhabited_type_le_zero_zero {o} :
  forall lib, @inhabited_type o lib (mkc_le mkc_zero mkc_zero).
Proof.
  introv.
  apply inhabited_le.
  exists (Z.of_nat 0) (Z.of_nat 0).
  rw @zero_as_integer.
  dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); omega.
Qed.
Hint Resolve inhabited_type_le_zero_zero.

Lemma isprogram_prod {o} :
  forall (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_prod a b).
Proof.
  introv isp1 isp2; apply isprog_eq; apply isprog_prod; eauto 2 with slow.
Qed.
Hint Resolve isprogram_prod : slow.

Lemma implies_approx_star_bterm_nobnd {o} :
  forall lib op (t1 t2 : @NTerm o),
    op <> NCan NFresh
    -> approx_star lib t1 t2
    -> approx_star_bterm lib op (nobnd t1) (nobnd t2).
Proof.
  introv d apr.
  exists ([] : list NVar) t1 t2.
  dands; unfold nobnd; eauto 2 with slow.
  left; dands; auto.
Qed.

Lemma implies_cequivc_mkc_prod {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_prod a1 b1) (mkc_prod a2 b2).
Proof.
  introv ceq1 ceq2.
  destruct_cterms.
  unfold cequivc in *; simpl in *.
  destruct ceq1 as [c1 c2].
  destruct ceq2 as [c3 c4].
  split; apply howetheorem1; try (apply isprogram_prod; eauto 2 with slow).

  - apply approx_star_congruence3;[|apply isprogram_prod; eauto 2 with slow].
    repeat (apply approx_starbts_cons; dands); auto;
      try (apply approx_starbts_nil).

    + apply implies_approx_star_bterm_nobnd;[intro xx; inversion xx|].
      apply le_bin_rel_approx1_eauto; auto.

    + rewrite (newvar_prog x0); auto.
      rewrite (newvar_prog x); auto.
      exists [nvarx] x0 x; dands; eauto 2 with slow.
      left; dands; [intro xx; inversion xx|].
      apply le_bin_rel_approx1_eauto; auto.

  - apply approx_star_congruence3;[|apply isprogram_prod; eauto 2 with slow].
    repeat (apply approx_starbts_cons; dands); auto;
      try (apply approx_starbts_nil).

    + apply implies_approx_star_bterm_nobnd;[intro xx; inversion xx|].
      apply le_bin_rel_approx1_eauto; auto.

    + rewrite (newvar_prog x0); auto.
      rewrite (newvar_prog x); auto.
      exists [nvarx] x x0; dands; eauto 2 with slow.
      left; dands; [intro xx; inversion xx|].
      apply le_bin_rel_approx1_eauto; auto.
Qed.

Lemma implies_approx_mk_le {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib (mk_le a1 b1) (mk_le a2 b2).
Proof.
  introv apra aprb.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  repnd.

  apply approx_open_approx; allrw @isprogram_eq; try (apply isprog_le_implies); auto.
  apply approx_open_mk_le; apply approx_implies_approx_open; auto.
Qed.

Lemma implies_cequiv_mk_le {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_le a1 b1) (mk_le a2 b2).
Proof.
  introv ceqa ceqb.
  allunfold @cequiv; allsimpl; repnd; dands; apply implies_approx_mk_le; auto.
Qed.

Lemma implies_cequivc_mkc_le {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_le a1 b1) (mkc_le a2 b2).
Proof.
  introv ceqa ceqb.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply implies_cequiv_mk_le; auto.
Qed.

Lemma implies_approx_mk_less_than {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib (mk_less_than a1 b1) (mk_less_than a2 b2).
Proof.
  introv apra aprb.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  repnd.

  apply approx_open_approx; allrw @isprogram_eq; try (apply isprog_less_than_implies); auto.
  apply approx_open_mk_less_than; apply approx_implies_approx_open; auto.
Qed.

Lemma implies_cequiv_mk_less_than {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_less_than a1 b1) (mk_less_than a2 b2).
Proof.
  introv ceqa ceqb.
  allunfold @cequiv; allsimpl; repnd; dands; apply implies_approx_mk_less_than; auto.
Qed.

Lemma implies_cequivc_mkc_less_than {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_less_than a1 b1) (mkc_less_than a2 b2).
Proof.
  introv ceqa ceqb.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply implies_cequiv_mk_less_than; auto.
Qed.

Lemma integer_in_int {o} :
  forall lib i, @equality o lib (mkc_integer i) (mkc_integer i) mkc_int.
Proof.
  introv.
  apply equality_in_int.
  exists i.
  dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); omega.
Qed.
Hint Resolve integer_in_int : slow.

Lemma ext_eq_natk_set_iff {o} :
  forall lib (t1 t2 : @CTerm o) n1 n2,
    computes_to_valc lib t1 (mkc_integer n1)
    -> computes_to_valc lib t2 (mkc_integer n2)
    ->
    (
      ext_eq
        lib
        (mkc_set mkc_int nvarx
                 (mkcv_prod [nvarx] (mkcv_le [nvarx] (mkcv_zero [nvarx]) (mkc_var nvarx))
                            (mkcv_less_than [nvarx] (mkc_var nvarx) (mk_cv [nvarx] t1))))
        (mkc_set mkc_int nvarx
                 (mkcv_prod [nvarx] (mkcv_le [nvarx] (mkcv_zero [nvarx]) (mkc_var nvarx))
                            (mkcv_less_than [nvarx] (mkc_var nvarx) (mk_cv [nvarx] t2))))
        <=>
        (forall (m : nat), (Z.of_nat m < n1)%Z <=> (Z.of_nat m < n2)%Z)
    ).
Proof.
  introv comp1 comp2.
  split; intro h.

  - introv.

    split; intro w.

    + pose proof (h (@mkc_integer o (Z.of_nat m)) (@mkc_integer o (Z.of_nat m))) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp.

      {
        apply equality_in_set.

        dands; eauto 2 with slow.

        {
          introv ea.
          apply equality_in_int in ea.
          unfold equality_of_int in ea; exrepnd; spcast.

          eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
          eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
          autorewrite with slow.

          eapply tequality_respects_cequivc_left;
            [apply cequivc_sym;apply implies_cequivc_mkc_prod;
             [apply implies_cequivc_mkc_le;
              [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
             |apply implies_cequivc_mkc_less_than;
              [apply computes_to_valc_implies_cequivc;exact ea1
              |apply computes_to_valc_implies_cequivc;exact comp1]
             ]
            |].
          eapply tequality_respects_cequivc_right;
            [apply cequivc_sym;apply implies_cequivc_mkc_prod;
             [apply implies_cequivc_mkc_le;
              [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
             |apply implies_cequivc_mkc_less_than;
              [apply computes_to_valc_implies_cequivc;exact ea0
              |apply computes_to_valc_implies_cequivc;exact comp1]
             ]
            |].

          clear dependent a.
          clear dependent a'.
          clear dependent t1.

          rw @fold_type.
          apply type_mkc_prod; dands; eauto 2 with slow.

          {
            apply type_mkc_le.
            exists (Z.of_nat 0) k.
            rw @zero_as_integer.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          }

          {
            introv inh.
            apply type_mkc_less_than.
            exists k n1.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          }
        }

        {
          eapply inhabited_type_respects_alphaeqc;
            [apply alphaeqc_sym;apply mkcv_prod_substc|].
          autorewrite with slow.

          apply inhabited_prod; dands.

          { apply inhabited_le.
            exists (Z.of_nat 0) (Z.of_nat m).
            rw @zero_as_integer.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
            apply inj_le; omega. }

          { apply inhabited_less_than.
            exists (Z.of_nat m) n1.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto. }
        }
      }

      {
        apply equality_in_set in q; repnd.
        clear q0 q1.

        eapply inhabited_type_respects_alphaeqc in q;[|apply mkcv_prod_substc].
        autorewrite with slow in q.

        apply inhabited_prod in q; repnd.
        apply inhabited_le in q0; exrepnd.
        apply inhabited_less_than in q; exrepnd.
        spcast.
        rw @zero_as_integer in q1.
        repeat computes_to_eqval.

        apply computes_to_valc_isvalue_eq in q1; eauto 2 with slow.
        apply mkc_integer_eq in q1; subst.

        apply computes_to_valc_isvalue_eq in q2; eauto 2 with slow.
        apply mkc_integer_eq in q2; subst.
        omega.
      }

    + pose proof (h (@mkc_integer o (Z.of_nat m)) (@mkc_integer o (Z.of_nat m))) as q.
      destruct q as [q' q]; clear q'.
      autodimp q hyp.

      {
        apply equality_in_set.

        dands; eauto 2 with slow.

        {
          introv ea.
          apply equality_in_int in ea.
          unfold equality_of_int in ea; exrepnd; spcast.

          eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
          eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
          autorewrite with slow.

          eapply tequality_respects_cequivc_left;
            [apply cequivc_sym;apply implies_cequivc_mkc_prod;
             [apply implies_cequivc_mkc_le;
              [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
             |apply implies_cequivc_mkc_less_than;
              [apply computes_to_valc_implies_cequivc;exact ea1
              |apply computes_to_valc_implies_cequivc;exact comp2]
             ]
            |].
          eapply tequality_respects_cequivc_right;
            [apply cequivc_sym;apply implies_cequivc_mkc_prod;
             [apply implies_cequivc_mkc_le;
              [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
             |apply implies_cequivc_mkc_less_than;
              [apply computes_to_valc_implies_cequivc;exact ea0
              |apply computes_to_valc_implies_cequivc;exact comp2]
             ]
            |].

          clear dependent a.
          clear dependent a'.
          clear dependent t2.

          rw @fold_type.
          apply type_mkc_prod; dands; eauto 2 with slow.

          {
            apply type_mkc_le.
            exists (Z.of_nat 0) k.
            rw @zero_as_integer.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          }

          {
            introv inh.
            apply type_mkc_less_than.
            exists k n2.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          }
        }

        {
          eapply inhabited_type_respects_alphaeqc;
            [apply alphaeqc_sym;apply mkcv_prod_substc|].
          autorewrite with slow.

          apply inhabited_prod; dands.

          { apply inhabited_le.
            exists (Z.of_nat 0) (Z.of_nat m).
            rw @zero_as_integer.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
            apply inj_le; omega. }

          { apply inhabited_less_than.
            exists (Z.of_nat m) n2.
            dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto. }
        }
      }

      {
        apply equality_in_set in q; repnd.
        clear q0 q1.

        eapply inhabited_type_respects_alphaeqc in q;[|apply mkcv_prod_substc].
        autorewrite with slow in q.

        apply inhabited_prod in q; repnd.
        apply inhabited_le in q0; exrepnd.
        apply inhabited_less_than in q; exrepnd.
        spcast.
        rw @zero_as_integer in q1.
        repeat computes_to_eqval.

        apply computes_to_valc_isvalue_eq in q1; eauto 2 with slow.
        apply mkc_integer_eq in q1; subst.

        apply computes_to_valc_isvalue_eq in q2; eauto 2 with slow.
        apply mkc_integer_eq in q2; subst.
        omega.
      }

  - introv; split; intro q.

    + apply equality_in_set in q; repnd.
      apply equality_in_set; dands; auto.

      {
        introv ea.
        apply equality_in_int in ea.
        unfold equality_of_int in ea; exrepnd; spcast.

        eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
        eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
        autorewrite with slow.

        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;apply implies_cequivc_mkc_prod;
           [apply implies_cequivc_mkc_le;
            [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
           |apply implies_cequivc_mkc_less_than;
            [apply computes_to_valc_implies_cequivc;exact ea1
            |apply computes_to_valc_implies_cequivc;exact comp2]
           ]
          |].
        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;apply implies_cequivc_mkc_prod;
           [apply implies_cequivc_mkc_le;
            [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
           |apply implies_cequivc_mkc_less_than;
            [apply computes_to_valc_implies_cequivc;exact ea0
            |apply computes_to_valc_implies_cequivc;exact comp2]
           ]
          |].

        clear dependent a.
        clear dependent a'.
        clear dependent t1.
        clear dependent t2.

        rw @fold_type.
        apply type_mkc_prod; dands; eauto 2 with slow.

        {
          apply type_mkc_le.
          exists (Z.of_nat 0) k.
          rw @zero_as_integer.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
        }

        {
          introv inh.
          apply type_mkc_less_than.
          exists k n2.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
        }
      }

      {
        eapply inhabited_type_respects_alphaeqc;
          [apply alphaeqc_sym;apply mkcv_prod_substc|].
        eapply inhabited_type_respects_alphaeqc in q;[|apply mkcv_prod_substc].
        autorewrite with slow in *.

        apply inhabited_prod in q; repnd.
        apply inhabited_le in q2; exrepnd.
        apply inhabited_less_than in q; exrepnd.
        spcast.
        rw @zero_as_integer in q3.
        repeat computes_to_eqval.

        apply computes_to_valc_isvalue_eq in q3; eauto 2 with slow.
        apply mkc_integer_eq in q3; subst.

        apply Z_of_nat_complete in q2; exrepnd; subst.

        apply inhabited_prod; dands.

        { apply inhabited_le.
          exists (Z.of_nat 0) (Z.of_nat n).
          rw @zero_as_integer.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          apply inj_le; omega. }

        { apply inhabited_less_than.
          exists (Z.of_nat n) n2.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          apply h; auto. }
      }

    + apply equality_in_set in q; repnd.
      apply equality_in_set; dands; auto.

      {
        introv ea.
        apply equality_in_int in ea.
        unfold equality_of_int in ea; exrepnd; spcast.

        eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
        eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
        autorewrite with slow.

        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;apply implies_cequivc_mkc_prod;
           [apply implies_cequivc_mkc_le;
            [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
           |apply implies_cequivc_mkc_less_than;
            [apply computes_to_valc_implies_cequivc;exact ea1
            |apply computes_to_valc_implies_cequivc;exact comp1]
           ]
          |].
        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;apply implies_cequivc_mkc_prod;
           [apply implies_cequivc_mkc_le;
            [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
           |apply implies_cequivc_mkc_less_than;
            [apply computes_to_valc_implies_cequivc;exact ea0
            |apply computes_to_valc_implies_cequivc;exact comp1]
           ]
          |].

        clear dependent a.
        clear dependent a'.
        clear dependent t1.
        clear dependent t2.

        rw @fold_type.
        apply type_mkc_prod; dands; eauto 2 with slow.

        {
          apply type_mkc_le.
          exists (Z.of_nat 0) k.
          rw @zero_as_integer.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
        }

        {
          introv inh.
          apply type_mkc_less_than.
          exists k n1.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
        }
      }

      {
        eapply inhabited_type_respects_alphaeqc;
          [apply alphaeqc_sym;apply mkcv_prod_substc|].
        eapply inhabited_type_respects_alphaeqc in q;[|apply mkcv_prod_substc].
        autorewrite with slow in *.

        apply inhabited_prod in q; repnd.
        apply inhabited_le in q2; exrepnd.
        apply inhabited_less_than in q; exrepnd.
        spcast.
        rw @zero_as_integer in q3.
        repeat computes_to_eqval.

        apply computes_to_valc_isvalue_eq in q3; eauto 2 with slow.
        apply mkc_integer_eq in q3; subst.

        apply Z_of_nat_complete in q2; exrepnd; subst.

        apply inhabited_prod; dands.

        { apply inhabited_le.
          exists (Z.of_nat 0) (Z.of_nat n).
          rw @zero_as_integer.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          apply inj_le; omega. }

        { apply inhabited_less_than.
          exists (Z.of_nat n) n1.
          dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
          apply h; auto. }
      }
Qed.

Lemma tequality_mkc_natk {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib (mkc_natk t1) (mkc_natk t2)
    <=> {k1 : Z , {k2 : Z
         , t1 ===>(lib) (mkc_integer k1)
         # t2 ===>(lib) (mkc_integer k2)
         # (forall (k : Z), (0 <= k)%Z -> ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z) }}.
Proof.
  introv.
  allrw @mkc_natk_eq.
  allrw @tequality_set.

  split; intro k; repnd; dands; auto; eauto 2 with slow; GC.

  - pose proof (k2 (@mkc_zero o) (@mkc_zero o)) as q.
    autodimp q hyp; eauto 2 with slow.
    eapply tequality_respects_alphaeqc_left in q;[|apply mkcv_prod_substc].
    eapply tequality_respects_alphaeqc_right in q;[|apply mkcv_prod_substc].
    autorewrite with slow in q.

    pose proof (k3 (@mkc_zero o) (@mkc_zero o)) as h.
    autodimp h hyp; eauto 2 with slow.
    eapply tequality_respects_alphaeqc_left in h;[|apply mkcv_prod_substc].
    eapply tequality_respects_alphaeqc_right in h;[|apply mkcv_prod_substc].
    autorewrite with slow in h.

    apply tequality_mkc_prod in q.
    apply tequality_mkc_prod in h.
    repnd; GC.
    clear q0 q h.

    autodimp q2 hyp; eauto 2 with slow.
    autodimp h2 hyp; eauto 2 with slow.

    apply type_mkc_less_than in q2.
    apply type_mkc_less_than in h2.
    exrepnd; spcast.
    clear ka0 q0 ka h0.

    exists kb0 kb; dands; spcast; auto.

    introv h.
    apply Z_of_nat_complete in h; exrepnd; subst.

    destruct (Z_lt_le_dec (Z.of_nat n) kb0); tcsp.

    + eapply ext_eq_natk_set_iff in k;[|eauto|eauto].
      applydup k in l; clear k; tcsp.

    + destruct (Z_lt_le_dec (Z.of_nat n) kb); tcsp.
      assert False; tcsp.
      eapply ext_eq_natk_set_iff in k;[|eauto|eauto].
      applydup k in l0; clear k; tcsp; try omega.

  - exrepnd; spcast.
    introv ea.
    apply equality_in_int in ea.
    unfold equality_of_int in ea; exrepnd; spcast.

    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
    autorewrite with slow.

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ea1
        |apply computes_to_valc_implies_cequivc;exact k0]
       ]
      |].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ea0
        |apply computes_to_valc_implies_cequivc;exact k0]
       ]
      |].

    clear dependent a.
    clear dependent a'.
    clear dependent t1.

    rw @fold_type.
    apply type_mkc_prod; dands; eauto 2 with slow.

    {
      apply type_mkc_le.
      exists (Z.of_nat 0) k.
      rw @zero_as_integer.
      dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
    }

    {
      introv inh.
      apply type_mkc_less_than.
      exists k k1.
      dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
    }

  - exrepnd; spcast.
    introv ea.
    apply equality_in_int in ea.
    unfold equality_of_int in ea; exrepnd; spcast.

    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
    autorewrite with slow.

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea1]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ea1
        |apply computes_to_valc_implies_cequivc;exact k4]
       ]
      |].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ea0]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ea0
        |apply computes_to_valc_implies_cequivc;exact k4]
       ]
      |].

    clear dependent a.
    clear dependent a'.
    clear dependent t2.

    rw @fold_type.
    apply type_mkc_prod; dands; eauto 2 with slow.

    {
      apply type_mkc_le.
      exists (Z.of_nat 0) k.
      rw @zero_as_integer.
      dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
    }

    {
      introv inh.
      apply type_mkc_less_than.
      exists k k2.
      dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow); try omega; auto.
    }

  - exrepnd; spcast.
    eapply ext_eq_natk_set_iff;[eauto|eauto|].
    introv.
    pose proof (k3 (Z.of_nat m)) as h; clear k3; autodimp h hyp; try omega.

    split; intro q; repndors; repnd; tcsp; try omega.
Qed.

Lemma type_mkc_natk {o} :
  forall lib (t : @CTerm o),
    type lib (mkc_natk t)
    <=> {k : Z , t ===>(lib) (mkc_integer k)}.
Proof.
  introv.
  rw <- @fold_type.
  rw @tequality_mkc_natk; split; introv h; exrepnd; spcast; repeat computes_to_eqval.
  - exists k1; spcast; auto.
  - exists k k; dands; spcast; auto.
    introv i.
    destruct (Z_lt_le_dec k0 k); tcsp.
Qed.

Lemma inhabited_prod {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # type lib B
     # inhabited_type lib A
     # inhabited_type lib B).
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd.

  - apply equality_in_prod in k0; exrepnd; spcast.
    autodimp k2 hyp.
    { allapply @inhabited_type_if_equality; auto. }
    allapply @equality_refl.
    dands; auto; eexists; eauto.

  - exists (mkc_pair t0 t).
    apply equality_in_prod; dands; auto.
    exists t0 t0 t t; dands; spcast; tcsp;
    apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma inhabited_prod2 {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # inhabited_type lib A
     # type lib B
     # inhabited_type lib B).
Proof.
  introv.
  rw @inhabited_prod; split; sp.
Qed.

Lemma equality_in_natk {o} :
  forall lib (a b t : @CTerm o),
    equality lib a b (mkc_natk t)
    <=> {m : nat , {k : Z
         , a ===>(lib) (mkc_nat m)
         # b ===>(lib) (mkc_nat m)
         # t ===>(lib) (mkc_integer k)
         # (Z.of_nat m < k)%Z }} .
Proof.
  introv.
  rw @mkc_natk_eq.
  rw @equality_in_set.

  split; intro h; exrepnd; dands.

  - allrw @equality_in_int.
    unfold equality_of_int in h1; exrepnd; spcast.
    eapply inhabited_type_respects_alphaeqc in h;[|apply mkcv_prod_substc].
    autorewrite with slow in *.
    allrw @inhabited_prod; repnd.
    allrw @inhabited_le; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in h6; eauto with slow.
    rw @mkc_zero_eq in h6; rw @mkc_nat_eq in h6; ginv.
    computes_to_eqval.
    allrw @inhabited_less_than; exrepnd; spcast.
    computes_to_eqval.
    exists (Z.to_nat k) kb; dands; spcast; tcsp;
    try (complete (rw @mkc_nat_eq; rw Znat.Z2Nat.id; auto)).
    rw Znat.Z2Nat.id; auto.

  - introv ei.
    allrw @equality_in_int.
    unfold equality_of_int in ei; exrepnd; spcast.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    autorewrite with slow.

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ei1]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ei1
        |apply computes_to_valc_implies_cequivc;exact h3]
       ]
      |].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply implies_cequivc_mkc_prod;
       [apply implies_cequivc_mkc_le;
        [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact ei0]
       |apply implies_cequivc_mkc_less_than;
        [apply computes_to_valc_implies_cequivc;exact ei0
        |apply computes_to_valc_implies_cequivc;exact h3]
       ]
      |].

    apply fold_type.
    allrw @type_mkc_prod; dands; eauto 2 with slow.

    + allrw @type_mkc_le.
      exists 0%Z k0.
      dands; tcsp; spcast; auto;
        try (rw @mkc_zero_eq; rw @mkc_nat_eq; simpl);
        apply computes_to_valc_refl; eauto with slow.

    + introv inh.
      allrw @inhabited_le; exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in inh0; eauto with slow.
      rw @mkc_zero_eq in inh0; rw @mkc_nat_eq in inh0; ginv.
      apply type_mkc_less_than.
      exists k0 k; dands; spcast; auto;
        apply computes_to_valc_refl; eauto with slow.

  - spcast.
    apply equality_in_int; unfold equality_of_int.
    exists (Z.of_nat m); dands; spcast; auto.

  - spcast.
    eapply inhabited_type_respects_alphaeqc;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    autorewrite with slow.
    apply inhabited_prod.
    allrw @type_mkc_le.
    allrw @type_mkc_less_than.
    allrw @inhabited_le.
    allrw @inhabited_less_than.
    dands.

    + exists 0%Z (Z.of_nat m); dands; spcast.
      * rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.
      * allrw @mkc_nat_eq; auto.

    + exists (Z.of_nat m) k; dands; spcast; auto.

    + exists 0%Z (Z.of_nat m); dands; spcast; tcsp; try omega.
      rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.

    + exists (Z.of_nat m) k; dands; spcast; auto.
Qed.

Lemma cequivc_mkc_isl {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_isl t) (mkc_isl u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_isl, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_assert {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_assert t) (mkc_assert u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_assert, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inl_implies_cequivc_isl_tt {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inl u)
    -> cequivc lib (mkc_isl t) tt.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inr_implies_cequivc_isl_ff {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inr u)
    -> cequivc lib (mkc_isl t) ff.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma implies_isl_in_bool {o} :
  forall lib (A B a b : @CTerm o),
    equality lib a b (mkc_union A B)
    -> equality lib (mkc_isl a) (mkc_isl b) mkc_bool.
Proof.
  introv e.
  apply equality_mkc_union in e; exrepnd.
  apply equality_in_bool.
  repndors; exrepnd; spcast;[left|right]; dands; spcast.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
Qed.

Lemma tt_not_approx_ff {o} :
  forall (lib : @library o), !approx lib mk_btrue mk_bfalse.
Proof.
  introv apr.
  inversion apr as [cl]; clear apr.
  unfold close_comput in cl; repnd.
  unfold close_compute_val in cl2.
  pose proof (cl2 (NInj NInl) [nobnd mk_axiom]) as h; fold_terms.
  autodimp h hyp; eauto 3 with slow.
  exrepnd.
  apply computes_to_value_isvalue_eq in h1; ginv; eauto 3 with slow.
Qed.

Lemma tt_not_cequiv_ff {o} :
  forall (lib : @library o), !cequiv lib mk_btrue mk_bfalse.
Proof.
  introv ceq.
  apply cequiv_le_approx in ceq.
  apply tt_not_approx_ff in ceq; sp.
Qed.

Lemma tt_not_cequivc_ff {o} :
  forall (lib : @library o), !cequivc lib tt ff.
Proof.
  introv.
  unfold cequivc; simpl.
  apply tt_not_cequiv_ff.
Qed.

Lemma equality_tt_in_bool_implies_cequiv {o} :
  forall lib (t : @CTerm o),
    equality lib t tt mkc_bool
    -> ccequivc lib t tt.
Proof.
  introv e.
  apply equality_in_bool in e; repndors; repnd; spcast; eauto with slow.
  apply tt_not_cequivc_ff in e; sp.
Qed.

Lemma isprogram_mk_assert {o} :
  forall (t : @NTerm o),
    isprogram (mk_assert t) <=> isprogram t.
Proof.
  introv.
  unfold mk_assert.
  rw @isprogram_decide_iff2; split; intro k; repnd; tcsp; dands; auto;
  apply isprog_vars_isprogrambt;
  apply isprog_vars_if_isprog; eauto 3 with slow.
Qed.

Lemma mkc_assert_tt {o} :
  forall (lib : @library o), cequivc lib (mkc_assert tt) mkc_unit.
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_mk_assert.
  apply isprogram_inl; eauto with slow.
Qed.

Lemma inhabited_type_mkc_unit {o} :
  forall (lib : @library o), inhabited_type lib mkc_unit.
Proof.
  introv.
  unfold inhabited_type.
  exists (@mkc_axiom o).
  apply equality_in_unit; dands; spcast;
  apply computes_to_valc_refl; eauto with slow.
Qed.
Hint Resolve inhabited_type_mkc_unit : slow.

Lemma equality_mkc_inl_implies {o} :
  forall lib (t1 t2 A B : @CTerm o),
    equality lib (mkc_inl t1) (mkc_inl t2) (mkc_union A B)
    -> equality lib t1 t2 A.
Proof.
  introv e.
  apply equality_mkc_union in e; repnd.
  repndors; exrepnd; spcast;
  apply computes_to_valc_isvalue_eq in e2; eauto 3 with slow;
  apply computes_to_valc_isvalue_eq in e4; eauto 3 with slow;
  eqconstr e2; eqconstr e4; auto.
Qed.

Lemma type_tnat {o} :
  forall (lib : @library o), type lib mkc_tnat.
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply tequality_set; dands; auto.
  { apply tequality_int. }

  introv e.
  allrw @substc_mkcv_le.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  apply equality_in_int in e.
  unfold equality_of_int in e; exrepnd; spcast.

  apply tequality_mkc_le.
  exists (0%Z) k (0%Z) k; dands; spcast; tcsp.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - destruct (Z_le_gt_dec 0 k); tcsp.
    right; dands; omega.
Qed.
Hint Resolve type_tnat : slow.

Definition equality_of_nat {p} lib (n m : @CTerm p) :=
  {k : nat , n ===>(lib) (mkc_nat k)
           # m ===>(lib) (mkc_nat k)}.

Lemma equality_in_tnat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    <=> equality_of_nat lib a b.
Proof.
  introv.
  rw @mkc_tnat_eq.
  rw @equality_in_set.
  rw @equality_in_int.
  unfold equality_of_int, equality_of_nat.
  rw @substc_mkcv_le.
  rw @substc_mkcv_zero.
  rw @mkc_var_substc.
  rw @inhabited_le.
  split; introv k; exrepnd; spcast; dands;
  repeat computes_to_eqval;
  computes_to_value_isvalue; ginv.
  - inversion k2; subst.
    apply Wf_Z.Z_of_nat_complete in k3; exrepnd; subst.
    exists n; dands; spcast; auto.
  - introv e.
    allrw @substc_mkcv_le.
    allrw @substc_mkcv_zero.
    allrw @mkc_var_substc.
    apply equality_in_int in e.
    unfold equality_of_int in e; exrepnd; spcast.
    apply tequality_mkc_le.
    exists (0%Z) k (0%Z) k; dands; spcast; auto;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
    destruct (Z_le_gt_dec 0 k); sp.
    right; sp; omega.
  - exists (Z.of_nat k0); dands; spcast; auto.
  - exists (0%Z) (Z.of_nat k0); dands; spcast; auto;
    try omega;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
Qed.

Lemma equality_in_int_and_inhabited_le_implies_equality_in_nat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> inhabited_type lib (mkc_le mkc_zero a)
    -> equality lib a b mkc_tnat.
Proof.
  introv e inh.
  apply equality_in_tnat.
  apply equality_in_int in e.
  apply inhabited_le in inh.
  unfold equality_of_nat.
  unfold equality_of_int in e.
  exrepnd; spcast.
  repeat computes_to_eqval.
  computes_to_value_isvalue; ginv.
  inversion inh0; subst.
  apply Wf_Z.Z_of_nat_complete in inh1; exrepnd; subst.
  exists n; dands; spcast; auto.
Qed.

Lemma equality_of_nat_implies_equality_of_int {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2
    -> equality_of_int lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  unfold equality_of_int.
  allrw @mkc_nat_eq.
  exists (Z.of_nat k); dands; spcast; auto.
Qed.

Lemma equality_in_int_implies_cequiv {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> cequivc lib a b.
Proof.
  introv e.
  apply equality_in_int in e.
  apply equality_of_int_imp_tt in e.
  unfold equality_of_int_tt in e; exrepnd.
  destruct_cterms; allunfold @computes_to_valc; allunfold @cequivc; allsimpl.
  allunfold @computes_to_value; repnd.
  apply (cequiv_trans _ _ (mk_integer k)).
  - apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
  - apply cequiv_sym.
    apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
Qed.

Lemma member_product2 {o} :
  forall lib (p : @CTerm o) A v B,
    member lib p (mkc_product A v B)
    <=>
    (type lib (mkc_product A v B)
     # {a, b : CTerm
        , p ===>(lib) (mkc_pair a b)
        # member lib a A
        # member lib b (substc a v B)}).
Proof.
  introv.
  rw @equality_in_product; split; intro k; exrepnd.
  - dands; auto.
    + apply tequality_product; auto.
    + allapply @equality_refl.
      exists a1 b1; dands; auto.
  - apply @tequality_product in k0; repnd.
    dands; auto.
    exists a a b b; dands; auto.
Qed.

Lemma equality_in_ufun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_ufun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (inhabited_type lib A -> equality lib f g B)).
Proof.
  introv.
  rw <- @fold_mkc_ufun.
  rw @equality_in_isect.
  split; intro k; repnd; dands; auto.

  - introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.

  - introv e.
    unfold inhabited_type in e; exrepnd.
    unfold member in e0.
    apply k in e0.
    repeat (rw @csubst_mk_cv in e0); sp.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp.
    exists a; apply equality_refl in e; auto.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    apply k.
    exists a; apply equality_refl in e; auto.
Qed.
