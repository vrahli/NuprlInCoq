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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export substc_more.
Require Export per_props4.
Require Export seq_util.

Definition mkcv_natk2nat {o} vs (t : @CVTerm o vs) :=
  mkcv_fun vs (mkcv_natk vs t) (mkcv_tnat vs).

Hint Rewrite @mkc_var_substc : slow.
Hint Rewrite @mkcv_tnat_substc : slow.
Hint Rewrite @lsubstc_mkc_tnat : slow.
Hint Rewrite @csubst_mk_cv : slow.
Hint Rewrite @substc2_mk_cv : slow.
Hint Rewrite @substc2_apply2 : slow.
Hint Rewrite @substc2_mk_cv : slow.
Hint Rewrite @mkcv_apply2_substc : slow.
Hint Rewrite @lsubstc_vars_mk_tnat_as_mkcv : slow.

Lemma substc_mkcv_natk2nat {o} :
  forall v (t : @CVTerm o [v]) a,
    alphaeqc
      (substc a v (mkcv_natk2nat [v] t))
      (natk2nat (substc a v t)).
Proof.
  introv; unfold mkcv_natk2nat.
  eapply alphaeqc_trans;[apply substc_mkcv_fun|].
  unfold natk2nat.
  autorewrite with slow.
  apply alphaeqc_mkc_fun; eauto 3 with slow.
  eapply alphaeqc_trans;[apply mkcv_natk_substc|].
  eauto 3 with slow.
Qed.

Lemma type_implies_tequality_refl {o} :
  forall lib (t : @CTerm o),
    type lib t -> tequality lib t t.
Proof.
  sp.
Qed.
Hint Resolve type_implies_tequality_refl : slow.

Lemma lsubstc_vars_mk_fun_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & alphaeqcv
         vs
         (lsubstc_vars (mk_fun t1 t2) w s vs c)
         (mkcv_fun
            vs
            (lsubstc_vars t1 w1 s vs c1)
            (lsubstc_vars t2 w2 s vs c2))}}}}.
Proof.
  introv.

  dup w as w'.
  rw @wf_fun_iff in w'; repnd.
  exists w'0 w'.

  dup c as c'.
  rw @cover_vars_upto_fun in c'; repnd.
  exists c'0 c'.

  unfold alphaeqcv; simpl.
  unfold csubst.
  repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
  simpl.
  autorewrite with slow.
  fold_terms.
  rewrite cl_lsubst_aux_swap_filter; eauto 3 with slow.

  { apply alphaeq_function_fun.
    apply disjoint_singleton_l; intro i.
    apply free_vars_lsubst_aux_subset in i.
    rewrite sub_free_vars_if_cl_sub in i; eauto 3 with slow.
    autorewrite with slow in *.
    apply in_remove_nvars in i; repnd.
    apply newvar_prop in i0; tcsp. }

  { apply disjoint_singleton_r; apply newvar_prop. }
Qed.

Lemma alphaeqcv_trans {o} :
  forall vs (t1 t2 t3 : @CVTerm o vs),
    alphaeqcv vs t1 t2
    -> alphaeqcv vs t2 t3
    -> alphaeqcv vs t1 t3.
Proof.
  introv aeq1 aeq2.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  eapply alpha_eq_trans; eauto.
Qed.

Lemma alphaeq_mk_fun {o} :
  forall a b c d : @NTerm o,
    alphaeq a b
    -> alphaeq c d
    -> alphaeq (mk_fun a c) (mk_fun b d).
Proof.
  introv aeq1 aeq2.
  constructor; simpl; auto.
  introv j.
  apply alphaeqbt_eq.
  repeat (destruct n; tcsp; try omega); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2.
    apply alphaeq_eq; auto.
  - pose proof (ex_fresh_var (all_vars c ++ all_vars d)) as h; exrepnd.
    apply (al_bterm_aux [v]); simpl; auto.
    + apply disjoint_singleton_l; auto.
    + repeat (rewrite lsubst_aux_trivial_cl_term); simpl; auto.
      * apply alphaeq_eq; auto.
      * apply disjoint_singleton_r.
        apply newvar_prop.
      * apply disjoint_singleton_r.
        apply newvar_prop.
Qed.

Lemma alpha_eq_mk_fun {o} :
  forall a b c d : @NTerm o,
    alpha_eq a b
    -> alpha_eq c d
    -> alpha_eq (mk_fun a c) (mk_fun b d).
Proof.
  introv aeq1 aeq2.
  allrw <- @alphaeq_eq.
  apply alphaeq_mk_fun; auto.
Qed.

Lemma alpha_eq_csubst_mk_natk {o} :
  forall (t : @NTerm o) s,
    alpha_eq (csubst (mk_natk t) s) (mk_natk (csubst t s)).
Proof.
  introv.
  unfold csubst.
  repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
  unfold mk_natk, mk_natk_aux.
  simpl; autorewrite with slow.
  fold_terms.
  unfold mk_natk, mk_natk_aux.
  prove_alpha_eq4.
  introv h.
  repeat (destruct n; tcsp; try omega).
  allrw @sub_find_sub_filter_eq; autorewrite with slow.
  boolvar; tcsp.

  {
    pose proof (newvar_prop t) as p1.
    pose proof (newvar_prop (mk_less_than (vterm (newvar t)) t)) as p2.
    allsimpl; autorewrite with slow in *.
    allrw not_over_or; repnd; tcsp.
  }

  {
    clear Heqb.
    rewrite <- sub_filter_app_r; simpl.

    remember (newvar t) as nv1.
    pose proof (newvar_prop t) as p1.
    rewrite <- Heqnv1 in p1.

    remember (newvar (mk_less_than (vterm nv1) t)) as nv2.
    pose proof (newvar_prop (mk_less_than (vterm nv1) t)) as p2.
    rewrite <- Heqnv2 in p2.

    remember (newvar (lsubst_aux t (csub2sub s))) as nv3.
    pose proof (newvar_prop (lsubst_aux t (csub2sub s))) as p3.
    rewrite <- Heqnv3 in p3.

    remember (newvar (@mk_void o)) as nv4.
    pose proof (newvar_prop (@mk_void o)) as p4.
    rewrite <- Heqnv4 in p4.

    pose proof (ex_fresh_var (nv1
       :: (remove_nvars [nv2]
             (nv1
              :: free_vars
                   (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2]))) ++
           nvarx
           :: nv4
              :: nvarx
                 :: nv2
                    :: bound_vars
                         (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2])) ++
                       [nvarx]) ++
          all_vars
            (mk_prod (mk_le mk_zero (vterm nv3))
               (mk_less_than (vterm nv3) (lsubst_aux t (csub2sub s)))))) as fv1; exrepnd.

    apply (al_bterm_aux [v]); simpl; autorewrite with slow; auto.

    {
      apply disjoint_singleton_l; auto.
    }

    fold_terms.
    boolvar; autorewrite with slow; simpl.

  }

Qed.

Lemma lsubstc_vars_mk_natk2nat_as_mkcv {o} :
  forall (t : @NTerm o) w s vs c,
    {w1 : wf_term t
     & {c1 : cover_vars_upto t s vs
     & alphaeqcv
         vs
         (lsubstc_vars (mk_natk2nat t) w s vs c)
         (mkcv_natk2nat
            vs
            (lsubstc_vars t w1 s vs c1)) }}.
Proof.
  introv.
  unfold mk_natk2nat in *.
  pose proof (lsubstc_vars_mk_fun_as_mkcv
                (mk_natk t) mk_tnat
                w s vs c) as h.
  exrepnd.

  dup w1 as w'.
  rw @wf_term_mk_natk in w'.
  exists w'.

  dup c1 as c'.
  rw @cover_vars_upto_natk in c'.
  exists c'.

  eapply alphaeqcv_trans;[exact h1|].
  unfold mkcv_natk2nat.
  autorewrite with slow.

  unfold alphaeqcv; simpl.
  apply alpha_eq_mk_fun; eauto 2 with slow.

  Print mk_natk_aux.
  Print mk_natk.
Qed.

Definition update_seq_cv {o} vs (s n m : @CVTerm o vs) (v : NVar) :=
  mkcv_lam
    vs
    v
    (mkcv_inteq
       (v :: vs)
       (mk_cv_app_r vs [v] (mkc_var v))
       (mk_cv_app_l [v] vs n)
       (mk_cv_app_l [v] vs m)
       (mkcv_apply
          (v :: vs)
          (mk_cv_app_l [v] vs s)
          (mk_cv_app_r vs [v] (mkc_var v)))).

(*
(*

   forall m : nat, squash (exists n : nat, P(m,n))

   implies

   squash (exists f : nat -> nat, forall m : nat, squash (P (m, f m)))

 *)
Lemma choice_sequence_induction {o} :
  forall lib (f m n v : NVar) c (P : @CTerm o),
    n <> m
    -> f <> m
    -> n <> f
    -> (forall a s,
          member lib a mkc_tnat
          -> member lib s (natk2nat a)
          -> type lib (mkc_apply2 P a s))
    -> inhabited_type lib (mkc_apply2 P mkc_zero c)
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            n
            (mkcv_forall
               [n]
               (mkcv_natk2nat [n] (mkc_var n))
               f
               (mkcv_fun
                  [f,n]
                  (mkcv_apply2 [f,n]
                               (mk_cv [f,n] P)
                               (mk_cv_app_l [f] [n] (mkc_var n))
                               (mk_cv_app_r [n] [f] (mkc_var f)))
                  (mkcv_squash
                     [f,n]
                     (mkcv_exists
                        [f,n]
                        (mkcv_tnat [f,n])
                        m
                        (mkcv_apply2 [m,f,n]
                               (mk_cv [m,f,n] P)
                               (mkcv_add [m,f,n] (mk_cv_app_l [m,f] [n] (mkc_var n)) (mkcv_one [m,f,n]))
                               (update_seq_cv
                                  [m,f,n]
                                  (mk_cv_app_l [m] [f,n] (mk_cv_app_r [n] [f] (mkc_var f)))
                                  (mk_cv_app_l [m,f] [n] (mkc_var n))
                                  (mk_cv_app_r [f,n] [m] (mkc_var m))
                                  v)))))))
    -> inhabited_type
         lib
         (mkc_exists
            nat2nat
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               n
               (mkcv_apply2 [n,f]
                            (mk_cv [n,f] P)
                            (mk_cv_app_r [f] [n] (mkc_var n))
                            (mk_cv_app_l [n] [f] (mkc_var f))))).
Proof.
  introv d1 d2 d3 wf base ind.

  unfold mkc_forall in ind.
  apply inhabited_function in ind.
  repnd.
  clear ind0 ind1.
  exrepnd.

  assert {f : nat -> nat
          & forall n, inhabited_type lib (mkc_apply2 P (mkc_nseq f) (mkc_nat n))}.
  {
  }

  assert (forall k : nat,
             member
               lib
               (mkc_apply f0 (mkc_nat k))
               (mkc_forall
                  (natk2nat (mkc_nat k))
                  f
                  (mkcv_fun
                     [f]
                     (mkcv_apply2
                        [f]
                        (mk_cv [f] P)
                        (mkcv_nat [f] k)
                        (mkc_var f))
                     (mkcv_squash
                        [f]
                        (mkcv_exists
                           [f]
                           (mkcv_tnat [f])
                           m
                           (mkcv_apply2
                              [m, f]
                              (mk_cv [m, f] P)
                              (mkcv_add
                                 [m, f]
                                 (mkcv_nat [m,f] k)
                                 (mkcv_one [m, f]))
                              (update_seq_cv
                                 [m, f]
                                 (mk_cv_app_l [m] [f] (mkc_var f))
                                 (mkcv_nat [m,f] k)
                                 (mk_cv_app_r [f] [m] (mkc_var m))
                                 v))))))
         ) as q.
  { introv.
    pose proof (ind0 (mkc_nat k) (mkc_nat k)) as h; clear ind0.
    autodimp h hyp; eauto 3 with slow.
    rewrite substc_mkcv_function in h; tcsp.
    rw @member_eq in h.
    autorewrite with slow in h.

    apply equality_in_function in h; repnd.
    apply equality_in_function in h; repnd.
    SearchAbout equality mkc_function.
    Check if_member_function.
    eapply (if_member_function lib) in h.

    substc_mkcv_natk2nat

    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_tnat_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> {j : CTerm
                , member lib j mkc_tnat
                # inhabited_type lib (mkc_apply2 P k j)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

  (* First use FunctionalChoice_on to get an existential (a Coq function from terms to terms) *)

  pose proof (FunctionalChoice_on
                {k : CTerm & member lib k mkc_tnat}
                (@CTerm o)
                (fun k j => member lib j mkc_tnat # inhabited_type lib (mkc_apply2 P (projT1 k) j)))
    as fc.
  simphyps.
  autodimp fc hyp; tcsp;[].
  exrepnd.
  clear h.
  rename fc0 into fc.

  assert {c : nat -> nat
          & forall a : CTerm,
              member lib a mkc_tnat
              -> (member lib (mkc_eapply (mkc_nseq c) a) mkc_tnat
                  # inhabited_type lib (mkc_apply2 P a (mkc_eapply (mkc_nseq c) a)))} as fs.
  { exists (fun n =>
              match member_tnat_implies_computes
                      lib
                      (f1 (existT _ (mkc_nat n) (nat_in_nat lib n)))
                      (fst (fc (existT _ (mkc_nat n) (nat_in_nat lib n)))) with
                | existT k _ => k
              end).
    introv mem.
    dands.

    - apply member_tnat_iff in mem; exrepnd.
      allrw @computes_to_valc_iff_reduces_toc; repnd.
      eapply member_respects_reduces_toc;[apply reduces_toc_eapply_nseq;exact mem1|].

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as mt.
      exrepnd.

      apply (member_respects_reduces_toc _ _ (mkc_nat k0)).

      + unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; allsimpl; dcwf h; simpl.
        boolvar; try omega.
        rw @Znat.Nat2Z.id.
        rewrite <- Heqmt; auto.

      + apply member_tnat_iff.
        exists k0.
        apply computes_to_valc_refl; eauto 3 with slow.

    - apply member_tnat_iff in mem; exrepnd.
      pose proof (nat_in_nat lib k) as mk.

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as q.
      exrepnd.
      remember (fc exI(mkc_nat k, nat_in_nat lib k)) as fck.
      exrepnd.
      allsimpl.

      allunfold @inhabited_type; exrepnd.
      exists t.
      allsimpl.

      eapply member_respects_cequivc_type;[|exact fck1].
      apply implies_cequivc_apply2; auto.

      + apply cequivc_sym.
        apply computes_to_valc_implies_cequivc; auto.

      + apply cequivc_sym.
        allrw @computes_to_valc_iff_reduces_toc; repnd.
        eapply cequivc_trans;
          [apply reduces_toc_implies_cequivc;
            apply reduces_toc_eapply_nseq;exact mem1
          |].

        eapply cequivc_trans;
          [|apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;
             exact q0].
        apply reduces_toc_implies_cequivc.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl.
        boolvar; try omega.
        allrw @Znat.Nat2Z.id.
        allsimpl.
        rw <- Heqfck; simpl.
        rw <- Heqq; auto.
  }
  clear f1 fc.
  exrepnd.

  (* then "convert" the Coq function into a Nuprl function *)

  apply inhabited_product.

  dands.

  { apply type_nat2nat. }

  { introv eqf.
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    apply tequality_function.
    dands.
    { apply tnat_type. }

    introv eqn.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_squash.
    apply type_respects_cequivc_left.

    { apply implies_cequivc_apply2; auto.
      { apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
    }

    { apply impp; eauto 3 with slow.
      { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_sym in eqf; apply equality_refl in eqf; auto. }
    }
  }

  { exists (@mkc_nseq o c).
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkc_var_substc.

    dands.

    { apply member_nseq_nat2nat. }

    { apply inhabited_function; dands; eauto 3 with slow.

      - introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        apply tequality_mkc_squash.
        apply type_respects_cequivc_left.

        { apply implies_cequivc_apply2; auto.
          { apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
          { apply implies_cequivc_apply; auto.
            apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
        }

        { apply impp; eauto 3 with slow.
          { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
          { pose proof (member_nseq_nat2nat lib c) as eqf.
            eapply equality_nat2nat_apply in eqf;[|exact eqn].
            apply equality_sym in eqf; apply equality_refl in eqf; auto. }
        }

      - exists (@mkc_lam o nvarx (mkcv_axiom nvarx)).
        introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        applydup @equality_int_nat_implies_cequivc in eqn.
        apply equality_refl in eqn.
        eapply equality_respects_cequivc_right;
          [apply implies_cequivc_apply;
            [apply cequivc_refl
            |exact eqn0]
          |].
        rw @member_eq.

        eapply member_respects_cequivc;
          [apply cequivc_sym;
            apply cequivc_beta
          |].
        rw @substc_mkcv_axiom.

        apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow).

        pose proof (fs0 a eqn) as q; repnd.

        eapply inhabited_type_cequivc;[|exact q].
        apply implies_cequivc_apply2; auto.
        apply cequivc_sym.
        apply reduces_toc_implies_cequivc.
        destruct_cterms.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl; auto.
    }
  }
Qed.
 *)

Print mk_update_seq.

Definition rule_choice_sequence_ind {o}
           (P I s B : @NTerm o)
           (f m n v : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax
                           (mk_squash
                              (mk_exists
                                 (mk_nat2nat)
                                 f
                                 (mk_forall
                                    mk_tnat
                                    n
                                    (mk_apply2 P (mk_var n) (mk_var f)))))))
      [
        mk_baresequent H (mk_concl (mk_apply2 P mk_zero s) B),
        mk_baresequent H (mk_concl
                            (mk_forall
                               mk_tnat
                               n
                               (mk_forall
                                  (mk_natk2nat (mk_var n))
                                  f
                                  (mk_fun
                                     (mk_apply2 P (mk_var n) (mk_var f))
                                     (mk_squash
                                        (mk_exists
                                           mk_tnat
                                           m
                                           (mk_apply2
                                              P
                                              (mk_add (mk_var n) mk_zero)
                                              (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v)))))))
                            I),
        mk_baresequent H (mk_conclax
                            (mk_member
                               P
                               (mk_function
                                  mk_tnat
                                  n
                                  (mk_fun
                                     (mk_natk2nat (mk_var n))
                                     (mk_uni i)))))
      ]
      [].

Lemma rule_choice_sequence_ind_true {o} :
  forall lib
         (P I s B : NTerm)
         (f m n v : NVar)
         (H : @barehypotheses o)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true lib (rule_choice_sequence_ind P I s B f m n v H i).
Proof.
  unfold rule_choice_sequence_ind, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp  into hyp1; destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2; destruct hyp2 as [wc2 hyp2].
  rename Hyp1 into hyp3; destruct hyp3 as [wc3 hyp3].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as base; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as ind; exrepnd; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as wf; exrepnd; clear hyp3.

  allunfold @mk_forall.
  allunfold @mk_exists.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in wf0; auto;[].

  apply inhabited_type_if_equality in ind1.
  apply inhabited_type_if_equality in base1.
  clear dependent I.
  clear dependent B.

  autorewrite with slow in *.

  dands.

  - (* tequality *)
    apply tequality_mkc_squash.
    apply tequality_product; dands.

    + unfold mk_nat2nat.
      lsubst_tac.
      autorewrite with slow.
      fold (@nat2nat o).
      rewrite fold_type.
      eauto 3 with slow.

    + introv ef.
      eapply alphaeqc_preserving_equality in ef;[|apply lsubstc_mk_nat2nat].
      clear base0 base1 ind0 ind1 wf1.
      repeat lsubstc_vars_as_mkcv.
      repeat (rewrite substc_mkcv_function; auto;[]).
      autorewrite with slow in *.

      apply tequality_function.
      dands; eauto 3 with slow.
      introv ea.
      repeat (rewrite substcv_as_substc2).
      repeat (rewrite substc2_apply2).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r;auto;[]).
      repeat (rewrite substc2_mk_cv_app_l;auto;[]).
      autorewrite with slow.

      apply equality_in_function in wf0; repnd.
      clear wf1 wf2.
      pose proof (wf0 a0 a'0 ea) as h; clear wf0.

      pose proof (lsubstc_vars_mk_fun_as_mkcv
                    (mk_natk2nat (@mk_var o n))
                    (mk_uni i)
                    w2 (csub_filter s1 [n]) [n] c2) as q.
      exrepnd; proof_irr.

      eapply alphaeqc_preserving_equality in h;
        [|apply substc_alphaeqcv;exact q1];clear q1.

      eapply alphaeqc_preserving_equality in h;[|apply substc_mkcv_fun].
      repeat lsubstc_vars_as_mkcv.
      autorewrite with slow in h.
      lsubst_tac.

      apply equality_in_fun in h; repnd.
      clear h0 h1.
      pose proof (h a a') as q; clear h.
      allrw <- @mkc_apply2_eq.
      autodimp q hyp;[|eapply equality_in_uni; eauto];[].


      SearchAbout tequality equality mkc_uni.
      unfold mk_natk2nat.
      SearchAbout lsubstc_vars mk_fun.
      SearchAbout equality mkc_fun.

      SearchAbout lsubstc_vars mk_natk2nat.

      SearchAbout alphaeqcv.
      SearchAbout lsubstc_vars mk_fun.
      unfold mk_fun in h.
      rewrite substc_mkcv_function in h; auto.

      SearchAbout equality mkc_function.

      pose proof (axiom_of_choice_00 lib f n m (lsubstc P wt s1 ct1)) as ac.
  repeat (autodimp ac hyp).

  - (* from qq1 *)
    introv m1 m2.
    apply equality_in_fun in qq1; repnd.
    pose proof (qq1 a a) as h.
    autodimp h hyp.
    lsubst_tac.
    allrw @lsubstc_mkc_tnat.
    apply equality_in_fun in h; repnd.
    pose proof (h b b) as q.
    autodimp q hyp.
    apply equality_in_uni in q; auto.
    allrw <- @mkc_apply2_eq; auto.

  - (* from hh1 *)
    apply equality_refl in hh1.
    exists (lsubstc e wfce1 s1 pt0).

    repeat lsubstc_vars_as_mkcv.
    auto.

  - repeat lsubstc_vars_as_mkcv.

    dands;
      [|apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow);
        allunfold @mkc_exists; allunfold @mkcv_forall;
        eapply inhabited_type_respects_alphaeqc;[|exact ac];
        apply alphaeqc_mkc_product1;
        apply alphaeqc_sym; apply lsubstc_mk_nat2nat].

    apply tequality_mkc_squash.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    apply tequality_product; dands.
    { apply type_nat2nat. }

    introv eqf.
    repeat (rw @substc_mkcv_function; auto;[]).
    allrw @mkcv_tnat_substc.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_apply.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto;[]).
    repeat (rw @substc2_mk_cv_app_l; auto;[]).
    allrw @mkc_var_substc.

    apply tequality_function; dands.
    { apply tnat_type. }

    introv eqn.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @mkcv_apply_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_squash.
    apply equality_in_fun in qq0; repnd.
    applydup qq0 in eqn.
    lsubst_tac.
    apply equality_in_fun in eqn0; repnd.
    pose proof (eqn0 (mkc_apply a a0) (mkc_apply a' a'0)) as q.
    allrw @lsubstc_mkc_tnat.
    autodimp q hyp.
    { apply equality_nat2nat_apply; auto. }
    allrw <- @mkc_apply2_eq.
    apply equality_in_uni in q; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
