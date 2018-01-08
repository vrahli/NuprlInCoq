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


Require Export substc_more.
Require Export sequents_tacs.
Require Export per_props_product.
Require Export per_props_function.
Require Export per_props_squash.
Require Export per_props_equality.
Require Export per_props_nat2.
Require Export lsubstc_vars.


(*

   forall m : nat, squash (exists n : nat, P(m,n))

   implies

   squash (exists f : nat -> nat, forall m : nat, squash (P (m, f m)))

 *)
Lemma axiom_of_choice_00 {o} :
  forall lib f m n (P : @CTerm o),
    n <> m
    -> f <> m
    -> (forall a b,
          member lib a mkc_tnat
          -> member lib b mkc_tnat
          -> type lib (mkc_apply2 P a b))
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            m
            (mkcv_squash
               [m]
               (mkcv_exists
                  [m]
                  (mkcv_tnat [m])
                  n
                  (mkcv_apply2 [n,m]
                               (mk_cv [n,m] P)
                               (mk_cv_app_l [n] [m] (mkc_var m))
                               (mk_cv_app_r [m] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_exists
            nat2nat
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               m
               (mkcv_squash
                  [m,f]
                  (mkcv_apply2 [m,f]
                               (mk_cv [m,f] P)
                               (mk_cv_app_r [f] [m] (mkc_var m))
                               (mkcv_apply [m,f]
                                           (mk_cv_app_l [m] [f] (mkc_var f))
                                           (mk_cv_app_r [f] [m] (mkc_var m))))))).
Proof.
  introv d1 d2 impp inh.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> inhabited_type
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] k)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 k k) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
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
                | existT _ k _ => k
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


Definition rule_AC00 {o}
           (P e : @NTerm o)
           (f m n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_squash (mk_exists (mk_nat2nat) f (mk_forall mk_tnat n (mk_squash (mk_apply2 P (mk_var n) (mk_apply (mk_var f) (mk_var n)))))))))
      [ mk_baresequent H (mk_concl (mk_forall mk_tnat n (mk_squash (mk_exists mk_tnat m (mk_apply2 P (mk_var n) (mk_var m))))) e),
        mk_baresequent H (mk_conclax (mk_member P (mk_fun mk_tnat (mk_fun mk_tnat (mk_uni i))))) ]
      [].

Lemma rule_AC00_true {p} :
  forall lib
         (P e : NTerm)
         (f m n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true lib (rule_AC00 P e f m n H i).
Proof.
  unfold rule_AC00, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hh; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as qq; exrepnd; clear hyp2.

  allunfold @mk_forall.
  allunfold @mk_exists.
  allunfold @mk_nat2nat.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in qq0; auto;[].
  allrw @tequality_mkc_member_sp; repnd.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.

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

   forall f : nat -> nat, squash exists n : nat, P(f,n)

   implies

   squash exists F : (nat -> nat) -> nat, forall f : nat -> nat, P (f, F f)

 *)
Lemma axiom_of_choice_10 {o} :
  forall lib F f n (P : @CTerm o),
    n <> f
    -> inhabited_type
         lib
         (mkc_forall
            nat2nat
            f
            (mkcv_squash
               [f]
               (mkcv_exists
                  [f]
                  (mkcv_tnat [f])
                  n
                  (mkcv_apply2 [n,f]
                               (mk_cv [n,f] P)
                               (mk_cv_app_l [n] [f] (mkc_var f))
                               (mk_cv_app_r [f] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_squash
            (mkc_exists
               (mkc_fun nat2nat mkc_tnat)
               F
               (mkcv_forall
                  [F]
                  (mk_cv [F] nat2nat)
                  f
                  (mkcv_apply2 [f,F]
                               (mk_cv [f,F] P)
                               (mk_cv_app_r [F] [f] (mkc_var f))
                               (mkcv_apply [f,F]
                                           (mk_cv_app_l [f] [F] (mkc_var F))
                                           (mk_cv_app_r [F] [f] (mkc_var f))))))).
Proof.
  introv d1 inh.
  apply inhabited_squash.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall f : CTerm,
            member lib f nat2nat
            -> inhabited_type
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] f)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 f1 f1) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
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

  assert (forall f : CTerm,
            member lib f nat2nat
            -> {k : CTerm
                , member lib k mkc_tnat
                # inhabited_type lib (mkc_apply2 P f k)}) as h.
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

Abort.
