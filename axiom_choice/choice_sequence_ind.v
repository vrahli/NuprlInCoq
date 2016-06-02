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


Require Export csubst6.
Require Export substc_more.
Require Export per_props4.
Require Export per_props_squash.
Require Export seq_util2.


Lemma type_implies_tequality_refl {o} :
  forall lib (t : @CTerm o),
    type lib t -> tequality lib t t.
Proof.
  sp.
Qed.
Hint Resolve type_implies_tequality_refl : slow.

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

Hint Resolve is_kseq_0 : slow.
Hint Resolve member_nseq_nat2nat : slow.

Record inh_seq {o} lib (P : @CTerm o) n :=
  MkInhSeq
    {
      inh_seq_seq : CTerm;
      inh_seq_isk : is_kseq lib inh_seq_seq n;
      inh_seq_inh : inhabited_type lib (mkc_apply2 P (mkc_nat n) inh_seq_seq)
    }.

Record inh_seq2 {o} lib (P : @CTerm o) :=
  MkInhSeq2
    {
      inh_seq2_nat : nat;
      inh_seq2_inh : inh_seq lib P inh_seq2_nat
    }.

Record inh_seq3 {o} lib (P : @CTerm o) n :=
  MkInhSeq3
    {
      inh_seq3_nat : nat;
      inh_seq3_inh : inh_seq lib P n
    }.

Fixpoint inh_seq_alpha0 {o}
         (lib : library)
         (P : @CTerm o)
         (v : NVar)
         (b : inh_seq lib P 0)
         (ind :
            forall n s,
              is_kseq lib s n
              -> inhabited_type lib (mkc_apply2 P (mkc_nat n) s)
              -> {m : nat & inhabited_type lib (mkc_apply2 P (mkc_nat (S n)) (update_seq s n m v))})
         (n : nat) : inh_seq lib P n :=
  match n with
    | 0 => b
    | S m =>
      match inh_seq_alpha0 lib P v b ind m with
      | MkInhSeq s isk inh =>
        match ind m s isk inh with
        | existT k i =>
          MkInhSeq
            o
            lib
            P
            (S m)
            (update_seq s m k v)
            (is_kseq_update lib s m k v isk)
            i
        end
      end
  end.

Fixpoint inh_seq_alpha {o}
         (lib : library)
         (P : @CTerm o)
         (v : NVar)
         (base : inh_seq lib P 0)
         (f : inh_seq2 lib P -> nat)
         (ind :
            forall a : inh_seq2 lib P,
              inhabited_type
                lib
                (mkc_apply2
                   P
                   (mkc_nat (S (inh_seq2_nat lib P a)))
                   (update_seq
                      (inh_seq_seq lib P (inh_seq2_nat lib P a) (inh_seq2_inh lib P a))
                      (inh_seq2_nat lib P a)
                      (f a)
                      v)))
         (n : nat) : inh_seq3 lib P n :=
  match n with
  | 0 => MkInhSeq3 o lib P 0 0 base
  | S m =>
    match inh_seq_alpha lib P v base f ind m with
    | MkInhSeq3 _ (MkInhSeq s isk inh) =>
      let k := f (MkInhSeq2 o lib P m (MkInhSeq o lib P m s isk inh)) in
      let i := ind (MkInhSeq2 o lib P m (MkInhSeq o lib P m s isk inh)) in
      MkInhSeq3
        o lib P
        (S m)
        k
        (MkInhSeq
           o lib P
           (S m)
           (update_seq s m k v)
           (is_kseq_update lib s m k v isk)
           i)
    end
  end.

Lemma inh_seq_seq_inh_seq3_inh_MkInhSeq {o} :
  forall lib (P : @CTerm o) k z s isk inh,
    inh_seq_seq lib P k (inh_seq3_inh lib P k (MkInhSeq3 o lib P k z (MkInhSeq o lib P k s isk inh))) = s.
Proof. sp. Qed.

Lemma inh_seq_alpha_prop1 {o} :
  forall lib
         (P : @CTerm o)
         (v : NVar)
         (b : inh_seq lib P 0)
         (f : inh_seq2 lib P -> nat)
         (ind :
            forall a : inh_seq2 lib P,
              inhabited_type
                lib
                (mkc_apply2
                   P
                   (mkc_nat (S (inh_seq2_nat lib P a)))
                   (update_seq
                      (inh_seq_seq lib P (inh_seq2_nat lib P a) (inh_seq2_inh lib P a))
                      (inh_seq2_nat lib P a)
                      (f a)
                      v)))
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (inh_seq_seq lib P n (inh_seq3_inh lib P n (inh_seq_alpha lib P v b f ind n)))
      (inh_seq_seq lib P m (inh_seq3_inh lib P m (inh_seq_alpha lib P v b f ind m)))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; apply implies_equality_natk2nat; introv ltm0.

  - simpl.
    remember (inh_seq_alpha lib P v b f ind m) as am.
    destruct am.
    destruct inh_seq3_inh0; allsimpl.

    dup inh_seq_isk0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - allsimpl.
    remember (inh_seq_alpha lib P v b f ind (k + m)) as am.
    destruct am.
    destruct inh_seq3_inh0; simphyps.
    rewrite inh_seq_seq_inh_seq3_inh_MkInhSeq.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma choice_sequence_ind {o} :
  forall lib (P : @CTerm o) c v,
    (forall n s1 s2,
        eq_kseq lib s1 s2 n
        -> tequality lib (mkc_apply2 P (mkc_nat n) s1) (mkc_apply2 P (mkc_nat n) s2))
    -> inhabited_type lib (mkc_apply2 P mkc_zero c)
    -> (forall n s,
           is_kseq lib s n
           -> inhabited_type lib (mkc_apply2 P (mkc_nat n) s)
           -> exists m, inhabited_type lib (mkc_apply2 P (mkc_nat (S n)) (update_seq s n m v)))
    -> exists f,
        member lib f nat2nat
        # forall n, inhabited_type lib (mkc_apply2 P (mkc_nat n) f).
Proof.
  introv wf base ind.

  assert (inh_seq lib P 0) as base1.
  {
    exists c; dands; eauto 3 with slow.
    rewrite <- mkc_zero_eq; auto.
  }

  assert (forall i : inh_seq2 lib P,
             exists m,
               inhabited_type
                 lib
                 (mkc_apply2
                    P
                    (mkc_nat (S (inh_seq2_nat lib P i)))
                    (update_seq (inh_seq_seq lib P (inh_seq2_nat lib P i) (inh_seq2_inh lib P i)) (inh_seq2_nat lib P i) m v))) as ind1.
  {
    introv; exrepnd; simpl.
    destruct i; simpl.
    destruct inh_seq2_inh0.
    apply ind; simpl; auto.
  }

  clear ind.
  apply FunctionalChoice_on in ind1; exrepnd.

  remember (inh_seq_alpha lib P v base1 f ind0) as F.
  remember (fun n => inh_seq3_nat lib P (S n) (F (S n))) as G.

  exists (@mkc_nseq o G).
  dands; eauto 3 with slow.
  introv.

  assert (forall n, eq_kseq lib (mkc_nseq G) (inh_seq_seq lib P n (inh_seq3_inh lib P n (F n))) n) as e.
  {
    introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (inh_seq3_nat lib P (S m) (inh_seq_alpha lib P v base1 f ind0 (S m))).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (inh_seq_alpha_prop1 lib P v base1 f ind0 n0 (S m)) as q.
      autodimp q hyp; try omega.

      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (inh_seq_alpha lib P v base1 f ind0 m) as am.
      destruct am.
      destruct inh_seq3_inh0; simphyps.
      rewrite inh_seq_seq_inh_seq3_inh_MkInhSeq.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (e n) as eqn.
  clear e.

  apply wf in eqn.
  eapply inhabited_type_tequality;[apply tequality_sym;exact eqn|].
  clear eqn.
  subst F.
  remember (inh_seq_alpha lib P v base1 f ind0 n) as am.
  destruct am.
  destruct inh_seq3_inh0; allsimpl; auto.
Qed.

Lemma lsubstc_mk_one {o} :
  forall p sub c,
    lsubstc mk_one p sub c = @mkc_one o.
Proof.
  unfold lsubstc, mkc_one; sp.
  apply cterm_eq; sp.
Qed.
Hint Rewrite @lsubstc_mk_one : slow.

Ltac rev_assert T h :=
    match goal with
    | [ |- ?C ] =>
      assert (T -> C) as h;[introv h|apply h;clear h]
    end.

Definition rule_choice_sequence_ind {o}
           (P s B : @NTerm o)
           (f m n z v : NVar)
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
                                    (mk_squash (mk_apply2 P (mk_var n) (mk_var f))))))))
      [
        mk_baresequent H (mk_concl (mk_apply2 P mk_zero s) B),
        mk_baresequent (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                                   (mk_hyp f (mk_natk2nat (mk_var n))))
                             (mk_hyp z (mk_apply2 P (mk_var n) (mk_var f))))
                       (mk_conclax
                          (mk_squash
                             (mk_exists
                                mk_tnat
                                m
                                (mk_apply2
                                   P
                                   (mk_add (mk_var n) mk_one)
                                   (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v))))),
        mk_baresequent (snoc (snoc H (mk_hyp n mk_tnat))
                             (mk_hyp f (mk_natk2nat (mk_var n))))
                       (mk_conclax
                            (mk_member
                               (mk_apply2 P (mk_var n) (mk_var f))
                               (mk_uni i)))
      ]
      [].

Lemma rule_choice_sequence_ind_true {o} :
  forall lib
         (P s B : NTerm)
         (f m n z v : NVar)
         (H : @barehypotheses o)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : m <> f)
         (d4 : !LIn m (free_vars P)),
    rule_true lib (rule_choice_sequence_ind P s B f m n z v H i).
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
  assert (!LIn n (vars_hyps H)
          # !LIn f (vars_hyps H)
          # !LIn z (vars_hyps H)
          # !LIn n (free_vars P)
          # !LIn f (free_vars P)
          # !LIn z (free_vars P)) as vhyps.

  { clear hyp1 hyp2 hyp3.
    dwfseq.
    sp.
  }

  destruct vhyps as [ nnH vhyps ].
  destruct vhyps as [ nfH vhyps ].
  destruct vhyps as [ nzH vhyps ].
  destruct vhyps as [ nnP vhyps ].
  destruct vhyps as [ nfP nzP ].
  (* done with proving these simple facts *)

  vr_seq_true.
  unfold mk_exists.
  lsubst_tac.

  assert (wf_term P) as wP.
  {
    dup wfct2 as wP.
    apply wf_apply2_iff in wP; repnd; auto.
  }

  assert (cover_vars P s1) as cP1.
  {
    dup pC1 as cP1.
    rw @cover_vars_squash in cP1.
    rw @cover_vars_product in cP1; repnd.
    rw @cover_vars_upto_function in cP1; repnd.
    rw @cover_vars_upto_squash in cP1.
    rw @cover_vars_upto_apply2 in cP1; repnd.
    rw <- @csub_filter_app_r in cP3; allsimpl.
    apply cover_vars_upto_csub_filter_disjoint in cP3; auto.

    - apply eqvars_is_eqset; simpl.
      introv; simpl; split; intro h; repndors; subst; tcsp.

    - repeat (rw disjoint_cons_r); dands; auto.
  }

  assert (cover_vars P s2) as cP2.
  {
    dup pC2 as cP2.
    rw @cover_vars_squash in cP2.
    rw @cover_vars_product in cP2; repnd.
    rw @cover_vars_upto_function in cP2; repnd.
    rw @cover_vars_upto_squash in cP2.
    rw @cover_vars_upto_apply2 in cP2; repnd.
    rw <- @csub_filter_app_r in cP4; allsimpl.
    apply cover_vars_upto_csub_filter_disjoint in cP4; auto.

    - apply eqvars_is_eqset; simpl.
      introv; simpl; split; intro h; repndors; subst; tcsp.

    - repeat (rw disjoint_cons_r); dands; auto.
  }

  rev_assert (
    forall s1 s2 (cP1 : cover_vars P s1) (cP2 : cover_vars P s2),
      similarity lib s1 s2 H
      -> hyps_functionality lib s1 H
      -> (forall f1 f2 n1 n2,
             equality lib f1 f2 nat2nat
             -> equality lib n1 n2 mkc_tnat
             -> tequality
                  lib
                  (mkc_apply2 (lsubstc P wP s1 cP1) n1 f1)
                  (mkc_apply2 (lsubstc P wP s2 cP2) n2 f2))
           # {f : CTerm
             , member lib f nat2nat
             # forall n,
                 member lib n mkc_tnat
                 -> inhabited_type lib (mkc_apply2 (lsubstc P wP s1 cP1) n f)}
    ) h.

  {
    apply implies_tequality_equality_mkc_squash_and.
    rw @inhabited_product.
    rw @tequality_product.
    dands.

    - eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
      eauto 3 with slow.

    - introv ef.
      eapply alphaeqc_preserving_equality in ef;[|apply lsubstc_mk_nat2nat].
      unfold mk_forall.
      repeat lsubstc_vars_as_mkcv.
      repeat (rewrite substc_mkcv_function; auto;[]).
      autorewrite with slow.

      apply tequality_function; dands; eauto 3 with slow;[].
      introv ea.
      repeat (rewrite substcv_as_substc2).
      autorewrite with slow in *.
      repeat (rewrite substc2_mk_cv_app_r;auto;[]).
      autorewrite with slow.
      apply tequality_mkc_squash.

      pose proof (h s1 s2 cP1 cP2 sim eqh) as q; repnd.
      apply q0; auto.

    - eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
      eauto 3 with slow.

    - introv ef.
      eapply alphaeqc_preserving_equality in ef;[|apply lsubstc_mk_nat2nat].
      unfold mk_forall.
      repeat lsubstc_vars_as_mkcv.
      repeat (rewrite substc_mkcv_function; auto;[]).
      autorewrite with slow.

      apply tequality_function; dands; eauto 3 with slow;[].
      introv ea.
      repeat (rewrite substcv_as_substc2).
      autorewrite with slow in *.
      repeat (rewrite substc2_mk_cv_app_r;auto;[]).
      autorewrite with slow.
      apply tequality_mkc_squash.

      apply similarity_refl in sim.
      pose proof (h s1 s1 cP1 cP1 sim eqh) as q; repnd.
      apply q0; auto.

    - pose proof (h s1 s2 cP1 cP2 sim eqh) as q; exrepnd.
      exists f0.
      dands.

      + eapply respects_alphaeqc_member;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
        auto.

      + unfold mk_forall.
        repeat lsubstc_vars_as_mkcv.
        repeat (rewrite substc_mkcv_function; auto;[]).
        autorewrite with slow.
        apply inhabited_function; dands; eauto 3 with slow;[|].

        * introv ea.
          repeat (rewrite substcv_as_substc2).
          autorewrite with slow in *.
          repeat (rewrite substc2_mk_cv_app_r;auto;[]).
          autorewrite with slow.
          apply tequality_mkc_squash.

          apply similarity_refl in sim.
          pose proof (h s1 s1 cP1 cP1 sim eqh) as q; repnd.
          apply q3; auto.

        * exists (@lam_axiom o).
          introv ea.

          eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].
          eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].

          repeat (rewrite substcv_as_substc2).
          autorewrite with slow in *.
          repeat (rewrite substc2_mk_cv_app_r;auto;[]).
          autorewrite with slow.
          apply equality_in_mkc_squash.
          dands; spcast; try (apply computes_to_valc_refl; eauto 3 with slow).

          apply q1.
          apply equality_refl in ea; auto.
  }

  clear dependent s1.
  clear dependent s2.
  introv sim hf.

  assert (!LIn n (dom_csub s1)) as nin1.
  {
    apply similarity_dom in sim; repnd; allrw; auto.
  }

  assert (!LIn n (dom_csub s2)) as nin2.
  {
    apply similarity_dom in sim; repnd; allrw; auto.
  }

  assert (forall s1 s2 n1 n2 f1 f2 (c1 : cover_vars P s1) (c2 : cover_vars P s2),
             similarity lib s1 s2 H
             -> hyps_functionality lib s1 H
             -> equality lib n1 n2 mkc_tnat
             -> equality lib f1 f2 (natk2nat n1)
             -> tequality
                  lib
                  (mkc_apply2 (lsubstc P wP s1 c1) n1 f1)
                  (mkc_apply2 (lsubstc P wP s2 c2) n2 f2)) as wf.
  {
    clear dependent s1.
    clear dependent s2.
    introv sim hf en ef.

    assert (!LIn n (dom_csub s1)) as nin1.
    {
      apply similarity_dom in sim; repnd; allrw; auto.
    }

    assert (!LIn n (dom_csub s2)) as nin2.
    {
      apply similarity_dom in sim; repnd; allrw; auto.
    }

    vr_seq_true in hyp3.
    pose proof (hyp3
                  (snoc (snoc s1 (n,n1)) (f,f1))
                  (snoc (snoc s2 (n,n2)) (f,f2)))
      as wf; exrepnd; clear hyp3.

    repeat (autodimp wf hyp).

    {
      apply hyps_functionality_snoc2; simpl; auto.

      - introv equ sim'.
        lsubst_tac.
        apply similarity_snoc in sim'; exrepnd; subst; allsimpl; inj.

        assert (!LIn n (dom_csub s1a)) as ni2.
        {
          apply similarity_dom in sim'3; repnd; allrw; auto.
        }

        assert (!LIn n (dom_csub s2a)) as ni3.
        {
          apply similarity_dom in sim'3; repnd; allrw; auto.
        }

        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].

        apply tequality_natk2nat.
        autorewrite with slow in *.
        apply equality_in_tnat in sim'1.
        unfold equality_of_nat in sim'1; exrepnd; spcast.
        exists (Z.of_nat k) (Z.of_nat k); dands; spcast; auto.
        introv h1.
        destruct (Z_lt_le_dec k0 (Z.of_nat k)); tcsp.

      - apply hyps_functionality_snoc2; simpl; auto.
        introv equ sim'.
        autorewrite with slow.
        eauto 3 with slow.
    }

    {
      assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n, n1))) as cov1.
      {
        apply cover_vars_mk_natk2nat.
        apply cover_vars_var_iff.
        rw @dom_csub_snoc; simpl.
        apply in_snoc; sp.
      }

      repeat (sim_snoc2; dands; auto); autorewrite with slow; auto; eauto 2 with slow.

      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto];[].
      auto.
    }

    exrepnd.
    lsubst_tac.

    apply tequality_in_uni_implies_tequality in wf0; auto;[].
    apply member_if_inhabited in wf1.
    apply member_in_uni in wf1; auto.
  }

  dands.

  {

    (*
       I don't see any way of proving that without assuming that P is well-formed because
       the induction hypothesis gives us the well-formedness of P only for f basically
     *)

    (* tequality *)

    introv ef en.
    apply wf; auto.
    apply equality_nat2nat_to_natk2nat; auto.
    eapply equality_refl; eauto.
  }

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2) as base; exrepnd; clear hyp1.
  repeat (autodimp base hyp).
  exrepnd.
  lsubst_tac.
  clear base0.
  apply inhabited_type_if_equality in base1.

  pose proof (choice_sequence_ind
                lib
                (lsubstc P wP s1 cP1)
                (lsubstc s w5 s1 c3)
                v) as h.

  repeat (autodimp h hyp).

  {
    introv eqk.
    unfold eq_kseq in eqk.

    apply wf; eauto 3 with slow.
    apply similarity_refl in sim; auto.
  }

  {
    introv isk inh.
    unfold inhabited_type in inh; exrepnd.

    vr_seq_true in hyp2.
    pose proof (hyp2
                  (snoc (snoc (snoc s1 (n,mkc_nat n0)) (f,s0)) (z,t))
                  (snoc (snoc (snoc s1 (n,mkc_nat n0)) (f,s0)) (z,t)))
      as ind; exrepnd; clear hyp2.

    repeat (autodimp ind hyp).

    {
      apply hyps_functionality_snoc2; simpl; auto.

      - introv equ sim'.
        lsubst_tac.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; inj.
        apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; subst; inj.
        lsubst_tac.
        autorewrite with slow in *.

        eapply alphaeqc_preserving_equality in sim'1;
          [|apply lsubstc_mk_natk2nat_sp2;auto];[].

        apply wf; auto.

      - apply hyps_functionality_snoc2; simpl; auto.

        + introv equ sim'.
          apply similarity_snoc in sim'; simpl in sim'; exrepnd; subst; inj.

          assert (!LIn n (dom_csub s1a)) as ni2.
          {
            apply similarity_dom in sim'3; repnd; allrw; auto.
          }

          assert (!LIn n (dom_csub s2a)) as ni3.
          {
            apply similarity_dom in sim'3; repnd; allrw; auto.
          }

          eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].
          eapply tequality_respects_alphaeqc_right;
            [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].

          apply tequality_natk2nat.
          autorewrite with slow in *.
          apply equality_in_tnat in sim'1.
          unfold equality_of_nat in sim'1; exrepnd; spcast.
          exists (Z.of_nat k) (Z.of_nat k); dands; spcast; auto.
          introv h1.
          destruct (Z_lt_le_dec k0 (Z.of_nat k)); tcsp.

        + apply hyps_functionality_snoc2; simpl; auto;[].
          introv equ' sim'.
          autorewrite with slow; eauto 3 with slow.
    }

    {
      assert (wf_term (mk_apply2 P (mk_var n) (mk_var f))) as wf1.
      {
        apply wf_apply2; auto.
      }

      assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n, mkc_nat n0))) as cov1.
      {
        apply cover_vars_mk_natk2nat.
        apply cover_vars_var_iff.
        rw @dom_csub_snoc; simpl.
        apply in_snoc; sp.
      }

      assert (cover_vars
                (mk_apply2 P (mk_var n) (mk_var f))
                (snoc (snoc s1 (n, mkc_nat n0)) (f, s0))) as cov2.
      {
        apply cover_vars_apply2; dands; eauto 3 with slow.
        - repeat (apply cover_vars_snoc_weak); auto.
        - apply cover_vars_var.
          allrw @dom_csub_snoc; simpl.
          repeat (rw in_snoc); sp.
        - apply cover_vars_var.
          allrw @dom_csub_snoc; simpl.
          repeat (rw in_snoc); sp.
      }

      apply similarity_refl in sim.

      repeat (sim_snoc2; dands; auto); autorewrite with slow; auto; eauto 2 with slow.

      {
        eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto];[].
        auto.
      }

      {
        lsubst_tac.
        rw @member_eq.
        auto.
      }
    }

    exrepnd.
    unfold mk_exists in ind1.
    clear ind0.
    lsubst_tac.
    apply equality_in_mkc_squash in ind1; repnd.
    clear ind0 ind2.
    apply inhabited_product in ind1; repnd.
    clear ind0 ind2.
    exrepnd.
    autorewrite with slow in *.
    apply member_tnat_implies_computes in ind1; exrepnd.

    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow in ind0.
    lsubst_tac.
    autorewrite with slow in ind0.
    exists k.

Lemma mkc_one_as_mkc_nat {o} : @mkc_one o = mkc_nat 1.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

    eapply inhabited_type_cequivc in ind0;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |rewrite mkc_one_as_mkc_nat;
           repeat (rewrite mkc_nat_eq);
           apply cequivc_mkc_add_integer
         |apply cequivc_refl]
      ].
    rewrite <- Znat.Nat2Z.inj_add in ind0.
    rewrite <- mkc_nat_eq in ind0.
    rewrite plus_comm in ind0.

    SearchAbout mk_update_seq.

  }

  {

  }

XXXXXXXXXXXXX

  - apply equality_in_mkc_squash; dands; spcast;
    try (complete (apply computes_to_valc_refl; eauto 3 with slow)).

    repeat lsubstc_vars_as_mkcv.

    eapply inhabited_type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply alphaeqc_mkc_product1;
        apply lsubstc_mk_nat2nat|].

    apply inhabited_product; autorewrite with slow.
    dands; eauto 2 with slow.

    + introv ef.
      repeat (rewrite substc_mkcv_function; auto;[]).
      autorewrite with slow in *.

      apply tequality_function.
      dands; eauto 3 with slow.
      introv ea.
      repeat (rewrite substcv_as_substc2).
      autorewrite with slow in *.
      repeat (rewrite substc2_mk_cv_app_r;auto;[]).
      autorewrite with slow.

      vr_seq_true in hyp3.
      pose proof (hyp3
                    (snoc (snoc s1 (n,a0)) (f,a))
                    (snoc (snoc s1 (n,a'0)) (f,a')))
        as wf; exrepnd; clear hyp3.

      repeat (autodimp wf hyp).

      {
        apply hyps_functionality_snoc2; simpl; auto.

        - introv equ sim'.
          lsubst_tac.
          apply similarity_snoc in sim'; exrepnd; subst; allsimpl; inj.

          assert (!LIn n (dom_csub s1a)) as ni2.
          {
            apply similarity_dom in sim'3; repnd; allrw; auto.
          }

          assert (!LIn n (dom_csub s2a)) as ni3.
          {
            apply similarity_dom in sim'3; repnd; allrw; auto.
          }

          eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].
          eapply tequality_respects_alphaeqc_right;
            [apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto|];[].

          apply tequality_natk2nat.
          autorewrite with slow in *.
          apply equality_in_tnat in sim'1.
          unfold equality_of_nat in sim'1; exrepnd; spcast.
          exists (Z.of_nat k) (Z.of_nat k); dands; spcast; auto.
          introv h1.
          destruct (Z_lt_le_dec k0 (Z.of_nat k)); tcsp.

        - apply hyps_functionality_snoc2; simpl; auto.
          introv equ sim'.
          autorewrite with slow.
          eauto 3 with slow.
      }

      {
        assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n, a0))) as cov1.
        {
          apply cover_vars_mk_natk2nat.
          apply cover_vars_var_iff.
          rw @dom_csub_snoc; simpl.
          apply in_snoc; sp.
        }

        repeat (sim_snoc2; dands; auto); autorewrite with slow; auto.

        {
          eapply similarity_refl; eauto.
        }

        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym;apply lsubstc_mk_natk2nat_sp2;auto];[].
        apply equality_nat2nat_to_natk2nat; auto.
        eapply equality_refl; eauto.
      }

      exrepnd.
      lsubst_tac.

      apply tequality_in_uni_implies_tequality in wf0; auto;[].
      apply member_if_inhabited in wf1.
      apply member_in_uni in wf1; auto.

    + assert (forall n (s : CTerm),
                 member lib (mkc_nat n) mkc_tnat
                 -> member lib s (natk2nat (mkc_nat n))
                 -> inhabited_type lib (mkc_apply2 (lsubstc P w1 s1 c1) (mkc_nat n) s)
                 -> exists m, inhabited_type
                                lib
                                (mkc_apply2
                                   (lsubstc P w1 s1 c1)
                                   (mkc_add (mkc_nat n) mkc_one)
                                   (update_seq s n m v))).
      {
        introv mn ms inh.


        pose proof (ind0 (mkc_nat n0) (mkc_nat n0)) as h; clear ind0.
        autodimp h hyp.
        rewrite substc_mkcv_function in h; auto;[].
        apply equality_in_function in h.
        repnd.
        clear h0 h1.
        pose proof (h s0 s0) as q; clear h.

        autodimp q hyp.
        {
          pose proof (lsubstc_vars_mk_natk2nat_as_mkcv
                        (mk_var n) w12 (csub_filter s1 [n]) [n] c18) as h.
          exrepnd; proof_irr.

          eapply alphaeqc_preserving_equality;
            [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply h1].

          eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym;apply substc_mkcv_natk2nat].
          autorewrite with slow; auto.
        }

        pose proof (lsubstc_vars_mk_fun_as_mkcv
                      (mk_apply2 P (mk_var n) (mk_var f))
                      (mk_squash
                         (mk_product
                            mk_tnat m
                            (mk_apply2
                               P (mk_add (mk_var n) mk_one)
                               (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v))))
                      w11
                      (csub_filter (csub_filter s1 [n]) [f])
                      [f, n]
                      c19) as h; exrepnd.

        rewrite substcv_as_substc2 in q.

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_alphaeqcv;
             apply implies_alphaeqc_substc2;
             apply h1].
        clear h1.

        repeat lsubstc_vars_as_mkcv.
        autorewrite with slow in q.

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_alphaeqcv;
             apply substc2_fun].
        autorewrite with slow in q.
        repeat (rewrite substc2_mk_cv_app_r in q; auto;[]).

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_mkcv_fun].
        autorewrite with slow in q.

        apply equality_in_fun in q; repnd.
        clear q0 q1.

        unfold inhabited_type in inh; exrepnd.

        pose proof (q t0 t0) as h; clear q.
        autodimp h hyp.
        apply equality_in_mkc_squash in h; repnd.
        clear h0 h1.

        eapply inhabited_type_respects_alphaeqc in h;
          [|apply substc_alphaeqcv;
             apply substc2_product;auto].
        rewrite mkcv_product_substc in h; auto;[].

        repeat lsubstc_vars_as_mkcv.
        autorewrite with slow in h.

        apply inhabited_product in h; repnd.
        clear h0 h1; exrepnd.
        apply member_tnat_implies_computes in h1; exrepnd.
        exists k.
        autorewrite with slow in h0.


        pose proof (lsubstc_vars_mk_add_as_mkcv
                      (mk_var n) mk_one
                      w16
                      (csub_filter (csub_filter (csub_filter s1 [n]) [f]) [m])
                      [m, f, n]
                      c35) as q.
        exrepnd; proof_irr.
        rewrite q1 in h0; clear q1.
        autorewrite with slow in h0.

        rewrite lsubstc_vars_mk_var_as_mkcv3 in h0; auto;
        [|repeat (rw @dom_csub_csub_filter);
           repeat (rw in_remove_nvars); simpl; tcsp].
        autorewrite with slow in h0.

      }


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
                                              (mk_add (mk_var n) mk_one)
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
         (d3 : m <> f)
         (d4 : !LIn f (free_vars P))
         (d5 : !LIn m (free_vars P))
         (d6 : !LIn n (free_vars P)),
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

      pose proof (lsubstc_vars_mk_natk2nat_as_mkcv
                    (mk_var n) w8 (csub_filter s1 [n]) [n] c29) as h.
      exrepnd; proof_irr.

      eapply alphaeqc_preserving_equality;
        [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply h1].

      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply substc_mkcv_natk2nat].
      autorewrite with slow; auto.

      apply equality_nat2nat_to_natk2nat; auto.
      eapply equality_refl; eauto.

  - apply equality_in_mkc_squash; dands; spcast;
    try (complete (apply computes_to_valc_refl; eauto 3 with slow)).

    repeat lsubstc_vars_as_mkcv.

    eapply inhabited_type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply alphaeqc_mkc_product1;
        apply lsubstc_mk_nat2nat|].

    apply inhabited_product; autorewrite with slow.
    dands; eauto 2 with slow.

    + introv ef.
      clear base0 base1 ind0 ind1 wf0.
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

      apply equality_in_function in wf1; repnd.
      clear wf0 wf2.
      pose proof (wf1 a0 a'0 ea) as h; clear wf1.

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

      pose proof (lsubstc_vars_mk_natk2nat_as_mkcv
                    (mk_var n) w12 (csub_filter s1 [n]) [n] c18) as h.
      exrepnd; proof_irr.

      eapply alphaeqc_preserving_equality;
        [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply h1].

      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply substc_mkcv_natk2nat].
      autorewrite with slow; auto.

      apply equality_nat2nat_to_natk2nat; auto.
      eapply equality_refl; eauto.

    + clear ind0 base0.
      unfold inhabited_type in ind1; exrepnd.
      apply equality_in_function in ind0; repnd.
      clear ind1 ind2.

      proof_irr.
      assert (forall n (s : CTerm),
                 member lib (mkc_nat n) mkc_tnat
                 -> member lib s (natk2nat (mkc_nat n))
                 -> inhabited_type lib (mkc_apply2 (lsubstc P wt s1 ct2) (mkc_nat n) s)
                 -> exists m, inhabited_type
                                lib
                                (mkc_apply2
                                   (lsubstc P wt s1 ct2)
                                   (mkc_add (mkc_nat n) mkc_one)
                                   (update_seq s n m v))).
      {
        introv mn ms inh.
        pose proof (ind0 (mkc_nat n0) (mkc_nat n0)) as h; clear ind0.
        autodimp h hyp.
        rewrite substc_mkcv_function in h; auto;[].
        apply equality_in_function in h.
        repnd.
        clear h0 h1.
        pose proof (h s0 s0) as q; clear h.

        autodimp q hyp.
        {
          pose proof (lsubstc_vars_mk_natk2nat_as_mkcv
                        (mk_var n) w12 (csub_filter s1 [n]) [n] c18) as h.
          exrepnd; proof_irr.

          eapply alphaeqc_preserving_equality;
            [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply h1].

          eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym;apply substc_mkcv_natk2nat].
          autorewrite with slow; auto.
        }

        pose proof (lsubstc_vars_mk_fun_as_mkcv
                      (mk_apply2 P (mk_var n) (mk_var f))
                      (mk_squash
                         (mk_product
                            mk_tnat m
                            (mk_apply2
                               P (mk_add (mk_var n) mk_one)
                               (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v))))
                      w11
                      (csub_filter (csub_filter s1 [n]) [f])
                      [f, n]
                      c19) as h; exrepnd.

        rewrite substcv_as_substc2 in q.

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_alphaeqcv;
             apply implies_alphaeqc_substc2;
             apply h1].
        clear h1.

        repeat lsubstc_vars_as_mkcv.
        autorewrite with slow in q.

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_alphaeqcv;
             apply substc2_fun].
        autorewrite with slow in q.
        repeat (rewrite substc2_mk_cv_app_r in q; auto;[]).

        eapply alphaeqc_preserving_equality in q;
          [|apply substc_mkcv_fun].
        autorewrite with slow in q.

        apply equality_in_fun in q; repnd.
        clear q0 q1.

        unfold inhabited_type in inh; exrepnd.

        pose proof (q t0 t0) as h; clear q.
        autodimp h hyp.
        apply equality_in_mkc_squash in h; repnd.
        clear h0 h1.

        eapply inhabited_type_respects_alphaeqc in h;
          [|apply substc_alphaeqcv;
             apply substc2_product;auto].
        rewrite mkcv_product_substc in h; auto;[].

        repeat lsubstc_vars_as_mkcv.
        autorewrite with slow in h.

        apply inhabited_product in h; repnd.
        clear h0 h1; exrepnd.
        apply member_tnat_implies_computes in h1; exrepnd.
        exists k.
        autorewrite with slow in h0.


        pose proof (lsubstc_vars_mk_add_as_mkcv
                      (mk_var n) mk_one
                      w16
                      (csub_filter (csub_filter (csub_filter s1 [n]) [f]) [m])
                      [m, f, n]
                      c35) as q.
        exrepnd; proof_irr.
        rewrite q1 in h0; clear q1.
        autorewrite with slow in h0.

        rewrite lsubstc_vars_mk_var_as_mkcv3 in h0; auto;
        [|repeat (rw @dom_csub_csub_filter);
           repeat (rw in_remove_nvars); simpl; tcsp].
        autorewrite with slow in h0.

      }


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
