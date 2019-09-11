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

  Authors: Vincent Rahli

*)


Require Export csubst8.
Require Export substc_more.
Require Export per_props_equality.
Require Export per_props_squash.
Require Export seq_util2.
Require Export lsubstc_vars.


Lemma type_implies_tequality_refl {o} :
  forall lib (t : @CTerm o),
    type lib t -> tequality lib t t.
Proof.
  sp.
Qed.
Hint Resolve type_implies_tequality_refl : slow.


Hint Resolve is_kseq_0 : slow.
Hint Resolve member_nseq_nat2nat : slow.
Hint Resolve computes_to_valc_implies_cequivc : slow.


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
      | MkInhSeq _ _ _ _ s isk inh =>
        match ind m s isk inh with
        | existT _ k i =>
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
    | MkInhSeq3 _ _ _ _ _ (MkInhSeq _ _ _ _ s isk inh) =>
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

Lemma mkc_one_as_mkc_nat {o} : @mkc_one o = mkc_nat 1.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

Ltac rev_assert T h :=
    match goal with
    | [ |- ?C ] =>
      assert (T -> C) as h;[introv h|apply h;clear h]
    end.


(**

<<
   H |- ⭣(𝛴 f:ℕ -> ℕ. 𝛱 n:ℕ. ⭣(P n f)

     By ChoiceSequenceInd c z

     H, n:ℕ, f:ℕn -> ℕ |- P n c                                    // base case
     H, n:ℕ, f:ℕn -> ℕ, z:P n f |- ⭣(𝛴 m:ℕ. P (n+1) (ext(f,n,m))) // induction case
     H, n:ℕ, f:ℕn -> ℕ |- (P n f) in Type(i)                       // P is a well-formed predicate on finite sequences
>>

We require that P be well-formed on finite sequencecs.
I don't see any way of proving this rule without assuming that
P is well-formed because the induction hypothesis gives us the
well-formedness of P only for f basically.

*)


Definition choice_sequence_ind_concl {o} (H : @bhyps o) P f n :=
  mk_baresequent
    H
    (mk_conclax
       (mk_squash
          (mk_exists
             (mk_nat2nat)
             f
             (mk_forall
                mk_tnat
                n
                (mk_squash (mk_apply2 P (mk_var n) (mk_var f))))))).

Definition choice_sequence_ind_base {o} (H : @bhyps o) P s B :=
  mk_baresequent H (mk_concl (mk_apply2 P mk_zero s) B).

Definition choice_sequence_ind_ind {o} (H : @bhyps o) P f n m z v :=
  mk_baresequent
    (snoc (snoc (snoc H (mk_hyp n mk_tnat))
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
                (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v))))).

Definition choice_sequence_ind_wf {o} (H : @bhyps o) P f n i :=
  mk_baresequent
    (snoc (snoc H (mk_hyp n mk_tnat))
          (mk_hyp f (mk_natk2nat (mk_var n))))
    (mk_conclax
       (mk_member
          (mk_apply2 P (mk_var n) (mk_var f))
          (mk_uni i))).

Definition rule_choice_sequence_ind {o}
           (P s B : @NTerm o)
           (f m n z v : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (choice_sequence_ind_concl H P f n)
      [
        choice_sequence_ind_base H P s B,
        choice_sequence_ind_ind H P f n m z v,
        choice_sequence_ind_wf H P f n i
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
         (d4 : v <> f)
         (d5 : v <> m)
         (d6 : v <> n)
         (d7 : !LIn m (free_vars P)),
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

    unfold mk_update_seq in ind0.
    repeat lsubstc_vars_as_mkcv.

    rw @mkcv_lam_substc in ind0; auto;[].
    autorewrite with slow in *.
    repeat (rewrite substc2_mk_cv_app_r in ind0; auto;[]).
    lsubst_tac.

    eapply inhabited_type_cequivc;[|exact ind0].
    apply implies_cequivc_apply2; eauto 2 with slow.
    unfold update_seq.
    apply implies_cequivc_lam.
    introv.
    autorewrite with slow.
    apply cequivc_mkc_inteq; eauto 2 with slow.
  }

  {
    exrepnd.
    exists f0; dands; auto.
    introv mem.
    apply member_tnat_implies_computes in mem; exrepnd.
    eapply inhabited_type_cequivc;[|exact (h0 k)].
    apply implies_cequivc_apply2; eauto 2 with slow.
    apply cequivc_sym; eauto 3 with slow.
  }
Qed.
