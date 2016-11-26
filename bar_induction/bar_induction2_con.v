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

Require Export bar_induction2.


Definition barind_meta2_fun_bar_con {o} lib Q S (B R : @CTerm o) v :=
  forall (s : CTerm),
    is_seq lib s
    -> (forall m, meta2_fun_on_seq lib S R m s)
    -> {m : nat , meta2_fun_on_seq lib Q B m (seq2kseq s m v) }.

Definition barind_meta2_fun_imp_con {o} lib Q S P (B R X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> meta2_fun_on_seq lib S R n s
    -> meta2_fun_on_seq lib Q B n s
    -> meta2_fun_on_seq lib P X n s.

Definition barind_meta2_fun_ind_con {o} lib S P (R X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> (forall (m : nat),
           meta2_fun_on_seq lib S R n s
           -> meta2_fun_on_upd_seq lib P X s n m v)
    -> meta2_fun_on_seq lib P X n s.

Definition barind_meta2_fun_ind_con_cont {o} lib S P (R X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> !meta2_fun_on_seq lib P X n s
    -> {m : nat
        , !meta2_fun_on_upd_seq lib P X s n m v
        /\ meta2_fun_on_seq lib S R n s}.

Lemma barind_meta2_fun_ind_con_implies_cont {o} :
  forall lib S P (R X : @CTerm o) v,
    barind_meta2_fun_ind_con lib S P R X v
    -> barind_meta2_fun_ind_con_cont lib S P R X v.
Proof.
  introv ind i ni.
  pose proof (ind n s i) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
  exrepnd.
  exists n0.
  dands.
  { intro h; tcsp. }
  { pose proof (classic (meta2_fun_on_seq lib S R n s)) as k.
    repndors; auto.
    destruct h0; tcsp. }
Qed.

Definition barind_meta2_fun_ind_con_cont2 {o} lib S P (R X : @CTerm o) v :=
  forall (x : meta2_fun_seq_NA lib P X),
    {m : nat
     , !meta2_fun_on_upd_seq
        lib P X
        (meta2_fun_seq_NA_seq x)
        (meta2_fun_seq_NA_nat x)
        m v
     /\ meta2_fun_on_seq
          lib S R
          (meta2_fun_seq_NA_nat x)
          (meta2_fun_seq_NA_seq x)}.

Definition barind_meta2_fun_ind_con_cont3 {o} lib S P (R X : @CTerm o) v :=
  {f : meta2_fun_seq_NA lib P X -> nat
   , forall a : meta2_fun_seq_NA lib P X,
       !meta2_fun_on_upd_seq
          lib P X
          (meta2_fun_seq_NA_seq a)
          (meta2_fun_seq_NA_nat a)
          (f a) v
       /\ meta2_fun_on_seq lib S R (meta2_fun_seq_NA_nat a) (meta2_fun_seq_NA_seq a)}.

Lemma barind_meta2_fun_ind_con_cont_implies_cont2 {o} :
  forall lib S P (R X : @CTerm o) v,
    barind_meta2_fun_ind_con_cont lib S P R X v
    -> barind_meta2_fun_ind_con_cont2 lib S P R X v.
Proof.
  introv ind; introv.
  unfold meta2_fun_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta2_fun_ind_con_cont2_implies_cont3 {o} :
  forall lib S P (R X : @CTerm o) v,
    barind_meta2_fun_ind_con_cont2 lib S P R X v
    -> barind_meta2_fun_ind_con_cont3 lib S P R X v.
Proof.
  introv ind; introv.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta2_fun_con_kseq_NA {o} lib C P (n : nat) (R A : @CTerm o) v :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s n
   # seq_normalizable lib s n v
   # !meta2_fun_on_seq lib P A (S n) (update_seq s n m v)
   # meta2_fun_on_seq lib C R n s}}.

Definition mk_meta2_fun_con_kseq_NA {o} {lib} {C P} {n : nat} {R A : @CTerm o} {v}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s n)
           (q : seq_normalizable lib s n v)
           (p : !meta2_fun_on_seq lib P A (S n) (update_seq s n m v))
           (c : meta2_fun_on_seq lib C R n s) : meta2_fun_con_kseq_NA lib C P n R A v :=
  existT _ m (existT _ s (i,(q,(p,c)))).

Definition meta2_fun_con_kseq_NA_nat {o} {lib} {C P} {n : nat} {R A : @CTerm o} {v}
           (x : meta2_fun_con_kseq_NA lib C P n R A v) : nat:=
  match x with
    | existT _ m _ => m
  end.

Definition meta2_fun_con_kseq_NA_seq {o} {lib} {C P} {n : nat} {R A : @CTerm o} {v}
           (x : meta2_fun_con_kseq_NA lib C P n R A v) : CTerm:=
  match x with
    | existT _ _ (existT _ s _) => s
  end.

Hint Rewrite @mkcv_inteq_substc : slow.
Hint Rewrite @mkcv_apply_substc : slow.

Lemma eq_kseq_update_seq_implies {o} :
  forall lib (s : @CTerm o) n k v s2,
    eq_kseq lib (update_seq s n k v) s2 n
    -> eq_kseq lib s s2 n.
Proof.
  introv eqs.
  unfold eq_kseq in *.
  apply implies_equality_natk2nat.
  introv ltmn.
  apply (equality_natk2nat_implies _ m) in eqs; auto; exrepnd.
  exists k0; dands; auto.
  clear eqs0.
  apply cequivc_nat_implies_computes_to_valc.
  apply computes_to_valc_implies_cequivc in eqs1.
  unfold update_seq in eqs1.
  eapply cequivc_trans in eqs1;[|apply cequivc_sym;apply cequivc_beta].
  autorewrite with slow in *.
  eapply cequivc_trans in eqs1;[|apply cequivc_sym;apply cequivc_mkc_inteq_nat].
  boolvar; subst; try omega; auto.
Qed.

Lemma implies_meta2_fun_on_seq_update_seq {o} :
  forall lib C (R : @CTerm o) s n k v,
    is_kseq lib (update_seq s n k v) (S n)
    -> meta2_fun_on_seq lib C R n s
    -> meta2_fun_on_seq lib C R n (update_seq s n k v).
Proof.
  introv isk m eqs c.
  pose proof (m A2 s2) as q; clear m.
  repeat (autodimp q hyp).
  { apply eq_kseq_update_seq_implies in eqs; auto. }
  repnd; dands; auto.
Abort.

Fixpoint meta2_fun_con_alpha {o}
         (lib : library)
         C P
         (R X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v
                  /\ meta2_fun_on_seq
                       lib C R
                       (meta2_fun_seq_NA_nat a)
                       (meta2_fun_seq_NA_seq a))
         (n : nat) : meta2_fun_con_kseq_NA lib C P n R X v :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta2_fun_seq_NA 0 c i h in
      let k := f p in
      mk_meta2_fun_con_kseq_NA
        k
        c
        i
        q
        (proj1 (ind p))
        (proj2 (ind p))
    | S m =>
      let (x,r) := meta2_fun_con_alpha lib C P R X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (e,na) := r in
      let p := mk_meta2_fun_seq_NA (S m) (update_seq s m x v) (is_kseq_update _ _ _ _ _ i) e in
      let k := f p in
      mk_meta2_fun_con_kseq_NA
        k
        (update_seq s m x v)
        (is_kseq_update lib s m x v i)
        (seq_normalizable_update lib s m x v z)
        (proj1 (ind p))
        (proj2 (ind p))
  end.

Lemma meta2_fun_con_kseq_NA_seq_mk_meta2_fun_con_kseq_NA {o} :
  forall lib C P n (R A : @CTerm o) v m s i q e p,
    meta2_fun_con_kseq_NA_seq (@mk_meta2_fun_con_kseq_NA o lib C P n R A v m s i q e p) = s.
Proof. sp. Qed.
Hint Rewrite @meta2_fun_con_kseq_NA_seq_mk_meta2_fun_con_kseq_NA : slow.

Lemma meta2_fun_con_alpha_prop1 {o} :
  forall lib C P
         (R X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v
                  /\ meta2_fun_on_seq
                       lib C R
                       (meta2_fun_seq_NA_nat a)
                       (meta2_fun_seq_NA_seq a))
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta2_fun_con_kseq_NA_seq (meta2_fun_con_alpha lib C P R X c v q h f ind n))
      (meta2_fun_con_kseq_NA_seq (meta2_fun_con_alpha lib C P R X c v q h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (meta2_fun_con_alpha lib C P R X c v q h f ind m) as am.
    unfold meta2_fun_con_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (meta2_fun_con_alpha lib C P R X c v q h f ind (k + m)) as am.
    unfold meta2_fun_con_kseq_NA in am; exrepnd; simphyps.
    autorewrite with slow.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    autorewrite with slow.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma bar_induction_meta4_con {o} :
  forall lib Q C P (B R X c : @CTerm o) v,
    barind_meta2_fun_bar_con lib Q C B R v
    -> barind_meta2_fun_imp_con lib Q C P B R X
    -> barind_meta2_fun_ind_con lib C P R X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta2_fun_ind_con_implies_cont in ind.
  apply barind_meta2_fun_ind_con_cont_implies_cont2 in ind.
  apply barind_meta2_fun_ind_con_cont2_implies_cont3 in ind.
  unfold barind_meta2_fun_ind_con_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c 0 v) as nc.
  clear Heqnc.

  remember (meta2_fun_con_alpha lib C P R X (seq2kseq c 0 v) v nc ni f ind) as g.
  remember (fun m => meta2_fun_con_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta2_fun_con_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta2_fun_con_kseq_NA_nat
              (meta2_fun_con_alpha lib C P R X (seq2kseq c 0 v) v nc ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (meta2_fun_con_alpha_prop1 lib C P R X (seq2kseq c 0 v) v nc ni f ind n (S m)) as q.
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

      remember (meta2_fun_con_alpha lib C P R X (seq2kseq c 0 v) v nc ni f ind m) as am.
      unfold meta2_fun_con_kseq_NA in am; exrepnd; simphyps.
      autorewrite with slow.
      unfold meta2_fun_con_kseq_NA_nat.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      autorewrite with slow.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  repeat (autodimp b hyp); eauto 3 with slow.
  {
    introv.
  }
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact h1].
    auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.

  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact q1].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.

  eapply cequivc_preserves_not_meta2_fun_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
  unfold meta2_fun_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_meta2_fun_seq_NA (S m) s am0 am1)) as fn.

  assert (eq_kseq lib (update_seq s (S m) fn v) s (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    eapply member_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
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
  }

  apply (seq2kseq_prop2 _ v) in ee1.
  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact ee1].
  clear ee1.

  unfold seq_normalizable in am2.
  eapply cequivc_preserves_meta2_fun_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.
