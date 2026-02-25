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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export bar_induction2.


Lemma bar_induction_meta_sp {o} :
  forall lib P (X c : @CTerm o) v,
    barind_meta2_fun_bar lib P X v
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar ind.
  pose proof (classic (meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta2_fun_ind_implies_cont in ind.
  apply barind_meta2_fun_ind_cont_implies_cont2 in ind.
  apply barind_meta2_fun_ind_cont2_implies_cont3 in ind.
  unfold barind_meta2_fun_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c 0 v) as nc.
  clear Heqnc.

  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind) as g.
  remember (fun m => meta2_fun_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta2_fun_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta2_fun_kseq_NA_nat (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (meta2_fun_alpha_prop1 lib P X (seq2kseq c 0 v) v nc ni f ind n (S m)) as q.
      autodimp q hyp; try lia.
      apply (equality_natk2nat_implies lib m) in q; try lia.
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

      remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
      unfold meta2_fun_kseq_NA in am; exrepnd; simphyps.
      rw @meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try lia.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

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
    boolvar; tcsp; GC; try lia.
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


Definition fun_on_seq_sp {o}
           lib (A1 A2 : @CTerm o) (n : nat) (s1 s2 : CTerm):=
  inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
  # tequality lib (mkc_apply2 A1 (mkc_nat n) s1)
                  (mkc_apply2 A2 (mkc_nat n) s2).

Definition barind_bar_sp {o} lib (A1 A2 : @CTerm o) v :=
  forall (s1 s2 : CTerm),
    eq_seq lib s1 s2
    -> {m : nat , fun_on_seq_sp lib A1 A2 m (seq2kseq s1 m v) (seq2kseq s2 m v) }.

Definition fun_on_upd_seq_sp {o} lib (A1 A2 s1 s2 : @CTerm o) (n m : nat) (v : NVar) :=
  fun_on_seq_sp lib A1 A2 (S n) (update_seq s1 n m v) (update_seq s2 n m v).

Definition barind_ind_sp {o} lib (A1 A2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> (forall (m : nat), fun_on_upd_seq_sp lib A1 A2 s1 s2 n m v)
    -> fun_on_seq_sp lib A1 A2 n s1 s2.

Definition fun_seq_sp_NA {o} lib (A1 A2 : @CTerm o) :=
  {n : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 n
   # !fun_on_seq_sp lib A1 A2 n s1 s2 }}}.

Definition mk_fun_seq_sp_NA {o} {lib} {A1 A2 : @CTerm o}
           (n  : nat)
           (s1 : CTerm)
           (s2 : CTerm)
           (i  : eq_kseq lib s1 s2 n)
           (p  : !fun_on_seq_sp lib A1 A2 n s1 s2) : fun_seq_sp_NA lib A1 A2 :=
  existT _ n (existT _ s1 (existT _ s2 (i,p))).

Definition fun_seq_sp_NA_nat {o} {lib} {A1 A2 : @CTerm o}
           (x : fun_seq_sp_NA lib A1 A2) : nat :=
  projT1 x.

Definition fun_seq_sp_NA_seq1 {o} {lib} {A1 A2 : @CTerm o}
           (x : fun_seq_sp_NA lib A1 A2) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition fun_seq_sp_NA_seq2 {o} {lib} {A1 A2 : @CTerm o}
           (x : fun_seq_sp_NA lib A1 A2) : CTerm :=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Definition barind_ind_sp_cont {o} lib (A1 A2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> !fun_on_seq_sp lib A1 A2 n s1 s2
    -> {m : nat , !fun_on_upd_seq_sp lib A1 A2 s1 s2 n m v}.

Definition barind_ind_sp_cont2 {o} lib (A1 A2 : @CTerm o) v :=
  forall (x : fun_seq_sp_NA lib A1 A2),
    {m : nat
     , !fun_on_upd_seq_sp
        lib A1 A2
        (fun_seq_sp_NA_seq1 x)
        (fun_seq_sp_NA_seq2 x)
        (fun_seq_sp_NA_nat x)
        m v}.

Definition barind_ind_sp_cont3 {o} lib (A1 A2 : @CTerm o) v :=
  {f : fun_seq_sp_NA lib A1 A2 -> nat
   , forall a : fun_seq_sp_NA lib A1 A2,
       !fun_on_upd_seq_sp
          lib A1 A2
          (fun_seq_sp_NA_seq1 a)
          (fun_seq_sp_NA_seq2 a)
          (fun_seq_sp_NA_nat a)
          (f a) v}.

Lemma barind_ind_sp_implies_cont {o} :
  forall lib (A1 A2 : @CTerm o) v,
    barind_ind_sp lib A1 A2 v
    -> barind_ind_sp_cont lib A1 A2 v.
Proof.
  introv ind i ni.
  pose proof (ind n s1 s2 i) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_ind_sp_cont_implies_cont2 {o} :
  forall lib (A1 A2 : @CTerm o) v,
    barind_ind_sp_cont lib A1 A2 v
    -> barind_ind_sp_cont2 lib A1 A2 v.
Proof.
  introv ind; introv.
  unfold fun_seq_sp_NA in x; exrepnd.
  pose proof (ind n s1 s2 x1 x0) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_ind_sp_cont2_implies_cont3 {o} :
  forall lib (A1 A2 : @CTerm o) v,
    barind_ind_sp_cont2 lib A1 A2 v
    -> barind_ind_sp_cont3 lib A1 A2 v.
Proof.
  introv ind; introv.
  unfold barind_ind_sp_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition fun_kseq_sp_NA {o} lib (n : nat) (A1 A2 : @CTerm o) v :=
  {m : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 (S n)
   # seq_normalizable lib s1 (S n) v
   # seq_normalizable lib s2 (S n) v
   # meta_kseq_at_is lib s1 n m
   # meta_kseq_at_is lib s2 n m
   # !fun_on_seq_sp lib A1 A2 (S n) s1 s2 }}}.

Definition mk_fun_kseq_sp_NA {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (m  : nat)
           (s1 : CTerm)
           (s2 : CTerm)
           (i  : eq_kseq lib s1 s2 (S n))
           (q1 : seq_normalizable lib s1 (S n) v)
           (q2 : seq_normalizable lib s2 (S n) v)
           (e1 : meta_kseq_at_is lib s1 n m)
           (e2 : meta_kseq_at_is lib s2 n m)
           (p  : !fun_on_seq_sp lib A1 A2 (S n) s1 s2)
  : fun_kseq_sp_NA lib n A1 A2 v :=
  existT _ m (existT _ s1 (existT _ s2 (i,(q1,(q2,(e1,(e2,p))))))).

Definition fun_kseq_sp_NA_nat {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : fun_kseq_sp_NA lib n A1 A2 v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition fun_kseq_sp_NA_seq1 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : fun_kseq_sp_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Definition fun_kseq_sp_NA_seq2 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : fun_kseq_sp_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Fixpoint alpha_sp {o}
         (lib : library)
         (A1 A2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !fun_on_seq_sp lib A1 A2 0 c1 c2)
         (f  : fun_seq_sp_NA lib A1 A2 -> nat)
         (ind : forall a : fun_seq_sp_NA lib A1 A2,
                  !fun_on_upd_seq_sp
                     lib A1 A2
                     (fun_seq_sp_NA_seq1 a)
                     (fun_seq_sp_NA_seq2 a)
                     (fun_seq_sp_NA_nat a) (f a) v)
         (n : nat) : fun_kseq_sp_NA lib n A1 A2 v :=
  match n with
    | 0 =>
      let i := eq_kseq_0 lib c1 c2 in
      let p := mk_fun_seq_sp_NA 0 c1 c2 i h in
      let k := f p in
      mk_fun_kseq_sp_NA
        k
        (update_seq c1 0 k v)
        (update_seq c2 0 k v)
        (eq_kseq_update lib c1 c2 0 k v i)
        (seq_normalizable_update lib c1 0 k v q1)
        (seq_normalizable_update lib c2 0 k v q2)
        (meta_kseq_at_is_update lib c1 0 k v)
        (meta_kseq_at_is_update lib c2 0 k v)
        (ind p)
    | S m =>
      let (_,r)   := alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind m in
      let (s1,r)  := r in
      let (s2,r)  := r in
      let (i,r)   := r in
      let (z1,r)  := r in
      let (z2,r)  := r in
      let (e1,r)  := r in
      let (e2,na) := r in
      let p := mk_fun_seq_sp_NA (S m) s1 s2 i na in
      let k := f p in
      mk_fun_kseq_sp_NA
        k
        (update_seq s1 (S m) k v)
        (update_seq s2 (S m) k v)
        (eq_kseq_update lib s1 s2 (S m) k v i)
        (seq_normalizable_update lib s1 (S m) k v z1)
        (seq_normalizable_update lib s2 (S m) k v z2)
        (meta_kseq_at_is_update lib s1 (S m) k v)
        (meta_kseq_at_is_update lib s2 (S m) k v)
        (ind p)
  end.

Lemma fun_kseq_sp_NA_seq1_mk_fun_kseq_sp_NA {o} :
  forall lib n A1 A2 v m (c1 c2 : @CTerm o) i q1 q2 e1 e2 p,
    fun_kseq_sp_NA_seq1 (@mk_fun_kseq_sp_NA o lib n A1 A2 v m c1 c2 i q1 q2 e1 e2 p) = c1.
Proof. sp. Qed.

Lemma fun_kseq_sp_NA_seq2_mk_fun_kseq_sp_NA {o} :
  forall lib n A1 A2 v m (c1 c2 : @CTerm o) i q1 q2 e1 e2 p,
    fun_kseq_sp_NA_seq2 (@mk_fun_kseq_sp_NA o lib n A1 A2 v m c1 c2 i q1 q2 e1 e2 p) = c2.
Proof. sp. Qed.

Lemma alpha_sp_prop1 {o} :
  forall lib
         (A1 A2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !fun_on_seq_sp lib A1 A2 0 c1 c2)
         (f  : fun_seq_sp_NA lib A1 A2 -> nat)
         (ind : forall a : fun_seq_sp_NA lib A1 A2,
                  !fun_on_upd_seq_sp
                     lib A1 A2
                     (fun_seq_sp_NA_seq1 a)
                     (fun_seq_sp_NA_seq2 a)
                     (fun_seq_sp_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (fun_kseq_sp_NA_seq1 (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind n))
      (fun_kseq_sp_NA_seq1 (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); lia. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind m) as am.
    unfold fun_kseq_sp_NA in am; exrepnd; allsimpl.

    dup am1 as i.
    apply (eq_kseq_implies lib m0) in i; try lia; exrepnd.
    exists k; dands; auto.

  - remember (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind (k + m)) as am.
    unfold fun_kseq_sp_NA in am; exrepnd; simphyps.
    rw @fun_kseq_sp_NA_seq1_mk_fun_kseq_sp_NA.

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
    boolvar; tcsp; GC; try lia.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma alpha_sp_prop2 {o} :
  forall lib
         (A1 A2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !fun_on_seq_sp lib A1 A2 0 c1 c2)
         (f  : fun_seq_sp_NA lib A1 A2 -> nat)
         (ind : forall a : fun_seq_sp_NA lib A1 A2,
                  !fun_on_upd_seq_sp
                     lib A1 A2
                     (fun_seq_sp_NA_seq1 a)
                     (fun_seq_sp_NA_seq2 a)
                     (fun_seq_sp_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (fun_kseq_sp_NA_seq2 (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind n))
      (fun_kseq_sp_NA_seq2 (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); lia. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind m) as am.
    unfold fun_kseq_sp_NA in am; exrepnd; allsimpl.

    dup am1 as i.
    apply (eq_kseq_implies lib m0) in i; try lia; exrepnd.
    exists k; dands; auto.

  - remember (alpha_sp lib A1 A2 c1 c2 v q1 q2 h f ind (k + m)) as am.
    unfold fun_kseq_sp_NA in am; exrepnd; simphyps.
    rw @fun_kseq_sp_NA_seq2_mk_fun_kseq_sp_NA.

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
    boolvar; tcsp; GC; try lia.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma cequivc_preserves_fun_on_seq_sp_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s2
    -> fun_on_seq_sp lib A1 A2 n s1 s
    -> fun_on_seq_sp lib A1 A2 n s2 s.
Proof.
  introv ceq m.
  allunfold @fun_on_seq_sp; repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_fun_on_seq_sp_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s2
    -> fun_on_seq_sp lib A1 A2 n s s1
    -> fun_on_seq_sp lib A1 A2 n s s2.
Proof.
  introv ceq m.
  allunfold @fun_on_seq_sp; repnd.
  dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_fun_on_seq_sp_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s2
    -> !fun_on_seq_sp lib A1 A2 n s1 s
    -> !fun_on_seq_sp lib A1 A2 n s2 s.
Proof.
  introv ceq h m.
  allunfold @fun_on_seq_sp; repnd.
  destruct h.
  dands; auto.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma cequivc_preserves_not_fun_on_seq_sp_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s2
    -> !fun_on_seq_sp lib A1 A2 n s s1
    -> !fun_on_seq_sp lib A1 A2 n s s2.
Proof.
  introv ceq h m.
  allunfold @fun_on_seq_sp; repnd.
  destruct h.
  dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
  apply cequivc_sym; auto.
Qed.

Lemma bar_induction_meta_sp2 {o} :
  forall lib (A1 A2 c1 c2 : @CTerm o) v,
    (* eq_seq lib c1 c2 *)
    barind_bar_sp lib A1 A2 v
    -> barind_ind_sp lib A1 A2 v
    -> fun_on_seq_sp lib A1 A2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v).
Proof.
  introv bar ind.
  pose proof (classic (fun_on_seq_sp lib A1 A2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v))) as ni.
  repndors; auto;[].
  provefalse.

  apply barind_ind_sp_implies_cont in ind.
  apply barind_ind_sp_cont_implies_cont2 in ind.
  apply barind_ind_sp_cont2_implies_cont3 in ind.
  unfold barind_ind_sp_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c1 0 v) as nc1.
  remember (seq_normalizable_seq2kseq lib c2 0 v) as nc2.
  clear Heqnc1.
  clear Heqnc2.

  remember (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind) as g.
  remember (fun m => fun_kseq_sp_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (fun_kseq_sp_NA_seq1 (g n)) n) as e1.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (fun_kseq_sp_NA_nat (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m)).
    dands;[|].

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (alpha_sp_prop1 lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind n (S m)) as q.
      autodimp q hyp; try lia.
      apply (equality_natk2nat_implies lib m) in q; try lia.
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

      remember (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
      unfold fun_kseq_sp_NA in am; exrepnd; simphyps.
      rw @fun_kseq_sp_NA_seq1_mk_fun_kseq_sp_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try lia.
  }

  assert (forall n, eq_kseq lib (mkc_nseq s) (fun_kseq_sp_NA_seq2 (g n)) n) as e2.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (fun_kseq_sp_NA_nat (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m)).
    dands;[|].

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (alpha_sp_prop2 lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind n (S m)) as q.
      autodimp q hyp; try lia.
      apply (equality_natk2nat_implies lib m) in q; try lia.
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

      remember (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
      unfold fun_kseq_sp_NA in am; exrepnd; simphyps.
      rw @fun_kseq_sp_NA_seq2_mk_fun_kseq_sp_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try lia.
  }

  pose proof (bar (mkc_nseq s) (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c1) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    pose proof (eq_kseq_0 lib (mkc_nseq s) c2) as h2.
    apply (seq2kseq_prop2 _ v) in h2.
    eapply cequivc_preserves_fun_on_seq_sp_left  in b;[|exact h1].
    eapply cequivc_preserves_fun_on_seq_sp_right in b;[|exact h2].
    auto.
  }

  pose proof (e1 (S m)) as q1.
  pose proof (e2 (S m)) as q2.
  apply (seq2kseq_prop2 _ v) in q1.
  apply (seq2kseq_prop2 _ v) in q2.

  eapply cequivc_preserves_fun_on_seq_sp_left  in b;[|exact q1].
  eapply cequivc_preserves_fun_on_seq_sp_right in b;[|exact q2].

  pose proof (e1 m) as z1.
  pose proof (e2 m) as z2.
  apply (seq2kseq_prop2 _ v) in z1.
  apply (seq2kseq_prop2 _ v) in z2.

  eapply cequivc_preserves_not_fun_on_seq_sp_left  in IHm;[|exact z1].
  eapply cequivc_preserves_not_fun_on_seq_sp_right in IHm;[|exact z2].
  clear q1 q2 z1 z2 e1 e2.

(* XXXXXXXXXXXXXXX *)

  subst; allsimpl.
  remember (alpha_sp lib A1 A2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
  unfold fun_kseq_sp_NA in am; exrepnd; allsimpl.

  remember (f (mk_fun_seq_sp_NA (S m) s1 s2 am1 am0)) as fn.

  assert (eq_kseq lib (update_seq s1 (S m) fn v) s1 (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    apply equality_refl in e.
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
    boolvar; tcsp; GC; try lia.
    apply computes_to_valc_implies_cequivc; auto.
  }

  assert (eq_kseq lib (update_seq s2 (S m) fn v) s2 (S m)) as ee2.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    apply equality_sym in e; apply equality_refl in e.
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
    boolvar; tcsp; GC; try lia.
    apply computes_to_valc_implies_cequivc; auto.
  }

  apply (seq2kseq_prop2 _ v) in ee1.
  apply (seq2kseq_prop2 _ v) in ee2.
  eapply cequivc_preserves_fun_on_seq_sp_left  in b;[|exact ee1].
  eapply cequivc_preserves_fun_on_seq_sp_right in b;[|exact ee2].
  clear ee1 ee2.

  unfold seq_normalizable in am2.
  unfold seq_normalizable in am3.
  eapply cequivc_preserves_fun_on_seq_sp_left in b;
    [|apply cequivc_sym;exact am2].
  eapply cequivc_preserves_fun_on_seq_sp_right in b;
    [|apply cequivc_sym;exact am3].
  sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
