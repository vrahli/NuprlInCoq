(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export approx_props3.
Require Export bar_induction.
Require Export seq_util2.


Definition barind_meta_dec {o} lib (B : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> inhabited_type
         lib
         (mkc_or
            (mkc_apply2 B (mkc_nat n) s)
            (mkc_not (mkc_apply2 B (mkc_nat n) s))).

Definition meta_on_seq {o} lib (A : @CTerm o) (n : nat) (s : CTerm) :=
  inhabited_type lib (mkc_apply2 A (mkc_nat n) s).

Definition barind_meta_bar {o} lib (B : @CTerm o) :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta_on_seq lib B m s }.

Definition barind_meta_imp {o} lib (B X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> meta_on_seq lib B n s
    -> meta_on_seq lib X n s.

Definition meta_on_upd_seq {o} lib (X s : @CTerm o) (n m : nat) (v : NVar) :=
  meta_on_seq lib X (S n) (update_seq s n m v).

Definition barind_meta_ind {o} lib (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> (forall (m : nat), meta_on_upd_seq lib X s n m v)
    -> meta_on_seq lib X n s.

Definition barind_meta_ind_cont {o} lib (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> !meta_on_seq lib X n s
    -> {m : nat , !meta_on_upd_seq lib X s n m v}.

Definition meta_seq_NA {o} lib (X : @CTerm o) :=
  {n : nat
   & {s : CTerm
   & is_kseq lib s n
   # !meta_on_seq lib X n s }}.

Definition mk_meta_seq_NA {o} {lib} {X : @CTerm o}
           (n : nat)
           (s : CTerm)
           (i : is_kseq lib s n)
           (p : !meta_on_seq lib X n s) : meta_seq_NA lib X :=
  existT _ n (existT _ s (i,p)).

Definition meta_seq_NA_nat {o} {lib} {X : @CTerm o} (x : meta_seq_NA lib X) : nat :=
  projT1 x.

Definition meta_seq_NA_seq {o} {lib} {X : @CTerm o} (x : meta_seq_NA lib X) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition barind_meta_ind_cont2 {o} lib (X : @CTerm o) v :=
  forall (x : meta_seq_NA lib X),
    {m : nat
     , !meta_on_upd_seq lib X (meta_seq_NA_seq x) (meta_seq_NA_nat x) m v}.

Definition barind_meta_ind_cont2_2 {o} lib (X : @CTerm o) v :=
  forall (x : meta_seq_NA lib X),
    {m : nat
     | !meta_on_upd_seq lib X (meta_seq_NA_seq x) (meta_seq_NA_nat x) m v}.

Definition barind_meta_ind_cont3 {o} lib (X : @CTerm o) v :=
  {f : meta_seq_NA lib X -> nat
   , forall a : meta_seq_NA lib X,
       !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v}.

Lemma barind_meta_ind_implies_cont {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind lib X v
    -> barind_meta_ind_cont lib X v.
Proof.
  introv ind mem ni.
  pose proof (ind n s mem) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta_ind_cont_implies_cont2 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont lib X v
    -> barind_meta_ind_cont2 lib X v.
Proof.
  introv ind; introv.
  unfold meta_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta_ind_cont_implies_cont2_2 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont lib X v
    -> barind_meta_ind_cont2_2 lib X v.
Proof.
  introv ind; introv.
  unfold meta_seq_NA in x; exrepnd; simpl.
  pose proof (ind n s x0 x1) as h; clear ind.
(*  pose proof (classic {m : nat | !meta_on_upd_seq lib X s n m v}) as ni. *)
Abort.

Lemma barind_meta_ind_cont2_implies_cont3 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont2 lib X v
    -> barind_meta_ind_cont3 lib X v.
Proof.
  introv ind; introv.
  unfold barind_meta_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta_kseq_at_is {o} lib (s : @CTerm o) (n m : nat) :=
  cequivc lib (mkc_apply s (mkc_nat n)) (mkc_nat m).

Definition meta_kseq_NA {o} lib (n : nat) (A : @CTerm o) :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # meta_kseq_at_is lib s n m
   # !meta_on_seq lib A (S n) s }}.

Definition mk_meta_kseq_NA {o} {lib} {n : nat} {A : @CTerm o}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (e : meta_kseq_at_is lib s n m)
           (p : !meta_on_seq lib A (S n) s) : meta_kseq_NA lib n A :=
  existT _ m (existT _ s (i,(e,p))).

Definition meta_kseq_NA_nat {o} {lib} {n : nat} {A : @CTerm o}
           (x : meta_kseq_NA lib n A) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_kseq_NA_seq {o} {lib} {n : nat} {A : @CTerm o}
           (x : meta_kseq_NA lib n A) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Lemma meta_kseq_at_is_update {o} :
  forall lib (s : @CTerm o) (n m : nat) (v : NVar),
    meta_kseq_at_is lib (update_seq s n m v) n m.
Proof.
  introv.
  unfold meta_kseq_at_is, update_seq.
  eapply cequivc_trans;[apply cequivc_beta|].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; tcsp; GC.
Qed.

Lemma meta_kseq_NA_seq_mk_meta_kseq_NA {o} :
  forall lib n (A : @CTerm o) m s i e p,
    meta_kseq_NA_seq (@mk_meta_kseq_NA o lib n A m s i e p) = s.
Proof. sp. Qed.

Fixpoint malpha {o}
         (lib : library)
         (X c : @CTerm o)
         (v : NVar)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n : nat) : meta_kseq_NA lib n X :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta_seq_NA 0 c i h in
      let k := f p in
      mk_meta_kseq_NA
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := malpha lib X c v h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (_,na) := r in
      let p := mk_meta_seq_NA (S m) s i na in
      let k := f p in
      mk_meta_kseq_NA
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma malpha_prop1 {o} :
  forall lib
         (X c : @CTerm o)
         (v : NVar)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_kseq_NA_seq (malpha lib X c v h f ind n))
      (meta_kseq_NA_seq (malpha lib X c v h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (malpha lib X c v h f ind m) as am.
    unfold meta_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (malpha lib X c v h f ind (k + m)) as am.
    unfold meta_kseq_NA in am; exrepnd; simphyps.
    rw @meta_kseq_NA_seq_mk_meta_kseq_NA.

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

Definition barind_meta_fun_n {o} lib (A : @CTerm o) (n : nat) :=
  forall s1 s2,
    eq_kseq lib s1 s2 n
    -> tequality lib (mkc_apply2 A (mkc_nat n) s1) (mkc_apply2 A (mkc_nat n) s2).

Definition barind_meta_fun {o} lib (A : @CTerm o) :=
  forall (n : nat), barind_meta_fun_n lib A n.

Lemma meta_on_seq_eq_kseq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    eq_kseq lib s1 s2 n
    -> barind_meta_fun_n lib A n
    -> meta_on_seq lib A n s1
    -> meta_on_seq lib A n s2.
Proof.
  introv e f h.
  allunfold @meta_on_seq.
  apply f in e.
  eapply inhabited_type_tequality; eauto.
Qed.

Lemma not_meta_on_seq_eq_kseq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    eq_kseq lib s1 s2 n
    -> barind_meta_fun_n lib A n
    -> !meta_on_seq lib A n s1
    -> !meta_on_seq lib A n s2.
Proof.
  introv e f h m; destruct h.
  eapply meta_on_seq_eq_kseq;[|auto|exact m].
  apply equality_sym; auto.
Qed.

(* in [barind_true_classically], [c] is [emseqc]*)
Lemma bar_induction_meta {o} :
  forall lib (B X c : @CTerm o) v,
    barind_meta_fun lib X
    -> barind_meta_bar lib B
    -> barind_meta_imp lib B X
    -> barind_meta_ind lib X v
    -> meta_on_seq lib X 0 c.
Proof.
  introv func bar imp ind.
  pose proof (classic (meta_on_seq lib X 0 c)) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_ind_implies_cont in ind.
  apply barind_meta_ind_cont_implies_cont2 in ind.
  apply barind_meta_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (malpha lib X c v ni f ind) as g.
  remember (fun m => meta_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_kseq_NA_nat (malpha lib X c v ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (malpha_prop1 lib X c v ni f ind n (S m)) as q.
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

      remember (malpha lib X c v ni f ind m) as am.
      unfold meta_kseq_NA in am; exrepnd; simphyps.
      rw @meta_kseq_NA_seq_mk_meta_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b; eauto 3 with slow.

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h.
    eapply meta_on_seq_eq_kseq in b;[|exact h|auto]; sp. }

  pose proof (e (S m)) as q1.
  eapply meta_on_seq_eq_kseq in b;[|exact q1|auto].
  pose proof (e m) as q2.
  eapply not_meta_on_seq_eq_kseq in IHm;[|exact q2|auto].
  clear q1 q2 e.

  subst; allsimpl.
  remember (malpha lib X c v ni f ind m) as am.
  unfold meta_kseq_NA in am; exrepnd; allsimpl.

  assert (eq_kseq lib (update_seq s (S m) (f (mk_meta_seq_NA (S m) s am0 am1)) v) s (S m)) as ee.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    unfold is_kseq, eq_kseq in e.
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

  eapply meta_on_seq_eq_kseq in b;[|exact ee|auto].
  sp.
Qed.

Lemma cequivc_preserves_meta_on_seq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> meta_on_seq lib A n s1
    -> meta_on_seq lib A n s2.
Proof.
  introv ceq m.
  allunfold @meta_on_seq.
  eapply inhabited_type_cequivc;[|exact m].
  apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_meta_on_seq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> !meta_on_seq lib A n s1
    -> !meta_on_seq lib A n s2.
Proof.
  introv ceq nm m.
  allunfold @meta_on_seq.
  destruct nm.
  eapply inhabited_type_cequivc;[|exact m].
  apply cequivc_sym.
  apply implies_cequivc_apply2; auto.
Qed.

Definition barind_meta_bar2 {o} lib (B : @CTerm o) v :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta_on_seq lib B m (seq2kseq s m v) }.

Definition meta_kseq_NA2 {o} lib (n : nat) (A : @CTerm o) v :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # seq_normalizable lib s (S n) v
   # meta_kseq_at_is lib s n m
   # !meta_on_seq lib A (S n) s }}.

Definition mk_meta_kseq_NA2 {o} {lib} {n : nat} {A : @CTerm o} {v}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (q : seq_normalizable lib s (S n) v)
           (e : meta_kseq_at_is lib s n m)
           (p : !meta_on_seq lib A (S n) s) : meta_kseq_NA2 lib n A v :=
  existT _ m (existT _ s (i,(q,(e,p)))).

Definition meta_kseq_NA2_nat {o} {lib} {n : nat} {A : @CTerm o} {v}
           (x : meta_kseq_NA2 lib n A v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_kseq_NA2_seq {o} {lib} {n : nat} {A : @CTerm o} {v}
           (x : meta_kseq_NA2 lib n A v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Fixpoint malpha2 {o}
         (lib : library)
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n : nat) : meta_kseq_NA2 lib n X v :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta_seq_NA 0 c i h in
      let k := f p in
      mk_meta_kseq_NA2
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (seq_normalizable_update lib c 0 k v q)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := malpha2 lib X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (_,na) := r in
      let p := mk_meta_seq_NA (S m) s i na in
      let k := f p in
      mk_meta_kseq_NA2
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (seq_normalizable_update lib s (S m) k v z)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma meta_kseq_NA2_seq_mk_meta_kseq_NA2 {o} :
  forall lib n (A : @CTerm o) v m s i q e p,
    meta_kseq_NA2_seq (@mk_meta_kseq_NA2 o lib n A v m s i q e p) = s.
Proof. sp. Qed.

Lemma malpha2_prop1 {o} :
  forall lib
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_kseq_NA2_seq (malpha2 lib X c v q h f ind n))
      (meta_kseq_NA2_seq (malpha2 lib X c v q h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (malpha2 lib X c v q h f ind m) as am.
    unfold meta_kseq_NA2 in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (malpha2 lib X c v q h f ind (k + m)) as am.
    unfold meta_kseq_NA2 in am; exrepnd; simphyps.
    rw @meta_kseq_NA2_seq_mk_meta_kseq_NA2.

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

(* same as bar_induction_meta but does not use X's functionality and
   adds a few seq2kseq instead *)
Lemma bar_induction_meta2 {o} :
  forall lib (B X c : @CTerm o) v,
    barind_meta_bar2 lib B v
    -> barind_meta_imp lib B X
    -> barind_meta_ind lib X v
    -> meta_on_seq lib X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta_on_seq lib X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_ind_implies_cont in ind.
  apply barind_meta_ind_cont_implies_cont2 in ind.
  apply barind_meta_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind) as g.
  remember (fun m => meta_kseq_NA2_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_kseq_NA2_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_kseq_NA2_nat (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (malpha2_prop1 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind n (S m)) as q.
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

      remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m) as am.
      unfold meta_kseq_NA2 in am; exrepnd; simphyps.
      rw @meta_kseq_NA2_seq_mk_meta_kseq_NA2.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h.
    apply (seq2kseq_prop2 _ v) in h.
    eapply cequivc_preserves_meta_on_seq in b;[|exact h]; auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.
  eapply cequivc_preserves_meta_on_seq in b;[|exact q1].
  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.
  eapply cequivc_preserves_not_meta_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m) as am.
  unfold meta_kseq_NA2 in am; exrepnd; allsimpl.

  assert (eq_kseq
            lib
            (update_seq s (S m) (f (mk_meta_seq_NA (S m) s am0 am1)) v)
            s
            (S m)) as ee.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    unfold is_kseq, eq_kseq in e.
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

  apply (seq2kseq_prop2 _ v) in ee.
  eapply cequivc_preserves_meta_on_seq in b;[|exact ee].
  clear ee.
  unfold seq_normalizable in am2.
  eapply cequivc_preserves_meta_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.

Definition meta_fun_on_seq {o} lib (A1 A2 : @CTerm o) (n : nat) (s1 s2 : CTerm) :=
  inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
  # tequality lib (mkc_apply2 A1 (mkc_nat n) s1) (mkc_apply2 A2 (mkc_nat n) s2).

Definition meta_fun_on_upd_seq {o} lib (X1 X2 s1 s2 : @CTerm o) (n m : nat) (v : NVar) :=
  meta_fun_on_seq lib X1 X2 (S n) (update_seq s1 n m v) (update_seq s2 n m v).

Definition barind_meta_fun_ind {o} lib (X1 X2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> (forall (m : nat), meta_fun_on_upd_seq lib X1 X2 s1 s2 n m v)
    -> meta_fun_on_seq lib X1 X2 n s1 s2.

Definition barind_meta_fun_ind_cont {o} lib (X1 X2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> !meta_fun_on_seq lib X1 X2 n s1 s2
    -> {m : nat , !meta_fun_on_upd_seq lib X1 X2 s1 s2 n m v}.

Definition meta_fun_seq_NA {o} lib (X1 X2 : @CTerm o) :=
  {n : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 n
   # !meta_fun_on_seq lib X1 X2 n s1 s2 }}}.

Definition mk_meta_fun_seq_NA {o} {lib} {X1 X2 : @CTerm o}
           (n  : nat)
           (s1 : CTerm)
           (s2 : CTerm)
           (i  : eq_kseq lib s1 s2 n)
           (p  : !meta_fun_on_seq lib X1 X2 n s1 s2) : meta_fun_seq_NA lib X1 X2 :=
  existT _ n (existT _ s1 (existT _ s2 (i,p))).

Definition meta_fun_seq_NA_nat {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : nat :=
  projT1 x.

Definition meta_fun_seq_NA_seq1 {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition meta_fun_seq_NA_seq2 {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : CTerm :=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Definition barind_meta_fun_ind_cont2 {o} lib (X1 X2 : @CTerm o) v :=
  forall (x : meta_fun_seq_NA lib X1 X2),
    {m : nat
     , !meta_fun_on_upd_seq
        lib X1 X2
        (meta_fun_seq_NA_seq1 x)
        (meta_fun_seq_NA_seq2 x)
        (meta_fun_seq_NA_nat x)
        m v}.

Definition barind_meta_fun_ind_cont3 {o} lib (X1 X2 : @CTerm o) v :=
  {f : meta_fun_seq_NA lib X1 X2 -> nat
   , forall a : meta_fun_seq_NA lib X1 X2,
       !meta_fun_on_upd_seq
          lib X1 X2
          (meta_fun_seq_NA_seq1 a)
          (meta_fun_seq_NA_seq2 a)
          (meta_fun_seq_NA_nat a)
          (f a) v}.

Lemma barind_meta_fun_ind_implies_cont {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind lib X1 X2 v
    -> barind_meta_fun_ind_cont lib X1 X2 v.
Proof.
  introv ind mem ni.
  pose proof (ind n s1 s2 mem) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta_fun_ind_cont_implies_cont2 {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind_cont lib X1 X2 v
    -> barind_meta_fun_ind_cont2 lib X1 X2 v.
Proof.
  introv ind; introv.
  unfold meta_fun_seq_NA in x; exrepnd.
  pose proof (ind n s1 s2 x1 x0) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta_fun_ind_cont2_implies_cont3 {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind_cont2 lib X1 X2 v
    -> barind_meta_fun_ind_cont3 lib X1 X2 v.
Proof.
  introv ind; introv.
  unfold barind_meta_fun_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta_fun_kseq_NA {o} lib (n : nat) (A1 A2 : @CTerm o) v :=
  {m : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 (S n)
   # seq_normalizable lib s1 (S n) v
   # seq_normalizable lib s2 (S n) v
   # meta_kseq_at_is lib s1 n m
   # meta_kseq_at_is lib s2 n m
   # !meta_fun_on_seq lib A1 A2 (S n) s1 s2 }}}.

Definition mk_meta_fun_kseq_NA {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (m : nat)
           (s1 s2 : CTerm)
           (i  : eq_kseq lib s1 s2 (S n))
           (q1 : seq_normalizable lib s1 (S n) v)
           (q2 : seq_normalizable lib s2 (S n) v)
           (e1 : meta_kseq_at_is lib s1 n m)
           (e2 : meta_kseq_at_is lib s2 n m)
           (p  : !meta_fun_on_seq lib A1 A2 (S n) s1 s2) : meta_fun_kseq_NA lib n A1 A2 v :=
  existT _ m (existT _ s1 (existT _ s2 (i,(q1,(q2,(e1,(e2,p))))))).

Definition meta_fun_kseq_NA_nat {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_fun_kseq_NA_seq1 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Definition meta_fun_kseq_NA_seq2 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Fixpoint m_fun_alpha {o}
         (lib : library)
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (n : nat) : meta_fun_kseq_NA lib n X1 X2 v :=
  match n with
    | 0 =>
      let i := eq_kseq_0 lib c1 c2 in
      let p := mk_meta_fun_seq_NA 0 c1 c2 i h in
      let k := f p in
      mk_meta_fun_kseq_NA
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
      let (_,r) := m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m in
      let (s1,r) := r in
      let (s2,r) := r in
      let (ek,r) := r in
      let (z1,r) := r in
      let (z2,r) := r in
      let (e1,r) := r in
      let (e2,na) := r in
      let p := mk_meta_fun_seq_NA (S m) s1 s2 ek na in
      let k := f p in
      mk_meta_fun_kseq_NA
        k
        (update_seq s1 (S m) k v)
        (update_seq s2 (S m) k v)
        (eq_kseq_update lib s1 s2 (S m) k v ek)
        (seq_normalizable_update lib s1 (S m) k v z1)
        (seq_normalizable_update lib s2 (S m) k v z2)
        (meta_kseq_at_is_update lib s1 (S m) k v)
        (meta_kseq_at_is_update lib s2 (S m) k v)
        (ind p)
  end.

Lemma meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA {o} :
  forall lib n (A1 A2 : @CTerm o) v m s1 s2 i q1 q2 e1 e2 p,
    meta_fun_kseq_NA_seq1 (@mk_meta_fun_kseq_NA o lib n A1 A2 v m s1 s2 i q1 q2 e1 e2 p) = s1.
Proof. sp. Qed.

Lemma meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA {o} :
  forall lib n (A1 A2 : @CTerm o) v m s1 s2 i q1 q2 e1 e2 p,
    meta_fun_kseq_NA_seq2 (@mk_meta_fun_kseq_NA o lib n A1 A2 v m s1 s2 i q1 q2 e1 e2 p) = s2.
Proof. sp. Qed.

Lemma m_fun_alpha_prop1 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind n))
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; allsimpl.

    dup am1 as i.
    apply (eq_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind (k + m)) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.

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

Lemma m_fun_alpha_prop2 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (m : nat),
    equality
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (meta_fun_kseq_NA_seq2 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv.
  induction m; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0; try omega.

  remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
  unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
  rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
  rw @meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA.

  destruct (deq_nat m0 m) as [d|d].

  - subst.
    exists m1.
    dands.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.

  - assert (m0 < m) as ltm by omega.
    clear d ltm0.

    eapply equality_natk2nat_implies in IHm;[|exact ltm].
    exrepnd.
    exists k; dands; auto.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.
      apply computes_to_valc_implies_cequivc; auto.

    + unfold update_seq.
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

Lemma m_fun_alpha_prop3 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (m : nat),
    cequivc
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (meta_fun_kseq_NA_seq2 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m)).
Proof.
  introv.

  assert (cequivc lib c1 c2) as ceq.
  { eapply cequivc_trans;[exact q1|].
    eapply cequivc_trans;[|apply cequivc_sym;exact q2].
    apply cequivc_seq2kseq_0. }

  induction m; introv; allsimpl.

  - remember (f (mk_meta_fun_seq_NA 0 c1 c2 (eq_kseq_0 lib c1 c2) h)) as n; clear Heqn.
    apply cequivc_update_seq; auto.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
    rw @meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA.
    apply cequivc_update_seq; auto.
Qed.

Definition barind_meta_fun_bar {o} lib (B1 B2 : @CTerm o) v :=
  forall (s1 s2 : CTerm),
    eq_seq lib s1 s2
    -> {m : nat , meta_fun_on_seq lib B1 B2 m (seq2kseq s1 m v) (seq2kseq s2 m v) }.

Definition barind_meta_fun_imp {o} lib (B1 B2 X1 X2 : @CTerm o) :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> meta_fun_on_seq lib B1 B2 n s1 s2
    -> meta_fun_on_seq lib X1 X2 n s1 s2.

Lemma cequivc_preserves_meta_fun_on_seq_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s
    -> meta_fun_on_seq lib A1 A2 n s1 s2
    -> meta_fun_on_seq lib A1 A2 n s s2.
Proof.
  introv ceq m.
  allunfold @meta_fun_on_seq; repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_meta_fun_on_seq_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s2 s
    -> meta_fun_on_seq lib A1 A2 n s1 s2
    -> meta_fun_on_seq lib A1 A2 n s1 s.
Proof.
  introv ceq m.
  allunfold @meta_fun_on_seq; repnd.
  dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_meta_fun_on_seq_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s
    -> !meta_fun_on_seq lib A1 A2 n s1 s2
    -> !meta_fun_on_seq lib A1 A2 n s s2.
Proof.
  introv ceq h m.
  allunfold @meta_fun_on_seq; repnd.
  destruct h; dands.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma cequivc_preserves_not_meta_fun_on_seq_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s2 s
    -> !meta_fun_on_seq lib A1 A2 n s1 s2
    -> !meta_fun_on_seq lib A1 A2 n s1 s.
Proof.
  introv ceq h m.
  allunfold @meta_fun_on_seq; repnd.
  destruct h; dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
  apply cequivc_sym; auto.
Qed.

Lemma bar_induction_meta3 {o} :
  forall lib (B1 B2 X1 X2 c1 c2 : @CTerm o) v,
    barind_meta_fun_bar lib B1 B2 v
    -> barind_meta_fun_imp lib B1 B2 X1 X2
    -> barind_meta_fun_ind lib X1 X2 v
    -> meta_fun_on_seq lib X1 X2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta_fun_on_seq lib X1 X2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_fun_ind_implies_cont in ind.
  apply barind_meta_fun_ind_cont_implies_cont2 in ind.
  apply barind_meta_fun_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_fun_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c1 0 v) as nc1.
  remember (seq_normalizable_seq2kseq lib c2 0 v) as nc2.
  clear Heqnc1 Heqnc2.

  pose proof (cequivc_seq2kseq_0 lib v c1 c2) as ceq0.

  remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind) as g.
  remember (fun m => meta_fun_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_fun_kseq_NA_seq1 (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_fun_kseq_NA_nat (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (m_fun_alpha_prop1 lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind n (S m)) as q.
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

      remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
      unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
      rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (m_fun_alpha_prop3
                lib X1 X2
                (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2
                ni f ind) as ceqn.
  rw <- Heqg in ceqn.

  pose proof (bar (mkc_nseq s) (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c1) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    pose proof (eq_kseq_0 lib (mkc_nseq s) c2) as h2.
    apply (seq2kseq_prop2 _ v) in h2.
    eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact h1].
    eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact h2].
    auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.

  pose proof (ceqn (S m)) as ceqsm.
  apply (implies_cequivc_seq2kseq _ v (S m)) in ceqsm.

  eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact q1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact q1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact ceqsm].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.

  pose proof (ceqn m) as ceqm.
  apply (implies_cequivc_seq2kseq _ v m) in ceqm.

  eapply cequivc_preserves_not_meta_fun_on_seq_left in IHm;[|exact q2].
  eapply cequivc_preserves_not_meta_fun_on_seq_right in IHm;[|exact q2].
  eapply cequivc_preserves_not_meta_fun_on_seq_right in IHm;[|exact ceqm].
  clear q1 q2 e ceqsm ceqm.

  subst; allsimpl.
  remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
  unfold meta_fun_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_meta_fun_seq_NA (S m) s1 s2 am1 am0)) as fn.

  assert (eq_kseq lib (update_seq s1 (S m) fn v) s1 (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    unfold eq_kseq in e.
    eapply equality_natk2nat_implies in e;[|exact ltm1]; exrepnd.
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

  assert (eq_kseq lib (update_seq s2 (S m) fn v) s2 (S m)) as ee2.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    unfold eq_kseq in e.
    eapply equality_natk2nat_implies in e;[|exact ltm1]; exrepnd.
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
  apply (seq2kseq_prop2 _ v) in ee2.
  eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact ee1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact ee2].
  clear ee1 ee2.

  unfold seq_normalizable in am2.
  unfold seq_normalizable in am3.
  eapply cequivc_preserves_meta_fun_on_seq_left in b;
    [|apply cequivc_sym;exact am2].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;
    [|apply cequivc_sym;exact am3].
  sp.
Qed.


Definition meta2_fun_on_seq {o} lib P (A1 : @CTerm o) (n : nat) (s1 : CTerm) :=
  forall A2 s2,
    eq_kseq lib s1 s2 n
    -> P A2
    -> inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
       # tequality lib (mkc_apply2 A1 (mkc_nat n) s1) (mkc_apply2 A2 (mkc_nat n) s2).

Definition meta2_fun_on_upd_seq {o} lib P (X s : @CTerm o) (n m : nat) (v : NVar) :=
  meta2_fun_on_seq lib P X (S n) (update_seq s n m v).

Definition barind_meta2_fun_ind {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> (forall (m : nat), meta2_fun_on_upd_seq lib P X s n m v)
    -> meta2_fun_on_seq lib P X n s.

Definition barind_meta2_fun_ind_cont {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> !meta2_fun_on_seq lib P X n s
    -> {m : nat , !meta2_fun_on_upd_seq lib P X s n m v}.

Definition meta2_fun_seq_NA {o} lib P (X : @CTerm o) :=
  {n : nat
   & {s : CTerm
   & is_kseq lib s n
   # !meta2_fun_on_seq lib P X n s }}.

Definition mk_meta2_fun_seq_NA {o} {lib} {P} {X : @CTerm o}
           (n : nat)
           (s : CTerm)
           (i : is_kseq lib s n)
           (p : !meta2_fun_on_seq lib P X n s) : meta2_fun_seq_NA lib P X :=
  existT _ n (existT _ s (i,p)).

Definition meta2_fun_seq_NA_nat {o} {lib} {P} {X : @CTerm o} (x : meta2_fun_seq_NA lib P X) : nat :=
  projT1 x.

Definition meta2_fun_seq_NA_seq {o} {lib} {P} {X : @CTerm o} (x : meta2_fun_seq_NA lib P X) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition barind_meta2_fun_ind_cont2 {o} lib P (X : @CTerm o) v :=
  forall (x : meta2_fun_seq_NA lib P X),
    {m : nat
     , !meta2_fun_on_upd_seq
        lib P X
        (meta2_fun_seq_NA_seq x)
        (meta2_fun_seq_NA_nat x)
        m v}.

Definition barind_meta2_fun_ind_cont3 {o} lib P (X : @CTerm o) v :=
  {f : meta2_fun_seq_NA lib P X -> nat
   , forall a : meta2_fun_seq_NA lib P X,
       !meta2_fun_on_upd_seq
          lib P X
          (meta2_fun_seq_NA_seq a)
          (meta2_fun_seq_NA_nat a)
          (f a) v}.

Lemma barind_meta2_fun_ind_implies_cont {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind lib P X v
    -> barind_meta2_fun_ind_cont lib P X v.
Proof.
  introv ind i ni.
  pose proof (ind n s i) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta2_fun_ind_cont_implies_cont2 {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind_cont lib P X v
    -> barind_meta2_fun_ind_cont2 lib P X v.
Proof.
  introv ind; introv.
  unfold meta2_fun_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta2_fun_ind_cont2_implies_cont3 {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind_cont2 lib P X v
    -> barind_meta2_fun_ind_cont3 lib P X v.
Proof.
  introv ind; introv.
  unfold barind_meta2_fun_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta2_fun_kseq_NA {o} lib P (n : nat) (A : @CTerm o) v :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # seq_normalizable lib s (S n) v
   # meta_kseq_at_is lib s n m
   # !meta2_fun_on_seq lib P A (S n) s }}.

Definition mk_meta2_fun_kseq_NA {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (q : seq_normalizable lib s (S n) v)
           (e : meta_kseq_at_is lib s n m)
           (p : !meta2_fun_on_seq lib P A (S n) s) : meta2_fun_kseq_NA lib P n A v :=
  existT _ m (existT _ s (i,(q,(e,p)))).

Definition meta2_fun_kseq_NA_nat {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : meta2_fun_kseq_NA lib P n A v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta2_fun_kseq_NA_seq {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : meta2_fun_kseq_NA lib P n A v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Fixpoint meta2_fun_alpha {o}
         (lib : library)
         P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v)
         (n : nat) : meta2_fun_kseq_NA lib P n X v :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta2_fun_seq_NA 0 c i h in
      let k := f p in
      mk_meta2_fun_kseq_NA
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (seq_normalizable_update lib c 0 k v q)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := meta2_fun_alpha lib P X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (e,na) := r in
      let p := mk_meta2_fun_seq_NA (S m) s i na in
      let k := f p in
      mk_meta2_fun_kseq_NA
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (seq_normalizable_update lib s (S m) k v z)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA {o} :
  forall lib P n (A : @CTerm o) v m s i q e p,
    meta2_fun_kseq_NA_seq (@mk_meta2_fun_kseq_NA o lib P n A v m s i q e p) = s.
Proof. sp. Qed.

Lemma meta2_fun_alpha_prop1 {o} :
  forall lib P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta2_fun_kseq_NA_seq (meta2_fun_alpha lib P X c v q h f ind n))
      (meta2_fun_kseq_NA_seq (meta2_fun_alpha lib P X c v q h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (meta2_fun_alpha lib P X c v q h f ind m) as am.
    unfold meta2_fun_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (meta2_fun_alpha lib P X c v q h f ind (k + m)) as am.
    unfold meta2_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA.

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

Definition barind_meta2_fun_bar {o} lib Q (B : @CTerm o) v :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta2_fun_on_seq lib Q B m (seq2kseq s m v) }.

Definition barind_meta2_fun_imp {o} lib Q P (B X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> meta2_fun_on_seq lib Q B n s
    -> meta2_fun_on_seq lib P X n s.

Lemma cequivc_preserves_meta2_fun_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> meta2_fun_on_seq lib P A n s1
    -> meta2_fun_on_seq lib P A n s2.
Proof.
  introv ceq m.
  allunfold @meta2_fun_on_seq; repnd.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_left;[|exact ek]; auto.
    apply cequivc_sym; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_meta2_fun_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> !meta2_fun_on_seq lib P A n s1
    -> !meta2_fun_on_seq lib P A n s2.
Proof.
  introv ceq h m.
  allunfold @meta2_fun_on_seq; repnd.
  destruct h.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_left;[|exact ek]; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma bar_induction_meta4 {o} :
  forall lib Q P (B X c : @CTerm o) v,
    barind_meta2_fun_bar lib Q B v
    -> barind_meta2_fun_imp lib Q P B X
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
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
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
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

(*Print Assumptions bar_induction_meta4.*)

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
