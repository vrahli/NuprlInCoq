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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export bar_induction.
Require Export seq_util.


Definition is_seq_nout {o} lib (s : @CTerm o) := member lib s nat2nout.

Definition eq_kseq_nout {o} lib (s1 s2 : @CTerm o) (n : nat) :=
  equality lib s1 s2 (natk2nout (mkc_nat n)).

Definition is_kseq_nout {o} lib (s : @CTerm o) (n : nat) := eq_kseq_nout lib s s n.

Definition nout_on_seq {o} lib P (A1 : @CTerm o) (n : nat) (s1 : CTerm) :=
  forall A2 s2,
    eq_kseq_nout lib s1 s2 n
    -> P A2
    -> inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
       # tequality lib (mkc_apply2 A1 (mkc_nat n) s1) (mkc_apply2 A2 (mkc_nat n) s2).

Definition barind_nout_bar {o} lib Q (B : @CTerm o) v :=
  forall (s : CTerm),
    is_seq_nout lib s
    -> {m : nat , nout_on_seq lib Q B m (seq2kseq s m v) }.

Definition barind_nout_imp {o} lib Q P (B X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq_nout lib s n
    -> nout_on_seq lib Q B n s
    -> nout_on_seq lib P X n s.

Definition nout_on_upd_seq {o} lib P (X s : @CTerm o) (n : nat) (u : CTerm) (v : NVar) :=
  nout_on_seq lib P X (S n) (update_seq_nout s n u v).

Definition cnterm2cterm {o} (t : @CNTerm o) : CTerm :=
  let (x,p) := t in
  existT isprog x (isprog_nout_implies_isprog x p).

Definition cnout_cterm {o} (t : @CNTerm o) : CTerm := cnterm2cterm t.
Definition cnout_term {o} (t : @CNTerm o) : NTerm := get_cterm (cnout_cterm t).

Definition barind_nout_ind {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq_nout lib s n
    -> (forall (u : CNTerm), nout_on_upd_seq lib P X s n (cnout_cterm u) v)
    -> nout_on_seq lib P X n s.

Definition barind_nout_ind_cont {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq_nout lib s n
    -> !nout_on_seq lib P X n s
    -> {u : CNTerm , !nout_on_upd_seq lib P X s n (cnout_cterm u) v}.

Definition nout_seq_NA {o} lib P (X : @CTerm o) :=
  {n : nat
   & {s : CTerm
   & is_kseq_nout lib s n
   # !nout_on_seq lib P X n s }}.

Definition mk_nout_seq_NA {o} {lib} {P} {X : @CTerm o}
           (n : nat)
           (s : CTerm)
           (i : is_kseq_nout lib s n)
           (p : !nout_on_seq lib P X n s) : nout_seq_NA lib P X :=
  existT _ n (existT _ s (i,p)).

Definition nout_seq_NA_nat {o} {lib} {P} {X : @CTerm o} (x : nout_seq_NA lib P X) : nat :=
  projT1 x.

Definition nout_seq_NA_seq {o} {lib} {P} {X : @CTerm o} (x : nout_seq_NA lib P X) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition barind_nout_ind_cont2 {o} lib P (X : @CTerm o) v :=
  forall (x : nout_seq_NA lib P X),
    {u : CNTerm
     , !nout_on_upd_seq
        lib P X
        (nout_seq_NA_seq x)
        (nout_seq_NA_nat x)
        (cnout_cterm u)
        v}.

Definition barind_nout_ind_cont3 {o} lib P (X : @CTerm o) v :=
  {f : nout_seq_NA lib P X -> CNTerm
   , forall a : nout_seq_NA lib P X,
       !nout_on_upd_seq
          lib P X
          (nout_seq_NA_seq a)
          (nout_seq_NA_nat a)
          (cnout_cterm (f a))
          v}.

Lemma barind_nout_ind_implies_cont {o} :
  forall lib P (X : @CTerm o) v,
    barind_nout_ind lib P X v
    -> barind_nout_ind_cont lib P X v.
Proof.
  introv ind i ni.
  pose proof (ind n s i) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_nout_ind_cont_implies_cont2 {o} :
  forall lib P (X : @CTerm o) v,
    barind_nout_ind_cont lib P X v
    -> barind_nout_ind_cont2 lib P X v.
Proof.
  introv ind; introv.
  unfold nout_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_nout_ind_cont2_implies_cont3 {o} :
  forall lib P (X : @CTerm o) v,
    barind_nout_ind_cont2 lib P X v
    -> barind_nout_ind_cont3 lib P X v.
Proof.
  introv ind; introv.
  unfold barind_nout_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Lemma eq_kseq_nout_0 {o} :
  forall lib (s1 s2 : @CTerm o),
    eq_kseq_nout lib s1 s2 0.
Proof.
  introv.
  unfold eq_kseq_nout, natk2nout.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists 0%Z; spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  allrw @mkc_nat_eq; ginv; omega.
Qed.

Lemma is_kseq_nout_0 {o} : forall lib (t : @CTerm o), is_kseq_nout lib t 0.
Proof.
  introv.
  apply eq_kseq_nout_0.
Qed.

Definition nout_kseq_at_is {o} lib (s : @CTerm o) (n : nat) u :=
  cequivc lib (mkc_apply s (mkc_nat n)) u.

Definition nout_kseq_NA {o} lib P (n : nat) (A : @CTerm o) v :=
  {u : CNTerm
   & {s : CTerm
   & is_kseq_nout lib s (S n)
   # seq_normalizable lib s (S n) v
   # nout_kseq_at_is lib s n (cnout_cterm u)
   # !nout_on_seq lib P A (S n) s }}.

Definition mk_nout_kseq_NA {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (u : CNTerm)
           (s : CTerm)
           (i : is_kseq_nout lib s (S n))
           (q : seq_normalizable lib s (S n) v)
           (e : nout_kseq_at_is lib s n (cnout_cterm u))
           (p : !nout_on_seq lib P A (S n) s) : nout_kseq_NA lib P n A v :=
  existT _ u (existT _ s (i,(q,(e,p)))).

Definition nout_kseq_NA_nout {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : nout_kseq_NA lib P n A v) : CNTerm :=
  match x with
    | existT u _ => u
  end.

Definition nout_kseq_NA_cterm {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : nout_kseq_NA lib P n A v) : CTerm :=
  cnterm2cterm (nout_kseq_NA_nout x).

Definition nout_kseq_NA_seq {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : nout_kseq_NA lib P n A v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Lemma implies_equality_natk2nout {o} :
  forall lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {t1 : CTerm
           & {t2 : CTerm
           & {u : CTerm
           & computes_to_valc lib (mkc_apply f (mkc_nat m)) t1
           # computes_to_valc lib (mkc_apply g (mkc_nat m)) t2
           # cequivc lib t1 u
           # cequivc lib t2 u
           # noutokensc u }}})
    -> equality lib f g (natk2nout (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists (Z.of_nat n); spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e0]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  rw @mkc_nat_eq in e3; ginv.

  assert (m < n) as ltm by omega.
  clear e1.

  pose proof (imp m ltm) as h; exrepnd.

  apply equality_in_nout.
  exists u; dands; spcast; auto.

  { eapply cequivc_trans;[|exact h3].
    apply computes_to_valc_implies_cequivc; auto. }

  { eapply cequivc_trans;[|exact h4].
    apply computes_to_valc_implies_cequivc; auto. }
Qed.

Lemma implies_member_natk2nout {o} :
  forall lib (f : @CTerm o) n,
    (forall m,
       m < n
       -> {t : CTerm
           & {u : CTerm
           & computes_to_valc lib (mkc_apply f (mkc_nat m)) t
           # cequivc lib t u
           # noutokensc u }})
    -> member lib f (natk2nout (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nout.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists t t u; dands; auto.
Qed.

Lemma implies_equality_natk2nout2 {o} :
  forall lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {u : CTerm
           , ccequivc lib (mkc_apply f (mkc_nat m)) u
           # ccequivc lib (mkc_apply g (mkc_nat m)) u
           # noutokensc u })
    -> equality lib f g (natk2nout (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists (Z.of_nat n); spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e0]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  rw @mkc_nat_eq in e3; ginv.

  assert (m < n) as ltm by omega.
  clear e1.

  pose proof (imp m ltm) as h; exrepnd.

  apply equality_in_nout.
  exists u; dands; spcast; auto.
Qed.

Lemma implies_member_natk2nout2 {o} :
  forall lib (f : @CTerm o) n,
    (forall m,
       m < n
       -> {u : CTerm
           , ccequivc lib (mkc_apply f (mkc_nat m)) u
           # noutokensc u })
    -> member lib f (natk2nout (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nout2.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists u; dands; auto.
Qed.

Lemma equality_natk2nout_implies {o} :
  forall lib m (f g : @CTerm o) n,
    m < n
    -> equality lib f g (natk2nout (mkc_nat n))
    -> {u : CTerm
        , ccequivc lib (mkc_apply f (mkc_nat m)) u
        # ccequivc lib (mkc_apply g (mkc_nat m)) u
        # noutokensc u }.
Proof.
  introv ltm mem.
  apply equality_in_fun in mem; repnd.
  clear mem0 mem1.
  pose proof (mem (mkc_nat m) (mkc_nat m)) as h; clear mem.
  autodimp h hyp.

  { apply equality_in_natk.
    exists m (Z.of_nat n); dands; spcast; try omega;
    try (apply computes_to_valc_refl; eauto 2 with slow). }

  apply equality_in_nout in h; exrepnd; spcast.
  exists u; dands; spcast; auto.
Qed.

Lemma member_natk2nout_implies {o} :
  forall lib m (f : @CTerm o) n,
    m < n
    -> member lib f (natk2nout (mkc_nat n))
    -> {u : CTerm , ccequivc lib (mkc_apply f (mkc_nat m)) u # noutokensc u}.
Proof.
  introv ltm mem.
  eapply equality_natk2nout_implies in mem;[|exact ltm].
  exrepnd; spcast.
  exists u; dands; spcast; auto.
Qed.

Lemma noutokensc_cnterm2cterm {o} :
  forall (u : @CNTerm o), noutokensc (cnterm2cterm u).
Proof.
  introv.
  unfold noutokensc.
  destruct u; simpl.
  allrw @isprog_nout_iff; sp.
Qed.
Hint Resolve noutokensc_cnterm2cterm : slow.

Lemma eq_kseq_nout_update {o} :
  forall lib (s1 s2 : @CTerm o) (n : nat) (u : CNTerm) (v : NVar),
    eq_kseq_nout lib s1 s2 n
    -> eq_kseq_nout
         lib
         (update_seq_nout s1 n (cnout_cterm u) v)
         (update_seq_nout s2 n (cnout_cterm u) v)
         (S n).
Proof.
  introv i.
  allunfold @eq_kseq_nout.
  unfold update_seq.
  apply implies_equality_natk2nout2.
  introv ltm.

  destruct (deq_nat m n) as [d|d]; subst.

  - exists (cnterm2cterm u).
    dands; eauto 3 with slow; tcsp; spcast;[|].

    + eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

    + eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

  - pose proof (equality_natk2nout_implies lib m s1 s2 n) as h.
    repeat (autodimp h hyp); try omega;[].
    exrepnd; spcast.
    exists u0.
    dands; spcast; auto.

    + eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.

    + eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.
Qed.

Lemma is_kseq_nout_update {o} :
  forall lib (s : @CTerm o) (n : nat) (u : CNTerm) (v : NVar),
    is_kseq_nout lib s n
    -> is_kseq_nout lib (update_seq_nout s n (cnout_cterm u) v) (S n).
Proof.
  introv i.
  apply eq_kseq_nout_update; auto.
Qed.

Lemma seq_normalizable_update_nout {o} :
  forall lib (s : @CTerm o) (n : nat) (u : CTerm) (v : NVar),
    seq_normalizable lib s n v
    -> seq_normalizable lib (update_seq_nout s n u v) (S n) v.
Proof.
  introv norm.
  allunfold @seq_normalizable.

  unfold update_seq, seq2kseq.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_inteq_substc.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [|apply cequivc_mkc_less;
       [apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_mkc_less;
         [apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_sym;apply cequivc_beta
         |apply cequivc_refl]
       ]
    ].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply implies_cequivc_apply;
        [exact norm|apply cequivc_refl]
      ]
    |].
  unfold seq2kseq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_beta]
    |].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [allrw @mkc_zero_eq; apply cequivc_inteq_less_swap1; try omega|].
  allrw <- @mkc_zero_eq.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_less_int|].
  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; tcsp.
  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply computes_to_valc_implies_cequivc; exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_less;
        [apply computes_to_valc_implies_cequivc; exact compu
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      ]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
       [apply computes_to_valc_implies_cequivc; exact compu
       |apply cequivc_refl
       |apply cequivc_mkc_inteq;
         [apply computes_to_valc_implies_cequivc; exact compu
         |apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_refl]
       |apply cequivc_refl
       ]
    ].

  eapply cequivc_trans;
    [apply cequivc_inteq_less_swap1; try omega|].

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat]
    |].

  eapply cequivc_trans;
    [apply cequivc_mkc_less_nat|].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat
      |apply cequivc_refl]
    ].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; subst; tcsp; try omega.
Qed.

Lemma nout_kseq_at_is_update {o} :
  forall lib (s : @CTerm o) (n : nat) (u : CTerm) (v : NVar),
    nout_kseq_at_is lib (update_seq_nout s n u v) n u.
Proof.
  introv.
  unfold nout_kseq_at_is, update_seq_nout.
  eapply cequivc_trans;[apply cequivc_beta|].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; tcsp; GC.
Qed.

Fixpoint nout_alpha {o}
         (lib : library)
         P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !nout_on_seq lib P X 0 c)
         (f : nout_seq_NA lib P X -> CNTerm)
         (ind : forall a : nout_seq_NA lib P X,
                  !nout_on_upd_seq
                     lib P X
                     (nout_seq_NA_seq a)
                     (nout_seq_NA_nat a)
                     (cnout_cterm (f a))
                     v)
         (n : nat) : nout_kseq_NA lib P n X v :=
  match n with
    | 0 =>
      let i := is_kseq_nout_0 lib c in
      let p := mk_nout_seq_NA 0 c i h in
      let k := f p in
      mk_nout_kseq_NA
        k
        (update_seq_nout c 0 (cnout_cterm k) v)
        (is_kseq_nout_update lib c 0 k v i)
        (seq_normalizable_update_nout lib c 0 (cnout_cterm k) v q)
        (nout_kseq_at_is_update lib c 0 (cnout_cterm k) v)
        (ind p)
    | S m =>
      let (_,r) := nout_alpha lib P X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (e,na) := r in
      let p := mk_nout_seq_NA (S m) s i na in
      let k := f p in
      mk_nout_kseq_NA
        k
        (update_seq_nout s (S m) (cnout_cterm k) v)
        (is_kseq_nout_update lib s (S m) k v i)
        (seq_normalizable_update_nout lib s (S m) (cnout_cterm k) v z)
        (nout_kseq_at_is_update lib s (S m) (cnout_cterm k) v)
        (ind p)
  end.

Definition ntseqc2ntseq {o} (f : @ntseqc o) : CTerm :=
  exist isprog (sterm (ntseqc2seq f)) (isprog_ntseqc f).

Lemma noutokensc_nout_kseq_NA_cterm :
  forall {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
         (x : nout_kseq_NA lib P n A v),
    noutokensc (nout_kseq_NA_cterm x).
Proof.
  introv.
  unfold nout_kseq_NA_cterm; eauto 3 with slow.
Qed.
Hint Resolve noutokensc_nout_kseq_NA_cterm : slow.

Lemma cequivc_beta_ntseqc2ntseq {o} :
  forall (lib : @library o) s n,
    cequivc
      lib
      (mkc_apply (ntseqc2ntseq s) (mkc_nat n))
      (cnterm2cterm (s n)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv;
    [apply isprogram_apply;
      eauto 3 with slow;
      apply nt_wf_sterm_implies_isprogram;
      apply nt_wf_sterm_iff;
      introv; simpl; unfold ntseqc2seq;
      remember (s n0) as t; destruct t; simpl; clear Heqt;
     allrw @isprog_nout_iff; sp
    |].
  eapply reduces_to_if_split2;[csunf;simpl;auto|].
  apply reduces_to_if_step; csunf; simpl.
  unfold compute_step_eapply; simpl.
  boolvar; try omega.
  rw Znat.Nat2Z.id; auto.
  unfold ntseqc2seq, get_cnterm, cnterm2cterm, get_cterm; simpl.
  remember (s n) as t; destruct t; simpl; auto.
Qed.

Lemma is_kseq_nout_implies {o} :
  forall lib m (s : @CTerm o) n,
    m < n
    -> is_kseq_nout lib s n
    -> {u : CTerm , ccequivc lib (mkc_apply s (mkc_nat m)) u # noutokensc u}.
Proof.
  introv ltm i.
  unfold is_kseq_nout in i.
  eapply member_natk2nout_implies in i;[|exact ltm]; auto.
Qed.

Lemma nout_kseq_NA_seq_mk_nout_kseq_NA {o} :
  forall lib P n (A : @CTerm o) v m s i q e p,
    nout_kseq_NA_seq (@mk_nout_kseq_NA o lib P n A v m s i q e p) = s.
Proof. sp. Qed.

Lemma nout_alpha_prop1 {o} :
  forall lib P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !nout_on_seq lib P X 0 c)
         (f : nout_seq_NA lib P X -> CNTerm)
         (ind : forall a : nout_seq_NA lib P X,
                  !nout_on_upd_seq
                     lib P X
                     (nout_seq_NA_seq a)
                     (nout_seq_NA_nat a)
                     (cnterm2cterm (f a))
                     v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (nout_kseq_NA_seq (nout_alpha lib P X c v q h f ind n))
      (nout_kseq_NA_seq (nout_alpha lib P X c v q h f ind m))
      (natk2nout (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nout2; introv ltm0.

  - remember (nout_alpha lib P X c v q h f ind m) as am.
    unfold nout_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_nout_implies lib m0) in i; try omega; exrepnd.
    exists u0; dands; auto.

  - remember (nout_alpha lib P X c v q h f ind (k + m)) as am.
    unfold nout_kseq_NA in am; exrepnd; simphyps.
    rw @nout_kseq_NA_seq_mk_nout_kseq_NA.

    eapply equality_natk2nout_implies in IHk;[|exact ltm0].
    exrepnd.
    exists u0; dands; auto.

    unfold update_seq_nout; spcast.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
Qed.

Lemma member_ntseqc2ntseq_nat2nout {o} :
  forall (lib : @library o) (s : ntseqc),
    member lib (ntseqc2ntseq s) nat2nout.
Proof.
  introv.
  unfold nat2nout.
  apply equality_in_fun; dands; tcsp; eauto 3 with slow.
  introv eqn.
  applydup @equality_int_nat_implies_cequivc in eqn.
  apply equality_respects_cequivc.
  { apply implies_cequivc_apply; auto. }
  clear eqn0.
  apply equality_refl in eqn.
  apply member_tnat_iff in eqn; exrepnd.

  eapply member_respects_cequivc.
  { apply cequivc_sym.
    apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact eqn0]. }

  apply (member_respects_cequivc _ (cnterm2cterm (s k))).
  { apply cequivc_sym.
    apply reduces_toc_implies_cequivc.
    unfold reduces_toc; simpl.
    eapply reduces_to_if_split2.
    { csunf; simpl; auto. }
    apply reduces_to_if_step.
    csunf; simpl.
    unfold compute_step_eapply; simpl.
    boolvar; try omega.
    allrw @Znat.Nat2Z.id; auto.
    unfold ntseqc2seq, get_cnterm, cnterm2cterm, get_cterm; simpl.
    remember (s k) as t; destruct t; simpl; auto.
  }

  remember (s k) as t; clear Heqt.
  clear eqn0.

  apply equality_in_nout.
  exists (cnterm2cterm t); dands; spcast; eauto 3 with slow.
Qed.

Lemma is_seq_nout_ntseqc2ntseq {o} :
  forall (lib : @library o) s, is_seq_nout lib (ntseqc2ntseq s).
Proof.
  introv.
  unfold is_seq_nout.
  apply member_ntseqc2ntseq_nat2nout.
Qed.
Hint Resolve is_seq_nout_ntseqc2ntseq : slow.

Lemma eq_kseq_nout_seq2kseq_0 {o} :
  forall lib v (s1 s2 : @CTerm o),
    eq_kseq_nout lib (seq2kseq s1 0 v) (seq2kseq s2 0 v) 0.
Proof.
  introv.
  apply implies_equality_natk2nout.
  introv ltm; omega.
Qed.

Lemma seq2kseq_prop1_nout {o} :
  forall lib (s1 s2 : @CTerm o) n v,
    eq_kseq_nout lib s1 s2 n
    -> eq_kseq_nout lib (seq2kseq s1 n v) (seq2kseq s2 n v) n.
Proof.
  introv equ.
  apply implies_equality_natk2nout2.
  introv ltm.
  apply (equality_natk2nout_implies _ m) in equ; auto; exrepnd; spcast.
  exists u.
  dands; spcast; auto.

  - unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega; auto.

  - unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega; auto.
Qed.

Lemma implies_is_kseq_nout_seq2kseq {o} :
  forall lib (s : @CTerm o) m v,
    is_kseq_nout lib s m
    -> is_kseq_nout lib (seq2kseq s m v) m.
Proof.
  introv i.
  apply seq2kseq_prop1_nout; auto.
Qed.

Lemma equality_nat2nout_to_natk2nout {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_tnat
    -> equality lib f g nat2nout
    -> equality lib f g (natk2nout n).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { apply type_mkc_natk.
    exists (Z.of_nat k); spcast; auto. }

  introv en.
  apply equality_natk_to_tnat in en; apply e in en; auto.
Qed.

Lemma is_kseq_nout_ntseqc2ntseq {o} :
  forall (lib : @library o) s n, is_kseq_nout lib (ntseqc2ntseq s) n.
Proof.
  introv.
  pose proof (is_seq_nout_ntseqc2ntseq lib s) as h.
  apply equality_nat2nout_to_natk2nout; auto.
  apply nat_in_nat.
Qed.
Hint Resolve is_kseq_nout_ntseqc2ntseq : slow.

Lemma seq2kseq_prop2_nout {o} :
  forall lib v (s1 s2 : @CTerm o) n,
    eq_kseq_nout lib s1 s2 n
    -> cequivc lib (seq2kseq s1 n v) (seq2kseq s2 n v).
Proof.
  introv equ.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw (@mkc_nat_eq o 0).

  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; auto.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; auto.

  eapply cequivc_trans;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    ].

  apply (equality_natk2nout_implies _ n0) in equ; auto.
  apply cequiv_stable; exrepnd; spcast.
  eapply cequivc_trans;
    [exact equ1
    |apply cequivc_sym;exact equ2].
Qed.

Lemma cequivc_preserves_eq_kseq_nout_left {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq_nout lib s1 s n
    -> eq_kseq_nout lib s2 s n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq_nout.
  eapply equality_respects_cequivc_left;[|exact ek]; auto.
Qed.

Lemma cequivc_preserves_eq_kseq_nout_right {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq_nout lib s s1 n
    -> eq_kseq_nout lib s s2 n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq_nout.
  eapply equality_respects_cequivc_right;[|exact ek]; auto.
Qed.

Lemma cequivc_preserves_nout_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> nout_on_seq lib P A n s1
    -> nout_on_seq lib P A n s2.
Proof.
  introv ceq m.
  allunfold @nout_on_seq; repnd.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_nout_left;[|exact ek]; auto.
    apply cequivc_sym; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_nout_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> !nout_on_seq lib P A n s1
    -> !nout_on_seq lib P A n s2.
Proof.
  introv ceq h m.
  allunfold @nout_on_seq; repnd.
  destruct h.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_nout_left;[|exact ek]; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma bar_induction_cterm_meta {o} :
  forall lib Q P (B X c : @CTerm o) v,
    barind_nout_bar lib Q B v
    -> barind_nout_imp lib Q P B X
    -> barind_nout_ind lib P X v
    -> nout_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (nout_on_seq lib P X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_nout_ind_implies_cont in ind.
  apply barind_nout_ind_cont_implies_cont2 in ind.
  apply barind_nout_ind_cont2_implies_cont3 in ind.
  unfold barind_nout_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c 0 v) as nc.
  clear Heqnc.

  remember (nout_alpha lib P X (seq2kseq c 0 v) v nc ni f ind) as g.
  remember (fun m => nout_kseq_NA_nout (g m)) as s.

  assert (forall n, eq_kseq_nout lib (ntseqc2ntseq s) (nout_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nout2; introv ltm.
    subst.
    exists (nout_kseq_NA_cterm (nout_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m)).
    dands; spcast; eauto 3 with slow.

    - eapply cequivc_trans;[apply cequivc_beta_ntseqc2ntseq|].
      simpl; auto.

    - pose proof (nout_alpha_prop1 lib P X (seq2kseq c 0 v) v nc ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nout_implies lib m) in q; try omega.
      apply cequiv_stable; exrepnd; spcast.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q2].
      clear q2.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (nout_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
      unfold nout_kseq_NA in am; exrepnd; simphyps.
      rw @nout_kseq_NA_seq_mk_nout_kseq_NA.
      unfold update_seq_nout.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (ntseqc2ntseq s)) as b.
  autodimp b hyp; eauto 3 with slow.

  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_nout_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_nout_0 lib (ntseqc2ntseq s) c) as h1.
    apply (seq2kseq_prop2_nout _ v) in h1.
    eapply cequivc_preserves_nout_on_seq in b;[|exact h1]; auto. }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2_nout _ v) in q1.

  eapply cequivc_preserves_nout_on_seq in b;[|exact q1].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2_nout _ v) in q2.

  eapply cequivc_preserves_not_nout_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (nout_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
  unfold nout_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_nout_seq_NA (S m) s am0 am1)) as fn.

  assert (eq_kseq_nout lib (update_seq_nout s (S m) (cnterm2cterm fn) v) s (S m)) as ee1.
  { unfold eq_kseq_nout.
    apply implies_equality_natk2nout2; introv ltm1.
    dup am0 as e.
    eapply member_natk2nout_implies in e;[|exact ltm1]; exrepnd; spcast.
    exists u0; dands; spcast; auto;[].
    unfold update_seq_nout.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
  }

  apply (seq2kseq_prop2_nout _ v) in ee1.
  eapply cequivc_preserves_nout_on_seq in b;[|exact ee1].
  clear ee1.

  unfold seq_normalizable in am2.
  eapply cequivc_preserves_nout_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
