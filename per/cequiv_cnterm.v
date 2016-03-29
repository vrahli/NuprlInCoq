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


Require Export cnterm.
Require Export per_props_nat.
Require Export seq_util.


Definition cnterm2cterm {o} (t : @CNTerm o) : CTerm :=
  let (x,p) := t in
  existT isprog x (isprog_nout_implies_isprog x p).

Definition cnout_cterm {o} (t : @CNTerm o) : CTerm := cnterm2cterm t.
Definition cnout_term {o} (t : @CNTerm o) : NTerm := get_cterm (cnout_cterm t).

Lemma noutokensc_cnterm2cterm {o} :
  forall (u : @CNTerm o), noutokensc (cnterm2cterm u).
Proof.
  introv.
  unfold noutokensc.
  destruct u; simpl.
  allrw @isprog_nout_iff; sp.
Qed.
Hint Resolve noutokensc_cnterm2cterm : slow.

Definition ntseqc2ntseq {o} (f : @ntseqc o) : CTerm :=
  exist isprog (sterm (ntseqc2seq f)) (isprog_ntseqc f).

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

Definition is_seq_nout {o} lib (s : @CTerm o) := member lib s nat2nout.

Lemma is_seq_nout_ntseqc2ntseq {o} :
  forall (lib : @library o) s, is_seq_nout lib (ntseqc2ntseq s).
Proof.
  introv.
  unfold is_seq_nout.
  apply member_ntseqc2ntseq_nat2nout.
Qed.
Hint Resolve is_seq_nout_ntseqc2ntseq : slow.

Definition mkcv_nout {o} vs : @CVTerm o vs := mk_cv vs mkc_nout.

Lemma mkcv_nout_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_nout [v])
    = mkc_nout.
Proof.
  introv.
  unfold mkcv_nout.
  allrw @csubst_mk_cv; auto.
Qed.

Lemma isprog_implies_isprog_nout {o} :
  forall (t : @NTerm o),
    noutokens t -> isprog t -> isprog_nout t.
Proof.
  introv nout isp.
  apply isprog_nout_iff.
  applydup @isprog_implies_wf in isp.
  apply closed_if_isprog in isp.
  allrw @nt_wf_eq; sp.
Qed.

Definition cterm2cnterm {o} (t : @CTerm o) : noutokensc t -> CNTerm :=
  match t with
    | exist x p => fun n => existT isprog_nout x (isprog_implies_isprog_nout x n p)
  end.

Lemma cnterm2cterm2cnterm {o} :
  forall (t : @CTerm o) (p : noutokensc t),
    (cnterm2cterm (cterm2cnterm t p)) = t.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl; auto.
Qed.
Hint Rewrite @cnterm2cterm2cnterm : slow.

Lemma equality_nat2nout_apply {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2nout
    -> equality lib a b mkc_tnat
    -> equality lib (mkc_apply f a) (mkc_apply g b) mkc_nout.
Proof.
  introv eqf eqn.
  unfold nat2nat in eqf.
  apply equality_in_fun in eqf; repnd.
  apply eqf in eqn; auto.
Qed.

Definition eq_kseq_nout {o} lib (s1 s2 : @CTerm o) (n : nat) :=
  equality lib s1 s2 (natk2nout (mkc_nat n)).

Definition is_kseq_nout {o} lib (s : @CTerm o) (n : nat) := eq_kseq_nout lib s s n.

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

Lemma eq_kseq_nout_of_seq {o} :
  forall lib (s : @CTerm o) v k,
    is_seq_nout lib s
    -> eq_kseq_nout lib s (seq2kseq s k v) k.
Proof.
  introv iss.
  unfold eq_kseq_nout.
  apply implies_equality_natk2nout2.
  introv l.
  unfold is_seq_nout in iss.

  assert (equality lib (mkc_nat m) (mkc_nat m) mkc_tnat) as equ by (eauto with slow).

  eapply equality_nat2nout_apply in iss;[|eauto].
  allrw @member_eq.
  apply equality_in_nout in iss; exrepnd; spcast; GC.
  exists u; dands; spcast; auto.
  unfold seq2kseq.

  eapply cequivc_trans;[apply cequivc_beta|].
  repeat (rewrite mkcv_less_substc).
  repeat (rewrite mkcv_apply_substc).
  repeat (rewrite mkcv_bot_substc).
  repeat (rewrite mkcv_nat_substc).
  repeat (rewrite mkcv_zero_substc).
  repeat (rewrite mkc_var_substc).
  repeat (rewrite csubst_mk_cv).
  rewrite mkc_zero_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  boolvar; try omega.
  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  boolvar; try omega.
  auto.
Qed.
Hint Resolve eq_kseq_nout_of_seq : slow.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../close/" "../cequiv/")
*** End:
*)
