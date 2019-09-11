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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms5.
Require Export computation7.
Require Export computation_exc.


Definition isccan {o} (t : @NTerm o) :=
  match t with
    | oterm (Can _) _ => True
    | _ => False
  end.

Definition isccanc {o} (t : @CTerm o) := isccan (get_cterm t).


Lemma dec_ex_reduces_in_atmost_k_steps_exc {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm & reduces_in_atmost_k_steps_exc lib t v k}.
Proof.
  introv.
  remember (compute_at_most_k_steps_exc lib k t) as c; symmetry in Heqc.
  destruct c.
  - left.
    exists n; auto.
  - right; intro r; exrepnd; rw r0 in Heqc; ginv.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_excc {o} :
  forall lib k (t : @CTerm o),
    decidable {v : CTerm & reduces_in_atmost_k_steps_excc lib t v k}.
Proof.
  introv.
  destruct_cterms.
  unfold reduces_in_atmost_k_steps_excc; simpl.
  pose proof (dec_ex_reduces_in_atmost_k_steps_exc lib k x) as h.
  destruct h as [h|h];[left|right].
  - exrepnd.
    applydup @reduces_in_atmost_k_steps_preserves_isprog in h0; auto.
    exists (mk_ct v h1); simpl; auto.
  - intro q; exrepnd.
    destruct h.
    destruct_cterms; allsimpl.
    exists x0; auto.
Qed.

Lemma dec_iscan {o} :
  forall (t : @NTerm o), decidable (iscan t).
Proof.
  introv.
  destruct t as [v|op bs]; simpl; tcsp; try (complete (right; sp)).
  dopid op as [can|ncan|exc|abs] Case; tcsp; try (complete (right; sp)).
Qed.

Lemma dec_iscanc {o} :
  forall (t : @CTerm o), decidable (iscanc t).
Proof.
  introv.
  destruct_cterms.
  unfold iscanc; simpl.
  apply dec_iscan.
Qed.

Definition noconst  {o} (t : @NTerm o) := assert (no_const t).
Definition noconstb {o} (b : @BTerm o) := assert (no_const_b b).
Definition noconsto {o} (op : @Opid o) := assert (no_const_o op).

Definition noseq  {o} (t : @NTerm o) := assert (no_seq t).
Definition noseqb {o} (b : @BTerm o) := assert (no_seq_b b).
Definition noseqo {o} (op : @Opid o) := assert (no_seq_o op).

Definition no_constc {o} (t : @CTerm o) := no_const (get_cterm t).
Definition noconstc  {o} (t : @CTerm o) := assert (no_constc t).

Definition no_seqc   {o} (t : @CTerm o) := no_seq (get_cterm t).
Definition noseqc    {o} (t : @CTerm o) := assert (no_seqc t).

Lemma decidable_eq_bool :
  forall (a b : bool),
    decidable (a = b).
Proof.
  introv.
  destruct a, b; tcsp; right; intro xx; ginv.
Qed.

Lemma decidable_noseqc {o} :
  forall (t : @CTerm o),
    decidable (noseqc t).
Proof.
  introv.
  destruct_cterms.
  unfold noseqc; simpl.
  apply decidable_eq_bool.
Qed.

Lemma decidable_noconstc {o} :
  forall (t : @CTerm o),
    decidable (noconstc t).
Proof.
  introv.
  destruct_cterms.
  unfold noconstc; simpl.
  apply decidable_eq_bool.
Qed.

Lemma noconstb_bterm {o} :
  forall l (t : @NTerm o),
    noconstb (bterm l t) <=> noconst t.
Proof.
  introv; sp.
Qed.

Lemma noconst_oterm {o} :
  forall op (bs : list (@BTerm o)),
    noconst (oterm op bs)
    <=> (noconsto op # forall b, LIn b bs -> noconstb b).
Proof.
  introv; unfold noconst; simpl.
  rw @assert_of_andb.
  rw @assert_ball_map; sp.
Qed.

Lemma noseq_oterm {o} :
  forall op (bs : list (@BTerm o)),
    noseq (oterm op bs)
    <=> (noseqo op # forall b, LIn b bs -> noseqb b).
Proof.
  introv; unfold noseq; simpl.
  rw @assert_of_andb.
  rw @assert_ball_map; sp.
Qed.

Lemma noseqb_bterm {o} :
  forall l (t : @NTerm o),
    noseqb (bterm l t) <=> noseq t.
Proof.
  introv; sp.
Qed.

Lemma decidable_eq_list :
  forall T (l1 l2 : list T),
    (forall a b, LIn (a,b) (combine l1 l2) -> decidable (a = b))
    -> decidable (l1 = l2).
Proof.
  induction l1; destruct l2; introv imp; allsimpl; tcsp;
  try (complete (right; intro xx; ginv; tcsp)).
  pose proof (imp a t) as q; autodimp q hyp.
  destruct q as [q|q]; subst;
  try (complete (right; intro xx; ginv; tcsp)).
  pose proof (IHl1 l2) as h; clear IHl1; autodimp h hyp.
  destruct h as [h|h]; subst; tcsp;
  try (complete (right; intro xx; ginv; tcsp)).
Qed.

Lemma dec_eq_terms {o} :
  forall (a b : @NTerm o),
    noconst a
    -> noseq a
    -> decidable (a = b).
Proof.
  nterm_ind a as [v1|op1 bs1 imp] Case; introv noc nos;
  destruct b as [v2|op2 bs2];
  try (complete (right; intro xx; ginv; tcsp)).

  - Case "vterm".
    destruct (deq_nvar v1 v2); subst; tcsp.
    right; intro xx; ginv; tcsp.

  - Case "oterm".
    allrw @noconst_oterm; repnd.
    allrw @noseq_oterm; repnd.
    destruct (opid_dec_no_const op1 op2) as [d|d]; auto; subst;
    try (complete (right; intro xx; ginv; tcsp));[].

    assert (decidable (bs1 = bs2)) as dbs.
    { apply decidable_eq_list.
      introv i.
      destruct a as [l1 t1].
      destruct b as [l2 t2].
      applydup in_combine in i; repnd.
      applydup noc in i1.
      allrw @noconstb_bterm.
      applydup nos in i1.
      allrw @noseqb_bterm.
      pose proof (imp t1 l1) as h; autodimp h hyp; clear imp.
      pose proof (h t2) as ih; clear h; repeat (autodimp ih hyp).
      destruct ih as [ih|ih]; auto; subst;
      try (complete (right; intro xx; ginv; tcsp));[].

      assert (decidable (l1 = l2)) as dl.
      { apply decidable_eq_list.
        introv j.
        destruct (deq_nvar a b); subst; tcsp. }

      destruct dl as [dl|dl]; subst; tcsp;
      try (complete (right; intro xx; ginv; tcsp)).
    }

    destruct dbs as [d|d]; subst; tcsp;
    try (complete (right; intro xx; ginv; tcsp)).
Qed.

Lemma dec_eq_cterms {o} :
  forall (a b : @CTerm o),
    noconstc a
    -> noseqc a
    -> decidable (a = b).
Proof.
  introv nc ns; destruct_cterms.
  unfold noconstc, no_constc in nc; allsimpl.
  unfold noseqc, no_seqc in ns; allsimpl.
  destruct (dec_eq_terms x0 x nc) as [d|d]; subst; tcsp; clear_irr; tcsp.
  right; intro xx.
  inversion xx; subst; tcsp.
Qed.
