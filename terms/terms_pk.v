(*

  Copyright 2014 Cornell University

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

Require Export terms2.



(* !!MOVE *)
Hint Resolve isvalue_mk_nat : slow.
Hint Resolve isprogram_implies : slow.
Hint Resolve isprog_implies : slow.
Hint Resolve isvalue_inl : slow.
Hint Resolve isvalue_inr : slow.
Hint Resolve iscvalue_mkc_inl : slow.
Hint Resolve iscvalue_mkc_inr : slow.
Hint Resolve isprog_mk_nat : slow.


Inductive param_kind {o} :=
| PKs : String.string -> param_kind
| PKa : get_patom_set o -> param_kind
| PKi : Z -> param_kind.

Definition get_param_from_cop {o} (c: @CanonicalOp o) : option (@param_kind o) :=
  match c with
    | NTok s  => Some (PKs s)
    | NUTok a => Some (PKa a)
    | Nint z  => Some (PKi z)
    | _       => None
  end.

Lemma param_kind_deq {o} : Deq (@param_kind o).
Proof.
  introv.
  destruct x, y;
    try (complete (destruct (String.string_dec s s0); subst; tcsp; right; intro h; ginv; tcsp));
    try (complete (destruct (Z.eq_dec z z0); subst; tcsp; right; intro h; ginv; tcsp));
    try (complete (destruct (get_patom_deq o g g0); subst; tcsp; right; intro h; ginv; tcsp));
    try (complete (right; introv h; ginv)).
Qed.

Lemma get_param_from_cop_pks {o} :
  forall (c : @CanonicalOp o) s,
    get_param_from_cop c = Some (PKs s)
    -> c = NTok s.
Proof.
  introv e; destruct c; allsimpl; ginv; auto.
Qed.

Lemma get_param_from_cop_pka {o} :
  forall (c : @CanonicalOp o) a,
    get_param_from_cop c = Some (PKa a)
    -> c = NUTok a.
Proof.
  introv e; destruct c; allsimpl; ginv; auto.
Qed.

Lemma get_param_from_cop_pki {o} :
  forall (c : @CanonicalOp o) z,
    get_param_from_cop c = Some (PKi z)
    -> c = Nint z.
Proof.
  introv e; destruct c; allsimpl; ginv; auto.
Qed.

Definition pk2term {o} (pk : @param_kind o) : NTerm :=
  match pk with
    | PKi i => mk_integer i
    | PKs s => mk_token s
    | PKa a => mk_utoken a
  end.

Definition pk2can {o} (pk : @param_kind o) : CanonicalOp :=
  match pk with
    | PKi i => Nint i
    | PKs s => NTok s
    | PKa a => NUTok a
  end.

Lemma pk2term_eq {o} :
  forall (pk : @param_kind o), pk2term pk = oterm (Can (pk2can pk)) [].
Proof.
  introv.
  destruct pk; simpl; auto.
Qed.

Lemma pk2term_utoken {o} :
  forall (pk : @param_kind o) a,
    pk2term pk = mk_utoken a
    -> pk = PKa a.
Proof.
  introv e.
  destruct pk; allsimpl; ginv; auto.
Qed.

Lemma isvalue_integer {o} :
  forall z, @isvalue o (mk_integer z).
Proof.
  introv; repeat constructor; simpl; sp.
Qed.
Hint Resolve isvalue_integer : slow.

Lemma isvalue_token {o} :
  forall s, @isvalue o (mk_token s).
Proof.
  introv; repeat constructor; simpl; sp.
Qed.
Hint Resolve isvalue_token : slow.

Lemma isvalue_utoken {o} :
  forall s, @isvalue o (mk_utoken s).
Proof.
  introv; repeat constructor; simpl; sp.
Qed.
Hint Resolve isvalue_utoken : slow.

Lemma isvalue_pk2term {o} :
  forall (pk : @param_kind o), isvalue (pk2term pk).
Proof.
  introv; destruct pk; allsimpl; eauto with slow.
Qed.
Hint Resolve isvalue_pk2term : slow.

Definition ispk {o} (t : @NTerm o) := {pk : param_kind & t = pk2term pk}.

Definition isinteger {o} (t : @NTerm o) := {z : Z & t = mk_integer z}.

Definition iswfpk {o} c (t : @NTerm o) :=
  match c with
    | CompOpLess => isinteger t
    | CompOpEq => ispk t
  end.

Lemma isprogram_utoken {o} :
  forall a : get_patom_set o, isprogram (mk_utoken a).
Proof.
  introv.
  repeat constructor; simpl; sp.
Qed.
Hint Resolve isprogram_utoken : slow.

Lemma isinteger_integer {o} :
  forall i, @isinteger o (mk_integer i).
Proof.
  introv; exists i; auto.
Qed.
Hint Resolve isinteger_integer : slow.

Lemma isprogram_token {o} :
  forall s, @isprogram o (mk_token s).
Proof.
  introv.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isprogram_token : slow.

Lemma isprogram_pk2term {o} :
  forall (pk : @param_kind o),
    isprogram (pk2term pk).
Proof.
  introv.
  destruct pk; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve isprogram_pk2term : slow extens.

Lemma ispk_pk2term {o} :
  forall (pk : @param_kind o), ispk (pk2term pk).
Proof.
  introv.
  exists pk; auto.
Qed.
Hint Resolve ispk_pk2term : slow.

Lemma isprogram_pk2can {o} :
  forall (pk : @param_kind o) bs,
    isprogram (oterm (Can (pk2can pk)) bs)
              <=> bs = [].
Proof.
  introv.
  rw @isprogram_ot_iff.
  destruct pk; allsimpl; split; intro k; repnd; destruct bs; allsimpl; ginv; tcsp.
Qed.

Lemma isprog_pk2term {o} :
  forall (pk : @param_kind o), isprog (pk2term pk).
Proof.
  introv; destruct pk; simpl; eauto 3 with slow.
Qed.
Hint Resolve isprog_pk2term : slow.

Definition pk2termc {o} (pk : @param_kind o) : CTerm :=
  exist isprog (pk2term pk) (isprog_pk2term pk).

Lemma mkc_utoken_eq_pk2termc {o} :
  forall (a : get_patom_set o),
    mkc_utoken a = pk2termc (PKa a).
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_token_eq_pk2termc {o} :
  forall (s : String.string),
    @mkc_token o s = pk2termc (PKs s).
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_integer_eq_pk2termc {o} :
  forall (i : Z),
    @mkc_integer o i = pk2termc (PKi i).
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

Lemma ispk_integer {o} :
  forall z, ispk (@mk_integer o z).
Proof.
  introv; exists (@PKi o z); simpl; auto.
Qed.
Hint Resolve ispk_integer : slow.

Lemma iswfpk_integer {o} :
  forall (c : ComparisonOp) (z : Z),
    iswfpk c (@mk_integer o z).
Proof.
  introv; unfold iswfpk.
  destruct c; eauto 3 with slow.
Qed.
Hint Resolve iswfpk_integer : slow.

Lemma isinteger_implies_ispk {o} :
  forall (t : @NTerm o), isinteger t -> ispk t.
Proof.
  introv i.
  unfold isinteger in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve isinteger_implies_ispk : slow.

Lemma iswfpk_implies_ispk {o} :
  forall c (t : @NTerm o), iswfpk c t -> ispk t.
Proof.
  introv i.
  unfold iswfpk in i; destruct c; eauto 3 with slow.
Qed.
Hint Resolve iswfpk_implies_ispk : slow.

Lemma ispk_token {o} :
  forall s, ispk (@mk_token o s).
Proof.
  introv.
  exists (@PKs o s); simpl; auto.
Qed.
Hint Resolve ispk_token : slow.

Lemma ispk_utoken {o} :
  forall a, ispk (@mk_utoken o a).
Proof.
  introv.
  exists (@PKa o a); simpl; auto.
Qed.
Hint Resolve ispk_utoken : slow.

Lemma iswfpk_pk2term {o} :
  forall (pk : @param_kind o),
    iswfpk CompOpEq (pk2term pk).
Proof.
  introv; destruct pk; simpl; eauto 3 with slow.
Qed.
Hint Resolve iswfpk_pk2term : slow.

Lemma isinteger_implies_isvalue {o} :
  forall (t : @NTerm o), isinteger t -> isvalue t.
Proof.
  introv i.
  unfold isinteger in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve isinteger_implies_isvalue : slow.

Lemma ispk_implies_isvalue {o} :
  forall (t : @NTerm o), ispk t -> isvalue t.
Proof.
  introv i.
  unfold ispk in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve ispk_implies_isvalue : slow.

Lemma iswfpk_implies_isvalue {o} :
  forall c (t : @NTerm o),
    iswfpk c t -> isvalue t.
Proof.
  introv isw.
  unfold iswfpk in isw; destruct c; eauto 3 with slow.
Qed.
Hint Resolve iswfpk_implies_isvalue : slow.

Lemma isvalue_implies_iscan {p} :
  forall v, @isvalue p v -> iscan v.
Proof.
  introv isv.
  destruct v; try (complete (inversion isv; subst; allsimpl; tcsp)).
Qed.
Hint Resolve isvalue_implies_iscan.

Lemma get_param_from_cop_pk2can {o} :
  forall pk : @param_kind o,
    get_param_from_cop (pk2can pk) = Some pk.
Proof.
  introv.
  destruct pk; simpl; auto.
Qed.

Lemma get_param_from_cop_some {o} :
  forall (c : @CanonicalOp o) pk,
    get_param_from_cop c = Some pk <=> c = pk2can pk.
Proof.
  introv.
  split; introv e; subst; try (apply get_param_from_cop_pk2can).
  destruct c; allsimpl; ginv; auto.
Qed.

Lemma ispk_implies_isvalue_like {o} :
  forall (t : @NTerm o), ispk t -> isvalue_like t.
Proof.
  introv i.
  unfold ispk in i; exrepnd; subst.
  eauto 3 with slow.
Qed.
Hint Resolve ispk_implies_isvalue_like : slow.

Definition iscan_op {o} (op : @Opid o) : Type :=
  {c : CanonicalOp & op = Can c}.

Definition isexc_op {o} (op : @Opid o) := op = Exc.

Definition iscan_like_op {o} (op : @Opid o) :=
  iscan_op op [+] isexc_op op.

Lemma isvalue_like_implies1 {o} :
  forall (t : @NTerm o),
    isvalue_like t
    -> {op : Opid
        & {bterms : list BTerm
        & t = oterm op bterms
        # iscan_like_op op}}
       [+] {f : ntseq & t = sterm f}.
Proof.
  introv isv.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst.
    + left.
      eexists; eexists; dands; eauto.
      left; eexists; eauto.
    + right.
      eexists; eauto.
  - apply isexc_implies2 in isv; exrepnd; subst.
    left.
    eexists; eexists; dands; eauto.
    right; unfold isexc_op; auto.
Qed.

Lemma implies_isvalue_like1 {o} :
  forall (op : @Opid o) bterms,
    iscan_like_op op
    -> isvalue_like (oterm op bterms).
Proof.
  introv isc.
  unfold iscan_like_op in isc; repndors.
  - unfold iscan_op in isc; exrepnd; subst; tcsp.
  - unfold isexc_op in isc; exrepnd; subst; tcsp.
Qed.

Definition spoterm {o} (op : @Opid o) := oterm op [].

Definition iscanc {o} (t : @CTerm o) := iscan (get_cterm t).
Definition isexcc {o} (t : @CTerm o) := isexc (get_cterm t).
Definition isvalue_likec {o} (t : @CTerm o) := isvalue_like (get_cterm t).

Lemma iscan_implies_not_isexc {o} :
  forall (t : @NTerm o), iscan t -> !isexc t.
Proof.
  introv isc ise.
  unfold isexc in ise.
  apply iscan_implies in isc; repndors; exrepnd; subst; allsimpl; tcsp.
Qed.
Hint Resolve iscan_implies_not_isexc : slow.

Lemma isvalue_likec_mkc_utoken {o} :
  forall a : get_patom_set o, isvalue_likec (mkc_utoken a).
Proof.
  introv.
  unfold isvalue_likec; simpl; eauto 2 with slow.
Qed.
Hint Resolve isvalue_likec_mkc_utoken : slow.
