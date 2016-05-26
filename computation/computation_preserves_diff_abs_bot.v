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



Require Export computation8.
Require Export computation11.
Require Export computation_preserves_lib.
Require Export atom_ren.
Require Export alphaeq5.


Lemma cl_sub_sub_find {o} :
  forall (sub : @Sub o) v t,
    sub_find sub v = Some t
    -> cl_sub sub
    -> closed t.
Proof.
  introv sf cl.
  apply sub_find_some in sf.
  eapply in_cl_sub; eauto.
Qed.

Inductive diff_abs_bot {o} : @NTerm o -> @NTerm o -> Type :=
| diff_abs_bot_vterm : forall v, diff_abs_bot (vterm v) (vterm v)
| diff_abs_bot_sterm :
    forall f1 f2,
      (forall n, diff_abs_bot (f1 n) (f2 n))
      -> diff_abs_bot (sterm f1) (sterm f2)
| diff_abs_bot_oterm :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2)
      -> diff_abs_bot (oterm op bs1) (oterm op bs2)
| diff_abs_bot_abs :
    forall abs bs v, diff_abs_bot (oterm (Abs abs) bs) (mk_vbot v)
| diff_abs_bot_bot :
    forall abs bs v, diff_abs_bot (mk_vbot v) (oterm (Abs abs) bs)
with diff_abs_bot_b {o} : @BTerm o -> @BTerm o -> Type :=
     | diff_abs_bot_bterm :
         forall l t1 t2,
           diff_abs_bot t1 t2
           -> diff_abs_bot_b (bterm l t1) (bterm l t2).
Hint Constructors diff_abs_bot.
Hint Constructors diff_abs_bot_b.

Ltac inv_diff_imp :=
  match goal with
  | [ H : forall _ _ : _, False -> _ |- _ ] => clear H
  | [ H : forall _ _ : _, (?b1,?b2) = (_,_) [+] False -> _ |- _ ] =>
    let h1 := fresh H in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] False -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] (?b5,?b6) = _ [+] False -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let h3 := fresh H in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      assert (diff_abs_bot_b b5 b6) as h3 by (apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] (?b5,?b6) = _ [+] (?b7,?b8) = _ [+] False -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let h3 := fresh H in
    let h4 := fresh H in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      assert (diff_abs_bot_b b5 b6) as h3 by (apply H; auto);
      assert (diff_abs_bot_b b7 b8) as h4 by (apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] LIn _ (combine ?bs1 ?bs2) -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let i  := fresh "i" in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2) as h2 by (introv i; apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] LIn _ (combine ?bs1 ?bs2) -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let h3 := fresh H in
    let i  := fresh "i" in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      assert (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2) as h3 by (introv i; apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] (?b5,?b6) = _ [+] LIn _ (combine ?bs1 ?bs2) -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let h3 := fresh H in
    let h4 := fresh H in
    let i  := fresh "i" in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      assert (diff_abs_bot_b b5 b6) as h3 by (apply H; auto);
      assert (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2) as h4 by (introv i; apply H; auto);
      clear H
  | [ H : forall _ _ : _, (?b1,?b2) = _ [+] (?b3,?b4) = _ [+] (?b5,?b6) = _ [+] (?b7,?b8) = _ [+] LIn _ (combine ?bs1 ?bs2) -> _ |- _ ] =>
    let h1 := fresh H in
    let h2 := fresh H in
    let h3 := fresh H in
    let h4 := fresh H in
    let h5 := fresh H in
    let i  := fresh "i" in
    assert (diff_abs_bot_b b1 b2) as h1 by (apply H; auto);
      assert (diff_abs_bot_b b3 b4) as h2 by (apply H; auto);
      assert (diff_abs_bot_b b5 b6) as h3 by (apply H; auto);
      assert (diff_abs_bot_b b7 b8) as h4 by (apply H; auto);
      assert (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2) as h5 by (introv i; apply H; auto);
      clear H
  end.

Ltac inv_diff_len len :=
  match type of len with
  | S _ = length ?x => destruct x; simpl in len; cpx
  | length ?x = S _ => destruct x; simpl in len; cpx
  end.

Ltac inv_diff_nterm H :=
  let imp := fresh "imp" in
  let len := fresh "len" in
  inversion H as [|? ? imp|? ? ? len imp| |];
    subst; clear H;
    try (simpl in len; cpx; try (repeat (inv_diff_len len)));
    try (simpl in imp; try inv_diff_imp).

Ltac inv_diff_bterm H :=
  let diff := fresh "diff" in
  try (unfold nobnd in H);
  inversion H as [? ? ? diff]; subst; clear H.

Ltac inv_diff :=
  match goal with
  | [ H : diff_abs_bot (vterm _)   _ |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot (sterm _)   _ |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot (oterm _ _) _ |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot _ (vterm _)   |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot _ (sterm _)   |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot _ (oterm _ _) |- _ ] => inv_diff_nterm H
  | [ H : diff_abs_bot_b (bterm _ _) _ |- _ ] => inv_diff_bterm H
  | [ H : diff_abs_bot_b _ (bterm _ _) |- _ ] => inv_diff_bterm H

  | [ H : diff_abs_bot_b (nobnd _) _ |- _ ] => inv_diff_bterm H
  | [ H : diff_abs_bot_b _ (nobnd _) |- _ ] => inv_diff_bterm H

  | [ H : diff_abs_bot (mk_nat _) _ |- _ ] => unfold mk_nat in H; inv_diff_nterm H
  | [ H : diff_abs_bot _ (mk_nat _) |- _ ] => unfold mk_nat in H; inv_diff_nterm H
  end.

Ltac invdiff := repeat inv_diff.

Definition diff_abs_bot_alpha {o} (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
   & alpha_eq t1 u1
   # alpha_eq t2 u2
   # diff_abs_bot u1 u2}}.

Lemma diff_abs_bot_implies_alpha {o} :
  forall (t1 t2 : @NTerm o),
    diff_abs_bot t1 t2
    -> diff_abs_bot_alpha t1 t2.
Proof.
  introv diff.
  eexists; eexists; dands; [| |eauto]; auto.
Qed.
Hint Resolve diff_abs_bot_implies_alpha : slow.

Lemma diff_abs_bot_alpha_eapply {o} :
  forall (a b c d : @NTerm o),
    diff_abs_bot_alpha a c
    -> diff_abs_bot_alpha b d
    -> diff_abs_bot_alpha (mk_eapply a b) (mk_eapply c d).
Proof.
  introv d1 d2.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_eapply);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_eapply : slow.

Lemma implies_alpha_eq_mk_exception {o} :
  forall (a1 a2 b1 b2 : @NTerm o),
    alpha_eq a1 b1
    -> alpha_eq a2 b2
    -> alpha_eq (mk_exception a1 a2) (mk_exception b1 b2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma diff_abs_bot_alpha_exc {o} :
  forall (a b c d : @NTerm o),
    diff_abs_bot_alpha a c
    -> diff_abs_bot_alpha b d
    -> diff_abs_bot_alpha (mk_exception a b) (mk_exception c d).
Proof.
  introv d1 d2.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_exception);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_exc : slow.

Lemma implies_alpha_eq_mk_arithop {o} :
  forall op (a1 a2 b1 b2 : @NTerm o),
    alpha_eq a1 b1
    -> alpha_eq a2 b2
    -> alpha_eq (mk_arithop op a1 a2) (mk_arithop op b1 b2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_alpha_eq_mk_compop {o} :
  forall op (a1 a2 a3 a4 b1 b2 b3 b4 : @NTerm o),
    alpha_eq a1 b1
    -> alpha_eq a2 b2
    -> alpha_eq a3 b3
    -> alpha_eq a4 b4
    -> alpha_eq (mk_compop op a1 a2 a3 a4) (mk_compop op b1 b2 b3 b4).
Proof.
  introv aeq1 aeq2 aeq3 aeq4.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma diff_abs_bot_alpha_arithop {o} :
  forall op (a b c d : @NTerm o),
    diff_abs_bot_alpha a c
    -> diff_abs_bot_alpha b d
    -> diff_abs_bot_alpha (mk_arithop op a b) (mk_arithop op c d).
Proof.
  introv d1 d2.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_arithop);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_arithop : slow.

Lemma diff_abs_bot_alpha_compop {o} :
  forall op (a1 a2 a3 a4 b1 b2 b3 b4 : @NTerm o),
    diff_abs_bot_alpha a1 b1
    -> diff_abs_bot_alpha a2 b2
    -> diff_abs_bot_alpha a3 b3
    -> diff_abs_bot_alpha a4 b4
    -> diff_abs_bot_alpha (mk_compop op a1 a2 a3 a4) (mk_compop op b1 b2 b3 b4).
Proof.
  introv d1 d2 d3 d4.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_compop);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_compop : slow.

Lemma diff_abs_bot_alpha_apply {o} :
  forall (a b c d : @NTerm o),
    diff_abs_bot_alpha a c
    -> diff_abs_bot_alpha b d
    -> diff_abs_bot_alpha (mk_apply a b) (mk_apply c d).
Proof.
  introv d1 d2.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_apply);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_apply : slow.

Lemma diff_abs_bot_alpha_atom_eq {o} :
  forall (a1 a2 a3 a4 b1 b2 b3 b4 : @NTerm o),
    diff_abs_bot_alpha a1 b1
    -> diff_abs_bot_alpha a2 b2
    -> diff_abs_bot_alpha a3 b3
    -> diff_abs_bot_alpha a4 b4
    -> diff_abs_bot_alpha (mk_atom_eq a1 a2 a3 a4) (mk_atom_eq b1 b2 b3 b4).
Proof.
  introv d1 d2 d3 d4.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_atom_eq);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_atom_eq : slow.

Lemma diff_abs_bot_alpha_fix {o} :
  forall (a b : @NTerm o),
    diff_abs_bot_alpha a b
    -> diff_abs_bot_alpha (mk_fix a) (mk_fix b).
Proof.
  introv d.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_fix);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_fix : slow.

Lemma diff_abs_bot_alpha_fresh {o} :
  forall v (a b : @NTerm o),
    diff_abs_bot_alpha a b
    -> diff_abs_bot_alpha (mk_fresh v a) (mk_fresh v b).
Proof.
  introv d.
  allunfold @diff_abs_bot_alpha; exrepnd.
  eexists; eexists; dands;
  try (apply implies_alpha_eq_mk_fresh);
  try eassumption.
  constructor; simpl; auto.
  introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve diff_abs_bot_alpha_fresh : slow.

Lemma diff_abs_bot_preserves_isnoncan_like {o} :
  forall (t1 t2 : @NTerm o),
    isnoncan_like t1
    -> diff_abs_bot t1 t2
    -> isnoncan_like t2.
Proof.
  introv isn d.
  inversion d; subst; try (unfold mk_vbot, mk_bottom, mk_fix); auto.
Qed.
Hint Resolve diff_abs_bot_preserves_isnoncan_like : slow.

Lemma diff_abs_bot_preserves_isvalue_like {o} :
  forall (t1 t2 : @NTerm o),
    isvalue_like t1
    -> diff_abs_bot t1 t2
    -> isvalue_like t2.
Proof.
  introv isn d.
  inversion d; subst; try (unfold mk_vbot, mk_bottom, mk_fix); auto.
Qed.
Hint Resolve diff_abs_bot_preserves_isvalue_like : slow.

Lemma diff_abs_bot_sym {o} :
  forall (t1 t2 : @NTerm o),
    diff_abs_bot t1 t2
    -> diff_abs_bot t2 t1.
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case; introv d;
  invdiff; auto; try (complete constructor).

  Case "oterm".
  constructor; auto.
  introv i.
  destruct b1 as [l1 t1].
  destruct b2 as [l2 t2].
  applydup @in_combine_swap in i; auto.
  apply imp in i0.
  inversion i0 as [? ? ? d]; clear i0; subst.
  constructor.
  apply in_combine in i; repnd.
  eapply ind; eauto.
Qed.
Hint Resolve diff_abs_bot_sym : slow.

Inductive diff_abs_bot_subs {o} : @Sub o -> @Sub o -> Type :=
| dab_sub_nil : diff_abs_bot_subs [] []
| dab_sub_cons :
    forall v t1 t2 sub1 sub2,
      diff_abs_bot t1 t2
      -> diff_abs_bot_subs sub1 sub2
      -> diff_abs_bot_subs ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors diff_abs_bot_subs.

Lemma diff_abs_bot_subs_sub_find_some {o} :
  forall (sub1 sub2 : @Sub o) v t,
    diff_abs_bot_subs sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # diff_abs_bot t u}.
Proof.
  induction sub1; destruct sub2; introv d fs; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma diff_abs_bot_subs_sub_find_none {o} :
  forall (sub1 sub2 : @Sub o) v,
    diff_abs_bot_subs sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d fn; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma diff_abs_bot_subs_filter {o} :
  forall (sub1 sub2 : @Sub o) l,
    diff_abs_bot_subs sub1 sub2
    -> diff_abs_bot_subs (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.
Hint Resolve diff_abs_bot_subs_filter : slow.

Lemma diff_abs_bot_lsubst_aux {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    diff_abs_bot t1 t2
    -> diff_abs_bot_subs sub1 sub2
    -> diff_abs_bot (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v|s|op bs ind] Case;
  introv dt ds; allsimpl;
  invdiff; allsimpl; auto;
  try (complete (autorewrite with slow; constructor)).

  - Case "vterm".
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (diff_abs_bot_subs_sub_find_some sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (diff_abs_bot_subs_sub_find_none sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "oterm".
    constructor; autorewrite with slow in *; auto.
    introv i.
    rewrite <- map_combine in i.
    apply in_map_iff in i; exrepnd; allsimpl; ginv.
    applydup imp in i1.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2]; allsimpl.
    invdiff.
    constructor.
    apply in_combine in i1; repnd.
    eapply ind; eauto 2 with slow.
Qed.

Lemma diff_abs_bot_alpha_l {o} :
  forall (t1 t2 t3 : @NTerm o),
    alpha_eq t1 t2
    -> diff_abs_bot_alpha t2 t3
    -> diff_abs_bot_alpha t1 t3.
Proof.
  introv aeq d.
  allunfold @diff_abs_bot_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Lemma diff_abs_bot_alpha_r {o} :
  forall (t1 t2 t3 : @NTerm o),
    diff_abs_bot_alpha t1 t2
    -> alpha_eq t2 t3
    -> diff_abs_bot_alpha t1 t3.
Proof.
  introv d aeq.
  allunfold @diff_abs_bot_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Definition diff_abs_bot_bterms {o} (bs1 bs2 : list (@BTerm o)) :=
  br_bterms diff_abs_bot_b bs1 bs2.

Lemma diff_abs_bot_refl {o} :
  forall (t : @NTerm o),
    diff_abs_bot t t.
Proof.
  nterm_ind t as [v|s ind|op bs ind] Case; introv; allsimpl; auto.

  Case "oterm".
  constructor; auto.
  introv i.
  rw in_combine_same in i; repnd; subst.
  destruct b2 as [l t].
  constructor; eapply ind; eauto.
Qed.
Hint Resolve diff_abs_bot_refl : slow.

Lemma diff_abs_bot_subs_refl {o} :
  forall (sub : @Sub o),
    diff_abs_bot_subs sub sub.
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a.
  constructor; eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_subs_refl : slow.

Lemma alpha_eq_mk_vbot_implies {o} :
  forall v (t : @NTerm o),
    alpha_eq (mk_vbot v) t
    -> {z : NVar & t = mk_vbot z}.
Proof.
  introv aeq.
  inversion aeq as [|?|? ? ? len imp]; subst; allsimpl; cpx; clear aeq.
  pose proof (imp 0) as h; clear imp; autodimp h hyp.
  unfold selectbt in h; allsimpl.
  apply alphaeqbt_nilv in h; exrepnd; subst.
  inversion h0 as [|?|? ? ? len imp]; subst; allsimpl; cpx; clear h0.
  pose proof (imp 0) as h; clear imp; autodimp h hyp.
  unfold selectbt in h; allsimpl.
  apply alphaeqbt_1v in h; exrepnd; subst; allrw disjoint_singleton_l.
  allunfold @lsubst; allsimpl.
  allrw not_over_or; repnd; boolvar; allrw disjoint_singleton_r.
  - destruct nt2 as [w|f|op bs]; allsimpl; allrw not_over_or; repnd; boolvar; tcsp;
    inversion h0; subst; tcsp.
    exists w; auto.
  - destruct n; allunfold @all_vars; allrw in_app_iff; sp.
Qed.

Lemma diff_abs_bot_change_bound_vars {o} :
  forall vs (t1 t2 : @NTerm o),
    diff_abs_bot t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
        & diff_abs_bot u1 u2
        # alpha_eq t1 u1
        # alpha_eq t2 u2
        # disjoint (bound_vars u1) vs
        # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind1s t1 as [v|s ind|op bs ind] Case; introv d;
  invdiff; allsimpl; auto.

  - Case "vterm".
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto 3 with slow.

  - Case "sterm".
    exists (sterm s) (sterm f2); dands; simpl; auto.

  - Case "oterm".

    assert ({bs' : list BTerm
             & {bs2' : list BTerm
             & alpha_eq_bterms bs bs'
             # alpha_eq_bterms bs2 bs2'
             # diff_abs_bot_bterms bs' bs2'
             # disjoint (flat_map bound_vars_bterm bs') vs
             # disjoint (flat_map bound_vars_bterm bs2') vs}}) as h.

      { revert dependent bs2.
        induction bs; destruct bs2; introv len imp; allsimpl; ginv.
        - exists ([] : list (@BTerm o)) ([] : list (@BTerm o));
            dands; simpl; eauto 3 with slow; try (apply br_bterms_nil).
        - cpx.
          destruct a as [l1 t1].
          destruct b as [l2 t2].
          pose proof (imp (bterm l1 t1) (bterm l2 t2)) as h; autodimp h hyp.
          invdiff.
          pose proof (ind t1 t1 l2) as h; repeat (autodimp h hyp); eauto 3 with slow.
          pose proof (h t2 diff) as k; clear h.
          exrepnd.

          autodimp IHbs hyp.
          { introv i d; eapply ind; eauto. }
          pose proof (IHbs bs2) as k.
          repeat (autodimp k hyp).
          exrepnd.

          pose proof (fresh_vars
                        (length l2)
                        (vs
                           ++ l2
                           ++ all_vars t1
                           ++ all_vars t2
                           ++ all_vars u1
                           ++ all_vars u2
                        )) as fv; exrepnd.
          allrw disjoint_app_r; repnd.

          exists ((bterm lvn (lsubst_aux u1 (var_ren l2 lvn))) :: bs')
                 ((bterm lvn (lsubst_aux u2 (var_ren l2 lvn))) :: bs2');
            dands; simpl;
            try (apply br_bterms_cons);
            try (apply alpha_eq_bterm_congr);
            tcsp.
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { constructor.
            apply diff_abs_bot_lsubst_aux; eauto 3 with slow;
            try (rw @sub_free_vars_var_ren; eauto 3 with slow);
            try (rw @dom_sub_var_ren; eauto 3 with slow). }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u1 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u2 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
      }

      exrepnd.
      allunfold @alpha_eq_bterms.
      allunfold @diff_abs_bot_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands;
      eauto 3 with slow;
      try (complete (apply alpha_eq_oterm_combine; dands; auto)).

  - pose proof (change_bvars_alpha_wspec vs (oterm (Abs abs) bs)) as p.
    exrepnd.
    pose proof (change_bvars_alpha_wspec vs (@mk_vbot o v)) as q.
    exrepnd.
    eexists; eexists; dands; try (exact p0); try (exact q0);
    eauto 3 with slow.

    apply alpha_eq_mk_vbot_implies in q0; exrepnd; subst.
    inversion p0; subst; auto.

  - pose proof (change_bvars_alpha_wspec vs (oterm (Abs abs) bs0)) as p.
    exrepnd.
    pose proof (change_bvars_alpha_wspec vs (@mk_vbot o v)) as q.
    exrepnd.
    eexists; eexists; dands; try (exact p0); try (exact q0);
    eauto 3 with slow.

    apply alpha_eq_mk_vbot_implies in q0; exrepnd; subst.
    inversion p0; subst; auto.
Qed.

Lemma diff_abs_bot_alpha_lsubst {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    diff_abs_bot t1 t2
    -> diff_abs_bot_subs sub1 sub2
    -> diff_abs_bot_alpha (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv d1 d2.

  pose proof (diff_abs_bot_change_bound_vars
                (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2 d1) as h.
  exrepnd.

  eapply diff_abs_bot_alpha_l;[apply lsubst_alpha_congr2;exact h2|].
  eapply diff_abs_bot_alpha_r;[|apply alpha_eq_sym;apply lsubst_alpha_congr2;exact h3].
  clear dependent t1.
  clear dependent t2.
  allrw disjoint_app_r; repnd.

  pose proof (unfold_lsubst sub1 u1) as z; exrepnd.
  rewrite z0; clear z0.

  pose proof (unfold_lsubst sub2 u2) as q; exrepnd.
  rewrite q0; clear q0.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2).

  dands; try (apply lsubst_aux_alpha_congr_same_disj); eauto 3 with slow.
  apply diff_abs_bot_lsubst_aux; auto.
Qed.

Lemma diff_abs_bot_preserves_isexc {o} :
  forall (t1 t2 : @NTerm o),
    diff_abs_bot t1 t2
    -> isexc t1
    -> isexc t2.
Proof.
  introv d ise.
  apply isexc_implies2 in ise; exrepnd; subst.
  invdiff.
Qed.
Hint Resolve diff_abs_bot_preserves_isexc : slow.

Lemma diff_abs_bot_preserves_eapply_wf_def {o} :
  forall can (bs1 bs2 : list (@BTerm o)),
    eapply_wf_def (oterm (Can can) bs1)
    -> length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_abs_bot_b b1 b2)
    -> eapply_wf_def (oterm (Can can) bs2).
Proof.
  introv w e i.
  allunfold @eapply_wf_def; repndors; exrepnd; subst;
  allunfold @mk_nseq; allunfold @mk_lam; ginv; allsimpl; cpx; tcsp.
  - right; left; eexists; eauto.
  - allsimpl; inv_diff_imp; invdiff.
    right; right.
    eexists; eexists; eauto.
Qed.
Hint Resolve diff_abs_bot_preserves_eapply_wf_def : slow.

Lemma hasvalue_like_eapply_can_right {o} :
  forall lib (a b : @NTerm o),
    iscan a
    -> hasvalue_like lib (mk_eapply a b)
    -> hasvalue_like lib b.
Proof.
  introv isc hv.
  allunfold @hasvalue_like; exrepnd.
  allunfold @reduces_to; exrepnd.
  revert dependent b.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in *; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct a as [x|g|op bs]; ginv.

    + apply compute_step_eapply_success in comp1; exrepnd; ginv.
      repndors; exrepnd.

      * apply compute_step_eapply2_success in comp1; repnd; GC.
        repndors; exrepnd; subst; ginv.
        exists (@mk_nat o n); dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst.
        apply isexc_implies2 in comp2; exrepnd; subst; ginv.
        exists (oterm Exc l); dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst.
        apply IHk in comp0; exrepnd.
        exists v0; dands; auto.
        exists (S k0).
        apply reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

    + apply iscan_implies in isc; repndors; exrepnd; ginv.
      apply compute_step_eapply_success in comp1; exrepnd; ginv.
      repndors; exrepnd.

      * apply compute_step_eapply2_success in comp1; repnd; GC.
        exists arg2; dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst.
        exists arg2; dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst.
        apply IHk in comp0; exrepnd.
        exists v0; dands; auto.
        exists (S k0).
        apply reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.
Qed.
Hint Resolve hasvalue_like_eapply_can_right : slow.

Lemma hasvalue_like_eapply_sterm_right {o} :
  forall lib f (a : @NTerm o),
    hasvalue_like lib (mk_eapply (sterm f) a)
    -> hasvalue_like lib a.
Proof.
  introv hv.
  apply hasvalue_like_eapply_can_right in hv; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_like_eapply_sterm_right : slow.

Lemma hasvalue_like_arithop_can_right {o} :
  forall lib c (a b : @NTerm o),
    iscan a
    -> hasvalue_like lib (mk_arithop c a b)
    -> hasvalue_like lib b.
Proof.
  introv isc hv.
  allunfold @hasvalue_like; exrepnd.
  allunfold @reduces_to; exrepnd.
  revert dependent b.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in *; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply iscan_implies in isc; repndors; exrepnd; subst.

    + apply compute_step_narithop_can1_success in comp1.
      repnd; repndors; exrepnd; ginv.

      * apply compute_step_arithop_success_can_can in comp3; exrepnd; subst; GC.
        exists (oterm (Can can') []); dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst; allunfold @nobnd; ginv.
        apply IHk in comp0; exrepnd.
        exists v0; dands; auto.
        exists (S k0).
        apply reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

      * exists t; dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

    + csunf comp1; allsimpl; ginv.
Qed.
Hint Resolve hasvalue_like_arithop_can_right : slow.

Lemma hasvalue_like_compop_can_right {o} :
  forall lib co (a b c d : @NTerm o),
    iscan a
    -> hasvalue_like lib (mk_compop co a b c d)
    -> hasvalue_like lib b.
Proof.
  introv isc hv.
  allunfold @hasvalue_like; exrepnd.
  allunfold @reduces_to; exrepnd.
  revert dependent b.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in *; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply iscan_implies in isc; repndors; exrepnd; subst.

    + apply compute_step_ncompop_can1_success in comp1.
      repnd; repndors; exrepnd; ginv.

      * apply compute_step_compop_success_can_can in comp3; exrepnd; subst; GC.
        exists (oterm (Can can') []); dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

      * subst; allunfold @nobnd; ginv.
        apply IHk in comp0; exrepnd.
        exists v0; dands; auto.
        exists (S k0).
        apply reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

      * exists t; dands; eauto 3 with slow.
        exists 0.
        apply reduces_in_atmost_k_steps_0; auto.

    + csunf comp1; allsimpl; ginv.
Qed.
Hint Resolve hasvalue_like_compop_can_right : slow.

Lemma not_hasvalue_like_vbot {o} :
  forall lib v, !@hasvalue_like o lib (mk_vbot v).
Proof.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_to_vbot_if_isvalue_like in hv1; auto.
Qed.

Lemma hasvalue_like_compute_step {o} :
  forall lib (t u : @NTerm o),
    hasvalue_like lib t
    -> compute_step lib t = csuccess u
    -> hasvalue_like lib u.
Proof.
  introv hv comp.
  allunfold @hasvalue_like; exrepnd.
  apply reduces_to_split2 in hv1; repndors; exrepnd; subst.
  - rewrite compute_step_value_like in comp; auto; ginv.
    exists u; dands; auto.
    apply reduces_to_symm.
  - rewrite hv1 in comp; ginv.
    exists v; dands; auto.
Qed.

Lemma hasvalue_like_ncan_fst {o} :
  forall lib ncan (t : @NTerm o) bs,
    hasvalue_like lib (oterm (NCan ncan) (bterm [] t :: bs))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  allunfold @hasvalue_like; exrepnd.
  pose proof (converges_to_value_like_ncan lib ncan t bs) as h.
  autodimp h hyp.

  {
    unfold converges_to_value_like.
    exists v; dands; auto.
  }

  exrepnd.
  exists u; dands; repndors; eauto 3 with slow.
Qed.

Definition diff_abs_bot_b_alpha {o} (b1 b2 : @BTerm o) :=
  {u1 : BTerm
   & {u2 : BTerm
   & alpha_eq_bterm b1 u1
   # alpha_eq_bterm b2 u2
   # diff_abs_bot_b u1 u2}}.

Definition diff_abs_bot_bs_alpha {o} (bs1 bs2 : list (@BTerm o)) :=
  br_bterms diff_abs_bot_b_alpha bs1 bs2.

Lemma diff_abs_bot_bterms_cons {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    diff_abs_bot_bterms (b1 :: bs1) (b2 :: bs2)
    <=> (diff_abs_bot_b b1 b2 # diff_abs_bot_bterms bs1 bs2).
Proof.
  unfold diff_abs_bot_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma diff_abs_bot_bterms_nil {o} :
  @diff_abs_bot_bterms o [] [].
Proof.
  unfold diff_abs_bot_bterms, br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve diff_abs_bot_bterms_nil : slow.

Lemma diff_abs_bot_bterms_cons_if {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    diff_abs_bot_b b1 b2
    -> diff_abs_bot_bterms bs1 bs2
    -> diff_abs_bot_bterms (b1 :: bs1) (b2 :: bs2).
Proof.
  introv d1 d2; apply diff_abs_bot_bterms_cons; sp.
Qed.
Hint Resolve diff_abs_bot_bterms_cons_if : slow.

Lemma diff_abs_bot_bs_alpha_cons {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    diff_abs_bot_bs_alpha (b1 :: bs1) (b2 :: bs2)
    <=> (diff_abs_bot_b_alpha b1 b2 # diff_abs_bot_bs_alpha bs1 bs2).
Proof.
  unfold diff_abs_bot_bs_alpha; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma diff_abs_bot_bs_alpha_cons_if {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    diff_abs_bot_b_alpha b1 b2
    -> diff_abs_bot_bs_alpha bs1 bs2
    -> diff_abs_bot_bs_alpha (b1 :: bs1) (b2 :: bs2).
Proof.
  introv d1 d2; apply diff_abs_bot_bs_alpha_cons; sp.
Qed.
Hint Resolve diff_abs_bot_bs_alpha_cons_if : slow.

Lemma diff_abs_bot_b_implies_diff_abs_bot_b_alpha {o} :
  forall (b1 b2 : @BTerm o),
    diff_abs_bot_b b1 b2
    -> diff_abs_bot_b_alpha b1 b2.
Proof.
  introv d.
  exists b1 b2; dands; eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_b_implies_diff_abs_bot_b_alpha : slow.

Lemma diff_abs_bot_bterms_implies_diff_abs_bot_bs_alpha {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    diff_abs_bot_bterms bs1 bs2
    -> diff_abs_bot_bs_alpha bs1 bs2.
Proof.
  introv d.
  unfold diff_abs_bot_bterms in d.
  unfold diff_abs_bot_bs_alpha.
  allunfold @br_bterms.
  allunfold @br_list; repnd; dands; auto.
  introv i; apply d in i.
  eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_bterms_implies_diff_abs_bot_bs_alpha : slow.

Lemma implies_diff_abs_bot_alpha_oterm {o} :
  forall op (bs1 bs2 : list (@BTerm o)),
    diff_abs_bot_bs_alpha bs1 bs2
    -> diff_abs_bot_alpha (oterm op bs1) (oterm op bs2).
Proof.
  introv diff.
  unfold diff_abs_bot_bs_alpha, br_bterms, br_list in diff; repnd.

  assert {bs1' : list BTerm
          & {bs2' : list BTerm
          & alpha_eq_bterms bs1 bs1'
          # alpha_eq_bterms bs2 bs2'
          # diff_abs_bot_bterms bs1' bs2'}} as hbs.
  { revert dependent bs2.
    induction bs1; introv len imp; destruct bs2; allsimpl; cpx; GC.
    - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)); dands; eauto 3 with slow.
    - pose proof (imp a b) as h; autodimp h hyp.
      pose proof (IHbs1 bs2) as k; repeat (autodimp k hyp).
      exrepnd.
      unfold diff_abs_bot_b_alpha in h; exrepnd.
      exists (u1 :: bs1') (u2 :: bs2'); dands; eauto 3 with slow. }

  exrepnd.
  applydup @alpha_eq_bterms_implies_same_length in hbs0.
  applydup @alpha_eq_bterms_implies_same_length in hbs2.
  exists (oterm op bs1') (oterm op bs2'); dands; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs0; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs2; auto.

  - constructor; try omega.
    introv i; apply hbs1; auto.
Qed.

Lemma implies_diff_abs_bot_b_alpha {o} :
  forall l (t1 t2 : @NTerm o),
    diff_abs_bot_alpha t1 t2
    -> diff_abs_bot_b_alpha (bterm l t1) (bterm l t2).
Proof.
  introv d.
  unfold diff_abs_bot_alpha in d; exrepnd.
  exists (bterm l u1) (bterm l u2); dands; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_abs_bot_b_alpha : slow.

Lemma diff_abs_bot_alpha_pushdown_fresh_isvalue_like {o} :
  forall v (t1 t2 : @NTerm o),
    isvalue_like t1
    -> diff_abs_bot t1 t2
    -> diff_abs_bot_alpha (pushdown_fresh v t1) (pushdown_fresh v t2).
Proof.
  introv ivl d.
  destruct t1 as [v1|f1|op1 bs1]; invdiff; allsimpl; eauto 3 with slow;
  try (complete (unfold isvalue_like in ivl; allsimpl; tcsp)).

  apply implies_diff_abs_bot_alpha_oterm.
  unfold diff_abs_bot_bs_alpha, br_bterms, br_list, mk_fresh_bterms.
  autorewrite with slow; dands; auto.
  introv i.
  rewrite <- map_combine in i.
  apply in_map_iff in i; exrepnd; ginv.
  applydup imp in i1.
  destruct a0 as [l1 t1].
  destruct a as [l2 t2].
  allsimpl.
  invdiff.
  apply implies_diff_abs_bot_b_alpha.
  unfold maybe_new_var; boolvar; eauto 3 with slow.

  pose proof (ex_fresh_var (all_vars t1 ++ all_vars t2)) as fv; exrepnd.
  allrw in_app_iff; allrw not_over_or; repnd.
  exists (mk_fresh v0 t1) (mk_fresh v0 t2).
  dands; auto.

  { apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp.
    repeat (rw @lsubst_trivial3); allsimpl; auto.
    - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
      dands; auto.
    - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
      dands; auto.
      apply newvar_prop. }

  { apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp.
    repeat (rw @lsubst_trivial3); allsimpl; auto.
    - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
      dands; auto.
    - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
      dands; auto.
      apply newvar_prop. }

  { constructor; auto; simpl.
    introv i; repndors; cpx. }
Qed.
Hint Resolve diff_abs_bot_alpha_pushdown_fresh_isvalue_like : slow.

Hint Resolve get_fresh_atom_prop : slow.
Hint Rewrite @get_utokens_sub_cons : slow.

Lemma implies_disjoint_singleton_l :
  forall (A : tuniv) (x : A) (s : list A),
    !LIn x s
    -> disjoint [x] s.
Proof.
  introv h.
  apply disjoint_singleton_l; auto.
Qed.
Hint Resolve implies_disjoint_singleton_l : slow.

Lemma implies_disjoint_singleton_r :
  forall (A : tuniv) (x : A) (s : list A),
    !LIn x s
    -> disjoint s [x].
Proof.
  introv h.
  apply disjoint_singleton_r; auto.
Qed.
Hint Resolve implies_disjoint_singleton_r : slow.

Lemma hasvalue_like_if_compute_step {o} :
  forall lib (t u : @NTerm o),
    hasvalue_like lib u
    -> compute_step lib t = csuccess u
    -> hasvalue_like lib t.
Proof.
  introv hv comp; allunfold @hasvalue_like; exrepnd.
  exists v; dands; auto.
  eapply reduces_to_if_split2; eauto.
Qed.

Lemma diff_abs_bot_subst_utokens_aux {o} :
  forall (t1 t2 : @NTerm o) sub,
    diff_abs_bot t1 t2
    -> diff_abs_bot (subst_utokens_aux t1 sub) (subst_utokens_aux t2 sub).
Proof.
  nterm_ind t1 as [v1|f1|op1 bs1 ind1] Case; introv d; invdiff; auto;
  try (complete (allsimpl; auto));
  try (complete (allsimpl; constructor)).

  Case "oterm".
  allrw @subst_utokens_aux_oterm.
  remember (get_utok op1) as guo1; symmetry in Heqguo1; destruct guo1.

  - unfold subst_utok.
    remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
    constructor; allrw map_length; auto.
    introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
    applydup imp in i1; applydup in_combine in i1; repnd.
    destruct a0 as [l1 u1].
    destruct a as [l2 u2].
    invdiff; allsimpl.
    constructor.
    eapply ind1; eauto.

  - constructor; allrw map_length; auto.
    introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
    applydup imp in i1; applydup in_combine in i1; repnd.
    destruct a0 as [l1 u1].
    destruct a as [l2 u2].
    invdiff; allsimpl.
    constructor; auto.
    eapply ind1; eauto.
Qed.

Lemma diff_abs_bot_alpha_subst_utokens {o} :
  forall (t1 t2 : @NTerm o) sub,
    diff_abs_bot_alpha t1 t2
    -> diff_abs_bot_alpha (subst_utokens t1 sub) (subst_utokens t2 sub).
Proof.
  introv d.
  unfold diff_abs_bot_alpha in d; exrepnd.

  eapply diff_abs_bot_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d0|].
  eapply diff_abs_bot_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d2].
  clear dependent t1.
  clear dependent t2.

  pose proof (diff_abs_bot_change_bound_vars
                (free_vars_utok_sub sub)
                u1 u2 d1) as d; exrepnd.
  rename u0 into t1.
  rename u3 into t2.

  eapply diff_abs_bot_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d3|].
  eapply diff_abs_bot_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d4].
  clear dependent u1.
  clear dependent u2.

  pose proof (unfold_subst_utokens sub t1) as h; exrepnd.
  pose proof (unfold_subst_utokens sub t2) as k; exrepnd.
  rename t' into u1.
  rename t'0 into u2.
  rw h0; rw k0.

  eapply diff_abs_bot_alpha_l;[apply (alpha_eq_subst_utokens_aux u1 t1 sub sub); eauto 3 with slow|].
  eapply diff_abs_bot_alpha_r;[|apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u2 t2 sub sub); eauto 3 with slow].

  apply diff_abs_bot_implies_alpha.
  apply diff_abs_bot_subst_utokens_aux; auto.
Qed.

Lemma compute_step_abs2bot_lsubst_aux {o} :
  forall (t : @NTerm o) t' u,
    wf_term t
    -> wf_term t'
    -> compute_step [] t = csuccess u
    (* hasvalue_like is needed in the case where t is bot and t' is abs *)
    -> hasvalue_like [] u
    -> diff_abs_bot t t'
    -> {u' : NTerm
        & compute_step [] t' = csuccess u'
        # diff_abs_bot_alpha u u'}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf wf' comp hv diff.

  - Case "vterm".
    allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; auto.
    inv_diff.
    csunf; simpl.
    eexists; dands; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; auto.
      inv_diff.
      eexists; csunf; simpl; dands; eauto 3 with slow.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            csunf; simpl; auto.
            invdiff.
            simpl.
            eexists; dands; eauto 5 with slow.
          }

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv.
              invdiff.
              csunf; simpl.
              dcwf h; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
              eexists; dands; eauto 2 with slow.

            + invdiff.
              csunf; simpl.
              apply isexc_implies2 in comp0; exrepnd; subst.
              invdiff.
              dcwf h; simpl; auto.
              eexists; dands; eauto 3 with slow.

            + invdiff.
              fold_terms.
              rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
              pose proof (ind arg2 arg2 []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              apply wf_term_eapply_iff in wf; exrepnd; allunfold @nobnd; ginv.
              apply wf_term_eapply_iff in wf'; exrepnd; allunfold @nobnd; ginv.
              allsimpl; cpx.
              eapply h in comp1; clear h; auto; try(exact diff); eauto 3 with slow.
              exrepnd; rewrite comp1.
              eexists; dands; eauto.
              fold_terms; eauto 4 with slow.
          }

          {
            SSCase "NFix".
            apply compute_step_fix_success in comp; repnd; subst.
            invdiff.
            csunf; simpl; auto.
            eexists; dands; eauto.
            fold_terms; eauto 7 with slow.
          }

          {
            SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst.
            invdiff.
            csunf; simpl; auto.
            eexists; dands; eauto.
            apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
          }

          {
            SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
            invdiff.
            csunf; simpl.
            eexists; dands; eauto 7 with slow.
          }

          {
            SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.
            invdiff.
            csunf; simpl.
            eexists; dands; eauto 3 with slow.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.

              repndors; exrepnd; subst; auto; invdiff;
              csunf; simpl; eexists; dands; eauto 4 with slow.
              apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  invdiff.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto;
                  invdiff;
                  eexists; dands; eauto;
                  apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.

                + unfold mk_nseq in *; allsimpl; ginv; GC.
                  invdiff.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.
                  eexists; dands; eauto 3 with slow.

              - invdiff.
                fold_terms; rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow.
                eexists; dands; eauto 3 with slow.

              - invdiff.
                fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply wf_term_eapply_iff in wf; exrepnd; allunfold @nobnd; ginv.
                apply wf_term_eapply_iff in wf'; exrepnd; allunfold @nobnd; ginv.
                allsimpl; cpx.
                eapply q in comp1; clear q; auto; try (exact diff); eauto 3 with slow.
                exrepnd; rewrite comp1; auto.
                eexists; dands; eauto.
                apply diff_abs_bot_alpha_eapply; eauto 3 with slow.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.

              - csunf; simpl; eexists; dands; eauto.
                apply diff_abs_bot_alpha_apply; eauto 3 with slow.
                apply diff_abs_bot_alpha_fix; eauto 3 with slow.

              - fold_terms.
                eapply hasvalue_like_compute_step in hv;
                  [|csunf;simpl;auto].
                unfold apply_bterm in hv; allsimpl.
                rewrite lsubst_lsubst_aux in hv; allsimpl; auto.
                boolvar.
                apply not_hasvalue_like_vbot in hv; tcsp.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl; eexists; dands; eauto.
              apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl; eexists; dands; eauto.
              apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.

              repndors; exrepnd; subst; auto;
              csunf; simpl; eexists; dands; eauto;
              apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl; eexists; dands; eauto.
              apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              unfold compute_step_sleep; simpl.
              eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
              eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              unfold compute_step_minus; simpl.
              eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              eexists; dands; eauto 7 with slow.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              unfold compute_step_parallel.
              eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; simpl; invdiff.

              - csunf; simpl.
                dcwf h.
                apply compute_step_compop_success_can_can in comp1; exrepnd; subst; ginv; GC.

                repndors; exrepnd; subst; allsimpl; cpx;
                unfold compute_step_comp; allrw;
                eexists; dands; eauto;
                boolvar; eauto 3 with slow.

              - rewrite compute_step_ncompop_ncanlike2; eauto 3 with slow.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allrw @wf_term_ncompop_iff; exrepnd; ginv.
                allsimpl; cpx.
                eapply q in comp4; clear q; auto; try (exact diff);
                try (complete (apply hasvalue_like_compop_can_right in hv; auto)).
                exrepnd.
                rewrite comp2; auto.
                allsimpl; inv_diff_imp; invdiff.
                eexists; dands; eauto.
                apply diff_abs_bot_alpha_compop; eauto 3 with slow.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                invdiff.
                dcwf h; simpl; auto.
                eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; allsimpl; invdiff.

              - csunf; simpl.
                dcwf h.
                apply compute_step_arithop_success_can_can in comp1; exrepnd; subst; ginv; GC.
                allsimpl; cpx.

                repndors; exrepnd; subst; allsimpl;
                unfold compute_step_comp; allrw;
                eexists; dands; eauto;
                boolvar; eauto 3 with slow.

              - rewrite compute_step_narithop_ncanlike2; eauto 3 with slow.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allrw @wf_term_narithop_iff; exrepnd; ginv.
                allsimpl; cpx.
                eapply q in comp4; clear q; auto; try (exact diff);
                try (complete (apply hasvalue_like_arithop_can_right in hv; auto)).
                exrepnd.
                rewrite comp2; auto.
                eexists; dands; eauto.
                apply diff_abs_bot_alpha_arithop; eauto 3 with slow.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                invdiff.
                dcwf h; simpl; auto.
                eexists; dands; eauto 3 with slow.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
              invdiff.
              csunf; simpl.
              eexists; dands; eauto.
              destruct (canonical_form_test_for c can2); eauto 3 with slow.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step [] (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind
                          (oterm (NCan ncan2) bts)
                          (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.

            applydup @wf_oterm_iff in wf; repnd.
            pose proof (wf0 (bterm [] (oterm (NCan ncan2) bts))) as wfn; allsimpl.
            autodimp wfn hyp.
            allrw @wf_bterm_iff.

            invdiff.

            * applydup @wf_oterm_iff in wf'; repnd.
              pose proof (wf'0 (bterm [] (oterm (NCan ncan2) bs0))) as wf'n; allsimpl.
              autodimp wf'n hyp.
              allrw @wf_bterm_iff.

              apply (q (oterm (NCan ncan2) bs0)) in Heqc; clear q; auto;
              try (complete (apply hasvalue_like_ncan_fst in hv; auto)).
              exrepnd.
              csunf; allsimpl.
              rewrite Heqc1; auto; simpl.
              eexists; dands; eauto.

              apply implies_diff_abs_bot_alpha_oterm.
              apply diff_abs_bot_bs_alpha_cons_if; eauto 3 with slow.
              apply diff_abs_bot_bterms_implies_diff_abs_bot_bs_alpha.
              unfold diff_abs_bot_bterms, br_bterms, br_list; dands; auto.

            * apply hasvalue_like_ncan_fst in hv.
              csunf Heqc; allsimpl; ginv.
              eapply hasvalue_like_compute_step in hv;
                [|csunf;simpl;auto].
              unfold apply_bterm in hv; allsimpl.
              rewrite lsubst_lsubst_aux in hv; allsimpl; auto.
              boolvar.
              apply not_hasvalue_like_vbot in hv; tcsp.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv;
            invdiff.

            * csunf; simpl; auto.
              eexists; dands; eauto.
              apply diff_abs_bot_alpha_atom_eq; eauto 3 with slow.

              { apply diff_abs_bot_alpha_lsubst; simpl; eauto 3 with slow. }

              { apply diff_abs_bot_alpha_exc; eauto 3 with slow. }

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.
              eexists; dands; eauto.
              apply implies_diff_abs_bot_alpha_oterm.
              apply diff_abs_bot_bterms_implies_diff_abs_bot_bs_alpha.
              unfold diff_abs_bot_bterms, br_bterms, br_list; dands; auto.

          + SSCase "Abs".

            csunf comp; allsimpl; ginv.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv; invdiff.

        - csunf; simpl; boolvar; auto.
          eexists; dands; eauto 3 with slow.

        - rewrite compute_step_fresh_if_isvalue_like2; simpl; eauto 3 with slow.
          eexists; dands; eauto 3 with slow.

        - rewrite compute_step_fresh_if_isnoncan_like; simpl; eauto 3 with slow.

          allrw @wf_fresh_iff.
          pose proof (compute_step_subst_utoken
                        [] t x
                        [(n,mk_utoken (get_fresh_atom t))]) as ch.
          autorewrite with slow in *; allsimpl.
          repeat (autodimp ch hyp); eauto 3 with slow;[].
          exrepnd.
          allrw disjoint_singleton_l.

          pose proof (fresh_atom o (get_utokens t ++ get_utokens t2)) as fa; exrepnd.
          allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a.

          pose proof (ch0 [(n,mk_utoken a)]) as ch'; allsimpl; clear ch0.
          autorewrite with slow in *; allsimpl.
          repeat (autodimp ch' hyp); eauto 3 with slow;[]; exrepnd.

          pose proof (hasvalue_like_fresh_implies [] a n t) as hv1.
          repeat (autodimp hv1 hyp).
          { eapply hasvalue_like_if_compute_step;
            [|rewrite computation2.compute_step_fresh_if_isnoncan_like;
               simpl; auto; rewrite comp2;simpl;reflexivity].
            auto. }
          applydup @hasvalue_like_compute_step in ch'1 as hv2; auto;[].

          pose proof (ind t (subst t n (mk_utoken a)) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }

          applydup (q (subst t2 n (mk_utoken a))) in ch'1 as comp'; clear q; eauto 4 with slow;
          [|repeat unfsubst; apply diff_abs_bot_lsubst_aux; simpl; eauto 3 with slow].
          exrepnd; allsimpl.

          pose proof (compute_step_subst_utoken [] t2 u' [(n,mk_utoken a)]) as ch''.
          autorewrite with slow in *; allsimpl.
          repeat (autodimp ch'' hyp); eauto 3 with slow.
          exrepnd.

          pose proof (ch''0 [(n,mk_utoken (get_fresh_atom t2))]) as ch'''; clear ch''0.
          autorewrite with slow in *; allsimpl.
          repeat (autodimp ch''' hyp); eauto 3 with slow.
          exrepnd.

          allrw @fold_subst.
          rewrite ch'''1; simpl.
          eexists; dands; eauto.
          apply diff_abs_bot_alpha_fresh.

          assert (!LIn (get_fresh_atom t2) (get_utokens w0)) as ni1.
          {
            intro i.
            apply ch''4 in i.
            apply get_fresh_atom_prop in i; tcsp.
          }

          assert (!LIn a (get_utokens w)) as ni2.
          {
            intro i.
            apply ch4 in i; auto.
          }

          assert (!LIn a (get_utokens w0)) as ni3.
          {
            intro i.
            apply ch''4 in i; auto.
          }

          eapply diff_abs_bot_alpha_l;
            [apply alpha_eq_subst_utokens_same;exact ch1|].
          eapply diff_abs_bot_alpha_r;
            [|apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact ch'''0].

          eapply diff_abs_bot_alpha_l;
            [apply simple_alphaeq_subst_utokens_subst;auto|].
          eapply diff_abs_bot_alpha_r;
            [|apply alpha_eq_sym;apply simple_alphaeq_subst_utokens_subst;auto].

          pose proof (simple_alphaeq_subst_utokens_subst w n a) as aeq1.
          autodimp aeq1 hyp.
          pose proof (simple_alphaeq_subst_utokens_subst w0 n a) as aeq2.
          autodimp aeq2 hyp.
          eapply diff_abs_bot_alpha_l;[apply alpha_eq_sym;exact aeq1|].
          eapply diff_abs_bot_alpha_r;[|exact aeq2].
          eapply diff_abs_bot_alpha_l;
            [apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact ch'0|].
          eapply diff_abs_bot_alpha_r;
            [|apply alpha_eq_subst_utokens_same;exact ch''1].
          apply diff_abs_bot_alpha_subst_utokens.
          eauto 3 with slow.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.
      invdiff.
      csunf; simpl.
      eexists; dands; eauto 3 with slow.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.
      unfold found_entry in comp0; allsimpl; ginv.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
