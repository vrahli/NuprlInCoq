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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand
           Vincent Rahli
           Mark Bickford

*)


Require Export list.
Require Export sequents.


(** substitute_hyp applies a substitution to the type of an hypothesis *)
Definition lsubst_hyp {o} (sub : (@Substitution o)) (h : hypothesis) : hypothesis :=
  match h with
  | {| hvar := hv; hidden := hi; htyp := ht; lvl := l |} =>
      {| hvar := hv; hidden := hi; htyp := lsubst ht sub; lvl := l |}
  end.

(** substitute_hyps applies a substitution to all the types of a list of
 * hypotheses. *)
Fixpoint lsubst_hyps {o} (sub : (@Substitution o)) (hs : barehypotheses) : barehypotheses :=
  match hs with
    | [] => []
    | h :: hs => lsubst_hyp sub h :: lsubst_hyps sub hs
  end.

Lemma is_nh_lsubst_hyp  {o} :
  forall sub a,
    is_nh (@lsubst_hyp o sub a) = is_nh a.
Proof.
  intros.
  destruct a; simpl; sp.
Qed.
Hint Rewrite @is_nh_lsubst_hyp : core.

Lemma lsubst_hyp_nil_sub {o} :
  forall h, @lsubst_hyp o [] h = h.
Proof.
  intro; unfold lsubst_hyp.
  destruct h.
  rewrite lsubst_nil; auto.
Qed.
Hint Rewrite @lsubst_hyp_nil_sub : core.

Lemma lsubst_hyps_nil_sub {o} :
  forall hs, @lsubst_hyps o [] hs = hs.
Proof.
  induction hs; simpl; auto.
  repeat (rewrite IHhs).
  rewrite lsubst_hyp_nil_sub; auto.
Qed.
Hint Rewrite @lsubst_hyps_nil_sub : core.

Lemma lsubst_hyps_snoc {o} :
  forall sub hs h, @lsubst_hyps o sub (snoc hs h) = snoc (lsubst_hyps sub hs) (lsubst_hyp sub h).
Proof.
  induction hs; simpl; auto; intros.
  repeat (rewrite IHhs); auto.
Qed.
Hint Rewrite @lsubst_hyps_snoc : core.

Lemma lsubst_hyps_cons {o} :
  forall sub h hs,
    @lsubst_hyps o sub (h :: hs) = lsubst_hyp sub h :: lsubst_hyps sub hs.
Proof.
  simpl; auto.
Qed.
Hint Rewrite @lsubst_hyps_cons : core.

Lemma mk_hs_subst_lsubst_hyps {o} :
  forall ts sub hs,
    mk_hs_subst ts (@lsubst_hyps o sub hs) = mk_hs_subst ts hs.
Proof.
  induction ts; simpl; intros; auto.
  destruct hs; simpl; auto.
  rewrite IHts.
  destruct h; simpl; auto.
Qed.
Hint Rewrite @mk_hs_subst_lsubst_hyps : core.

Lemma hvar_lsubst_hyp {o} :
  forall sub a,
    hvar (@lsubst_hyp o sub a) = hvar a.
Proof.
  destruct a; sp.
Qed.
Hint Rewrite @hvar_lsubst_hyp : core.

Lemma htyp_lsubst_hyp {o} :
  forall sub a,
    htyp (@lsubst_hyp o sub a) = lsubst (htyp a) sub.
Proof.
  destruct a; sp.
Qed.
Hint Rewrite @htyp_lsubst_hyp : core.

Lemma lvl_lsubst_hyp {o} :
  forall sub a,
    lvl (@lsubst_hyp o sub a) = lvl a.
Proof.
  destruct a; sp.
Qed.
Hint Rewrite @lvl_lsubst_hyp : core.

Lemma vars_hyps_lsubst_hyps {o} :
  forall sub hs,
    vars_hyps (@lsubst_hyps o sub hs) = vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  rewrite IHhs.
  rewrite hvar_lsubst_hyp; sp.
Qed.
Hint Rewrite @vars_hyps_lsubst_hyps : core.

Lemma nh_vars_hyps_lsubst_hyps {o} :
  forall sub hs,
    nh_vars_hyps (@lsubst_hyps o sub hs) = nh_vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  repeat (rewrite nh_vars_hyps_cons).
  rewrite IHhs.
  rewrite is_nh_lsubst_hyp.
  rewrite hvar_lsubst_hyp; sp.
Qed.
Hint Rewrite @nh_vars_hyps_lsubst_hyps : core.

Lemma length_lsubst_hyps {o} :
  forall sub hs,
    length (@lsubst_hyps o sub hs) = length hs.
Proof.
  induction hs; simpl; sp.
Qed.
Hint Rewrite @length_lsubst_hyps : core.


Lemma substitute_hyps_as_lsubst_hyps {o} :
  forall (sub : @CSub o) H,
    substitute_hyps sub H = lsubst_hyps (csub2sub sub) H.
Proof.
  induction H; simpl; tcsp; allrw; tcsp.
Qed.

Definition alpha_eq_hyp {o} (h1 h2 : @hypothesis o) :=
  alpha_eq (htyp h1) (htyp h2).

Inductive alpha_eq_hyps {o} : @barehypotheses o -> @barehypotheses o -> Type :=
| aeq_hs_nil : alpha_eq_hyps [] []
| aeq_hs_cons :
    forall h1 h2 hs1 hs2,
      alpha_eq_hyp h1 h2
      -> alpha_eq_hyps hs1 hs2
      -> alpha_eq_hyps (h1 :: hs1) (h2 :: hs2).
Hint Constructors alpha_eq_hyps.

Lemma combine_lsubst_hyps_aeq {o} :
  forall (sub1 sub2 : @Sub o) H,
    alpha_eq_hyps
      (lsubst_hyps sub2 (lsubst_hyps sub1 H))
      (lsubst_hyps (lsubst_sub sub1 sub2 ++ sub2) H).
Proof.
  induction H; allsimpl; tcsp.
  constructor; auto.
  destruct a; unfold alpha_eq_hyp; simpl.
  apply combine_sub_nest.
Qed.

Lemma alpha_eq_hyp_trans {o} :
  forall (h1 h2 h3 : @hypothesis o),
    alpha_eq_hyp h1 h2
    -> alpha_eq_hyp h2 h3
    -> alpha_eq_hyp h1 h3.
Proof.
  introv aeq1 aeq2.
  destruct h1, h2, h3.
  allunfold @alpha_eq_hyp; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_hyp_trans : slow.

Lemma alpha_eq_hyps_trans {o} :
  forall (hs1 hs2 hs3 : @bhyps o),
    alpha_eq_hyps hs1 hs2
    -> alpha_eq_hyps hs2 hs3
    -> alpha_eq_hyps hs1 hs3.
Proof.
  induction hs1; introv aeq1 aeq2.
  - inversion aeq1; subst.
    inversion aeq2; subst; auto.
  - inversion aeq1 as [|? ? ? ? a1 a2]; subst; clear aeq1.
    inversion aeq2 as [|? ? ? ? a3 a4]; subst; clear aeq2.
    constructor; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_hyps_trans : slow.

Lemma alpha_eq_hyp_refl {o} :
  forall (h : @hypothesis o),
    alpha_eq_hyp h h.
Proof.
  introv.
  destruct h.
  allunfold @alpha_eq_hyp; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_hyp_refl : slow.

Lemma alpha_eq_hyps_refl {o} :
  forall (hs : @bhyps o),
    alpha_eq_hyps hs hs.
Proof.
  induction hs; auto.
  constructor; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_hyps_refl : slow.

Lemma lsubst_mk_pair {o} :
  forall (a b : @NTerm o) sub,
    cl_sub sub
    -> lsubst (mk_pair a b) sub = mk_pair (lsubst a sub) (lsubst b sub).
Proof.
  introv cl.
  repeat unflsubst; simpl; autorewrite with slow; auto.
Qed.

Lemma lsubst_mk_apply {o} :
  forall (a b : @NTerm o) sub,
    cl_sub sub
    -> lsubst (mk_apply a b) sub = mk_apply (lsubst a sub) (lsubst b sub).
Proof.
  introv cl.
  repeat unflsubst; simpl; autorewrite with slow; auto.
Qed.

Lemma lsubst_aux_snoc_not_in {o} :
  forall (t : @NTerm o) v u s,
    !LIn v (free_vars t)
    -> lsubst_aux t (snoc s (v,u)) = lsubst_aux t s.
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case ; introv nit; allsimpl; auto.

  - Case "vterm".
    allrw not_over_or; repnd; GC.
    allrw @sub_find_snoc.
    remember (sub_find s x) as sf; symmetry in Heqsf; destruct sf; auto.
    boolvar; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl; f_equal.
    rw @sub_filter_snoc; boolvar; tcsp.
    eapply ind; eauto.
    intro j; destruct nit.
    rw lin_flat_map; eexists; dands; eauto.
    simpl; rw in_remove_nvars; sp.
Qed.

Lemma cl_lsubst_snoc_not_in {o} :
  forall (t : @NTerm o) v u s,
    cl_sub s
    -> closed u
    -> !LIn v (free_vars t)
    -> lsubst t (snoc s (v,u)) = lsubst t s.
Proof.
  introv cl1 cl2 nit.
  repeat unflsubst.
  apply lsubst_aux_snoc_not_in; auto.
Qed.

Lemma cl_lsubst_var_snoc_in {o} :
  forall v u (s : @Sub o),
    cl_sub s
    -> closed u
    -> !LIn v (dom_sub s)
    -> lsubst (mk_var v) (snoc s (v,u)) = u.
Proof.
  introv cl1 cl2 ni.
  repeat unflsubst.
  simpl.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto.
  boolvar; tcsp.
Qed.

Lemma ext_alpha_eq_subst_subset {o} :
  forall vs1 vs2 (sub1 sub2 : @Sub o),
    subset vs2 vs1
    -> ext_alpha_eq_subs vs1 sub1 sub2
    -> ext_alpha_eq_subs vs2 sub1 sub2.
Proof.
  introv ss ext.
  introv i; apply ext.
  apply ss; auto.
Qed.

Lemma alpha_eq_hyps_lsubst_if_ext_eq {o} :
  forall (hs1 hs2 : @bhyps o) (sub1 sub2 : Sub),
    alpha_eq_hyps hs1 hs2
    -> ext_alpha_eq_subs (hyps_free_vars hs1) sub1 sub2
    -> alpha_eq_hyps (lsubst_hyps sub1 hs1) (lsubst_hyps sub2 hs2).
Proof.
  induction hs1; introv aeq1 aeq2.
  - inversion aeq1; subst; simpl; auto.
  - inversion aeq1 as [|? ? ? ? a1 a2]; subst; clear aeq1; simpl.
    constructor.
    + destruct a, h2; allunfold @alpha_eq_hyp; allsimpl.
      apply alpha_eq_lsubst_if_ext_eq; auto.
      unfold hyp_free_vars in aeq2; allsimpl.
      eapply ext_alpha_eq_subst_subset;[|exact aeq2]; eauto 3 with slow.
    + apply IHhs1; auto; allsimpl.
      eapply ext_alpha_eq_subst_subset;[|exact aeq2]; eauto 3 with slow.
Qed.

Definition cequiv_ext {o} lib (a b : @NTerm o) :=
  in_ext lib (fun lib => Cast (cequiv lib a b)).

Definition cequiv_hyp {o} lib (h1 h2 : @hypothesis o) :=
  cequiv_ext lib (htyp h1) (htyp h2).

Inductive cequiv_hyps {o} (lib : library) : @barehypotheses o -> @barehypotheses o -> Type :=
| ceq_hs_nil : cequiv_hyps lib [] []
| ceq_hs_cons :
    forall h1 h2 hs1 hs2,
      cequiv_hyp lib h1 h2
      -> cequiv_hyps lib hs1 hs2
      -> cequiv_hyps lib (h1 :: hs1) (h2 :: hs2).
Hint Constructors cequiv_hyps.

Definition cequiv_open_ext {o} lib (a b : @NTerm o) :=
  in_ext lib (fun lib => Cast (cequiv_open lib a b)).

Definition cequiv_open_hyp {o} lib (h1 h2 : @hypothesis o) :=
  cequiv_open_ext lib (htyp h1) (htyp h2).

Inductive cequiv_open_hyps {o} (lib : library) : @barehypotheses o -> @barehypotheses o -> Type :=
| ceq_open_hs_nil : cequiv_open_hyps lib [] []
| ceq_open_hs_cons :
    forall h1 h2 hs1 hs2,
      cequiv_open_hyp lib h1 h2
      -> cequiv_open_hyps lib hs1 hs2
      -> cequiv_open_hyps lib (h1 :: hs1) (h2 :: hs2).
Hint Constructors cequiv_open_hyps.

Definition isprog_hyp {o} (h : @hypothesis o) := isprog (htyp h).

Definition isprog_hyps {o} (hs : @bhyps o) :=
  forall h, LIn h hs -> isprog_hyp h.

Definition wf_hyp {o} (h : @hypothesis o) := wf_term (htyp h).

Definition wf_hyps {o} (hs : @bhyps o) :=
  forall h, LIn h hs -> wf_hyp h.

Lemma isprog_hyps_cons {o} :
  forall (h : @hypothesis o) hs,
    isprog_hyps (h :: hs) <=> (isprog_hyp h # isprog_hyps hs).
Proof.
  introv.
  unfold isprog_hyps; split; intro i; allsimpl; dands; tcsp.
  introv j; repndors; subst; tcsp.
Qed.

Lemma wf_hyps_cons {o} :
  forall (h : @hypothesis o) hs,
    wf_hyps (h :: hs) <=> (wf_hyp h # wf_hyps hs).
Proof.
  introv.
  unfold wf_hyps; split; intro i; allsimpl; dands; tcsp.
  introv j; repndors; subst; tcsp.
Qed.

Lemma alpha_eq_hyp_implies_cequiv_open_hyp {o} :
  forall lib (h1 h2 : @hypothesis o),
    wf_hyp h1
    -> wf_hyp h2
    -> alpha_eq_hyp h1 h2
    -> cequiv_open_hyp lib h1 h2.
Proof.
  introv isp1 isp2 aeq.
  destruct h1, h2.
  unfold alpha_eq_hyp in aeq; allsimpl.
  unfold cequiv_open_hyp; simpl.
  introv x; spcast.
  allunfold @wf_hyp; allsimpl.
  apply alpha_implies_cequiv_open; eauto 3 with slow.
Qed.

Lemma alpha_eq_hyps_implies_cequiv_open_hyps {o} :
  forall lib (hs1 hs2 : @bhyps o),
    wf_hyps hs1
    -> wf_hyps hs2
    -> alpha_eq_hyps hs1 hs2
    -> cequiv_open_hyps lib hs1 hs2.
Proof.
  induction hs1; introv isp1 isp2 aeq.
  - inversion aeq; auto.
  - inversion aeq as [|? ? ? ? a1 a2]; clear aeq; subst.
    allrw @wf_hyps_cons; repnd.
    constructor; tcsp.
    apply alpha_eq_hyp_implies_cequiv_open_hyp; auto.
Qed.

Lemma cequiv_hyps_snoc_implies {o} :
  forall lib (hs1 hs : @bhyps o) h1,
    cequiv_hyps lib (snoc hs1 h1) hs
    -> {hs2 : bhyps
        & {h2 : hypothesis
        & hs = snoc hs2 h2
        # cequiv_hyps lib hs1 hs2
        # cequiv_hyp lib h1 h2 }}.
Proof.
  induction hs1; introv ceq; allsimpl.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    inversion ceq2; subst; clear ceq2.
    exists ([] : @bhyps o) h2; simpl; dands; auto.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    apply IHhs1 in ceq2; exrepnd; subst.
    exists (h2 :: hs0) h0; simpl; dands; auto.
Qed.

Lemma alpha_eq_hyps_snoc_implies {o} :
  forall (hs1 hs : @bhyps o) h1,
    alpha_eq_hyps (snoc hs1 h1) hs
    -> {hs2 : bhyps
        & {h2 : hypothesis
        & hs = snoc hs2 h2
        # alpha_eq_hyps hs1 hs2
        # alpha_eq_hyp h1 h2 }}.
Proof.
  induction hs1; introv ceq; allsimpl.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    inversion ceq2; subst; clear ceq2.
    exists ([] : @bhyps o) h2; simpl; dands; auto.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    apply IHhs1 in ceq2; exrepnd; subst.
    exists (h2 :: hs0) h0; simpl; dands; auto.
Qed.

Lemma cequiv_open_hyps_snoc_implies {o} :
  forall lib (hs1 hs : @bhyps o) h1,
    cequiv_open_hyps lib (snoc hs1 h1) hs
    -> {hs2 : bhyps
        & {h2 : hypothesis
        & hs = snoc hs2 h2
        # cequiv_open_hyps lib hs1 hs2
        # cequiv_open_hyp lib h1 h2 }}.
Proof.
  induction hs1; introv ceq; allsimpl.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    inversion ceq2; subst; clear ceq2.
    exists ([] : @bhyps o) h2; simpl; dands; auto.
  - inversion ceq as [|? ? ? ? ceq1 ceq2]; subst; clear ceq.
    apply IHhs1 in ceq2; exrepnd; subst.
    exists (h2 :: hs0) h0; simpl; dands; auto.
Qed.

Lemma wf_hyps_snoc {o} :
  forall (hs : @bhyps o) h,
    wf_hyps (snoc hs h) <=> (wf_hyps hs # wf_hyp h).
Proof.
  introv; unfold wf_hyps; split; introv q; allsimpl; repnd; dands; tcsp.
  - introv j; apply q; rw in_snoc; sp.
  - apply q; rw in_snoc; sp.
  - introv j; allrw in_snoc; repndors; subst; tcsp.
Qed.

Hint Resolve cequiv_subst_csub2sub_refl : slow.

Lemma alpha_eq_hyp_preserves_wf {o} :
  forall (h1 h2 : @hypothesis o),
    alpha_eq_hyp h1 h2
    -> wf_hyp h1
    -> wf_hyp h2.
Proof.
  introv aeq wf.
  destruct h1, h2.
  allunfold @alpha_eq_hyp; allunfold @wf_hyp; allsimpl.
  eauto 3 with slow.
Qed.

Lemma alpha_eq_hyp_preserves_cover_vars {o} :
  forall (h1 h2 : @hypothesis o) s,
    alpha_eq_hyp h1 h2
    -> cover_vars (htyp h1) s
    -> cover_vars (htyp h2) s.
Proof.
  introv aeq cov.
  destruct h1, h2.
  allunfold @alpha_eq_hyp; allsimpl.
  allunfold @cover_vars.
  apply alphaeq_preserves_free_vars in aeq; rw <- aeq; auto.
Qed.

Lemma similarity_preserves_alpha_eq_hyps {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    vars_hyps hs1 = vars_hyps hs2
    -> alpha_eq_hyps hs1 hs2
    -> similarity lib s1 s2 hs1
    -> similarity lib s1 s2 hs2.
Proof.
  induction hs1 using rev_list_indT; introv eqvs aeq sim.
  - inversion aeq; subst; auto.
  - inversion sim as [|? ? ? ? ? ? wf cov equ sim'];
    ginv; subst; cpx; clear sim.
    allapply @alpha_eq_hyps_snoc_implies; exrepnd; subst.
    allrw @vars_hyps_snoc; cpx.
    dup aeq1 as cov'.
    applydup @alpha_eq_hyp_preserves_wf in aeq1 as wf'; auto.
    eapply alpha_eq_hyp_preserves_cover_vars in cov';[|eauto].
    apply similarity_snoc.
    rw e0.

    exists s0 s3 t1 t2 wf' cov'; dands; auto.
    eapply alphaeqc_preserving_equality;[eauto|].
    unfold alphaeqc, lsubstc; simpl.
    apply lsubst_alpha_congr2; auto.
Qed.

Lemma cequiv_subst_implies_prog_sub {o} :
  forall lib (sub1 sub2 : @Sub o),
    cequiv_subst lib sub1 sub2
    -> (prog_sub sub1 # prog_sub sub2).
Proof.
  induction sub1; introv ceq.
  - inversion ceq; subst; dands; eauto 3 with slow.
  - inversion ceq as [|? ? ? ? ? c1 c2]; subst; clear ceq.
    allrw @prog_sub_cons.
    applydup @cequiv_isprogram in c1; repnd.
    apply IHsub1 in c2; sp.
Qed.

Inductive approx_open_sub {p} (lib : @library p) : @Sub p -> @Sub p -> Type :=
  | apr_op_sub_nil : approx_open_sub lib [] []
  | apr_op_sub_cons :
      forall v t1 t2 s1 s2,
        approx_open lib t1 t2
        -> approx_open_sub lib s1 s2
        -> approx_open_sub lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors approx_open_sub.

Inductive approx_sub {p} (lib : @library p) : @Sub p -> @Sub p -> Type :=
  | apr_sub_nil : approx_sub lib [] []
  | apr_sub_cons :
      forall v t1 t2 s1 s2,
        approx lib t1 t2
        -> approx_sub lib s1 s2
        -> approx_sub lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors approx_sub.

Lemma approx_sub_implies_prog_sub {o} :
  forall lib (sub1 sub2 : @Sub o),
    approx_sub lib sub1 sub2 -> (prog_sub sub1 # prog_sub sub2).
Proof.
  induction sub1; introv apr.
  - inversion apr; subst; dands; eauto 3 with slow.
  - inversion apr as [|? ? ? ? ? a1 a2]; subst; clear apr.
    allrw @prog_sub_cons.
    apply approx_isprog in a1; repnd.
    apply IHsub1 in a2; repnd.
    dands; eauto 3 with slow.
Qed.

Lemma approx_sub_iff_sub_range_rel {o} :
  forall lib (sub1 sub2 : @Sub o),
    approx_sub lib sub1 sub2
    <=> sub_range_rel (approx lib) sub1 sub2.
Proof.
  induction sub1; introv; split; intro h.
  - inversion h; subst; simpl; auto.
  - destruct sub2; allsimpl; tcsp.
  - inversion h as [|? ? ? ? ? a1 a2]; subst; clear h.
    simpl; dands; auto.
    apply IHsub1; auto.
  - allsimpl.
    destruct a.
    destruct sub2; tcsp.
    destruct p; repnd; subst.
    apply IHsub1 in h; auto.
Qed.

Lemma lsubst_approx_congr2 {o} :
  forall lib (t1 t2 : @NTerm o) (sub1 sub2 : Sub),
    approx_sub lib sub1 sub2
    -> approx_open lib t1 t2
    -> isprogram (lsubst t1 sub1)
    -> isprogram (lsubst t2 sub2)
    -> approx lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv apr1 apr2 isp1 isp2.
  apply lsubst_approx_congr; auto.
  apply approx_sub_iff_sub_range_rel; auto.
Qed.

Lemma implies_approx_sub_app {o} :
  forall lib (sub1 sub2 sub3 sub4 : @Sub o),
    approx_sub lib sub1 sub2
    -> approx_sub lib sub3 sub4
    -> approx_sub lib (sub1 ++ sub3) (sub2 ++ sub4).
Proof.
  induction sub1; introv apr1 apr2; allsimpl.
  - inversion apr1; subst; auto.
  - inversion apr1 as [|? ? ? ? ? a1 a2]; subst; clear apr1; simpl.
    constructor; auto.
Qed.

Lemma approx_sub_refl {o} :
  forall lib (sub : @Sub o),
    prog_sub sub
    -> approx_sub lib sub sub.
Proof.
  induction sub; introv prs; allsimpl; eauto 3 with slow.
  destruct a.
  allrw @prog_sub_cons; repnd.
  constructor; eauto 3 with slow.
Qed.

Lemma approx_open_lsubst_congr2 {o} :
  forall lib (t : @NTerm o) sub1 sub2,
    wf_term t
    -> approx_sub lib sub1 sub2
    -> approx_open lib (lsubst t sub1) (lsubst t sub2).
Proof.
  introv wft apr.
  apply approx_open_simpler_equiv.
  applydup @approx_sub_implies_prog_sub in apr; repnd.

  unfold simpl_olift; dands; auto;
  try (apply lsubst_wf_if_eauto; eauto 3 with slow).

  introv ps isp1 isp2.

  dup isp1 as isp1'.
  dup isp2 as isp2'.

  eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;apply combine_sub_nest|].
  eapply approx_alpha_rw_r_aux;[apply alpha_eq_sym;apply combine_sub_nest|].
  eapply alpha_prog_eauto in isp1';[|apply combine_sub_nest].
  eapply alpha_prog_eauto in isp2';[|apply combine_sub_nest].

  repeat (rw @lsubst_sub_trivial; eauto 2 with slow;
          [|rw @sub_free_vars_if_cl_sub; eauto 2 with slow]).
  repeat (rw @lsubst_sub_trivial in isp1'; eauto 2 with slow;
          [|rw @sub_free_vars_if_cl_sub; eauto 2 with slow]).
  repeat (rw @lsubst_sub_trivial in isp2'; eauto 2 with slow;
          [|rw @sub_free_vars_if_cl_sub; eauto 2 with slow]).

  apply lsubst_approx_congr2; eauto 3 with slow.
  apply implies_approx_sub_app; auto.
  apply approx_sub_refl; auto.
Qed.

Lemma cequiv_subst_as_approx_sub {o} :
  forall lib (sub1 sub2 : @Sub o),
    cequiv_subst lib sub1 sub2 <=> (approx_sub lib sub1 sub2 # approx_sub lib sub2 sub1).
Proof.
  induction sub1; introv; split; intro h; repnd.
  - inversion h; subst; dands; auto.
  - inversion h0; subst; auto.
  - inversion h as [|? ? ? ? ? c1 c2]; subst; clear h.
    applydup @cequiv_sym in c1 as c3.
    apply cequiv_le_approx in c1.
    apply cequiv_le_approx in c3.
    apply IHsub1 in c2; repnd.
    dands; constructor; auto.
  - inversion h as [|? ? ? ? ? a1 a2]; subst; clear h.
    inversion h0 as [|? ? ? ? ? a3 a4]; subst; clear h0.
    constructor;[split; auto|].
    apply IHsub1; sp.
Qed.

Lemma cequiv_open_lsubst_same_term {o} :
  forall lib (t : @NTerm o) sub1 sub2,
    wf_term t
    -> cequiv_subst lib sub1 sub2
    -> cequiv_open lib (lsubst t sub1) (lsubst t sub2).
Proof.
  introv wf ceq.
  apply cequiv_subst_as_approx_sub in ceq; repnd.
  apply olift_approx_cequiv; apply approx_open_lsubst_congr2; auto.
Qed.

Definition cequiv_subst_ext {o} lib (s1 s2 : @Sub o) :=
  in_ext lib (fun lib => Cast (cequiv_subst lib s1 s2)).

Lemma cequiv_open_hyp_same_hyps {o} :
  forall lib (h : @hypothesis o) sub1 sub2,
    wf_hyp h
    -> cequiv_subst_ext lib sub1 sub2
    -> cequiv_open_hyp lib (lsubst_hyp sub1 h) (lsubst_hyp sub2 h).
Proof.
  introv wf ceq.
  destruct h; unfold cequiv_open_hyp; simpl.
  unfold wf_hyp in wf; allsimpl.
  introv x; apply ceq in x; spcast.
  apply cequiv_open_lsubst_same_term; auto.
Qed.

Lemma cequiv_open_hyps_same_hyps {o} :
  forall lib (hs : @bhyps o) sub1 sub2,
    wf_hyps hs
    -> cequiv_subst_ext lib sub1 sub2
    -> cequiv_open_hyps lib (lsubst_hyps sub1 hs) (lsubst_hyps sub2 hs).
Proof.
  induction hs; introv wf ceq; simpl; auto.
  allrw @wf_hyps_cons; repnd.
  constructor; try (apply IHhs;auto).
  apply cequiv_open_hyp_same_hyps; auto.
Qed.

Definition eq_free_vars_hyp {o} (h1 h2 : @hypothesis o) :=
  free_vars (htyp h1) = free_vars (htyp h2).

Definition eq_free_vars_hyps {o} (hs1 hs2 : @bhyps o) :=
  forall h1 h2, LIn (h1,h2) (combine hs1 hs2) -> eq_free_vars_hyp h1 h2.

Lemma eq_vars_hyps_implies_eq_length {o} :
  forall (hs1 hs2 : @bhyps o),
    vars_hyps hs1 = vars_hyps hs2
    -> length hs1 = length hs2.
Proof.
  introv e.
  rw <- @vars_hyps_length; rw e.
  rw @vars_hyps_length; auto.
Qed.

Lemma combine_snoc {T} :
  forall (l1 l2 : list T) a1 a2,
    length l1 = length l2
    -> combine (snoc l1 a1) (snoc l2 a2)
       = snoc (combine l1 l2) (a1,a2).
Proof.
  induction l1; introv len; allsimpl; cpx.
  destruct l2; allsimpl; cpx.
  rw IHl1; auto.
Qed.

Lemma eq_free_vars_hyps_snoc {o} :
  forall (hs1 hs2 : @bhyps o) h1 h2,
    length hs1 = length hs2
    -> (eq_free_vars_hyps (snoc hs1 h1) (snoc hs2 h2)
        <=> (eq_free_vars_hyps hs1 hs2 # eq_free_vars_hyp h1 h2)).
Proof.
  introv len; split; intro h; repnd; dands; tcsp.
  - introv i.
    apply h.
    rw @combine_snoc; auto.
    rw in_snoc; sp.
  - apply h.
    rw @combine_snoc; auto.
    rw in_snoc; sp.
  - introv i.
    rw @combine_snoc in i; auto.
    allrw in_snoc; repndors; ginv.
Qed.

Lemma similarity_preserves_cequiv_open_hyps {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    wf_hyps hs2
    -> eq_free_vars_hyps hs1 hs2
    -> vars_hyps hs1 = vars_hyps hs2
    -> cequiv_open_hyps lib hs1 hs2
    -> similarity lib s1 s2 hs1
    -> similarity lib s1 s2 hs2.
Proof.
  induction hs1 using rev_list_indT; introv wf2 efvs vsh ceq sim; allsimpl.

  - destruct hs2; allsimpl; cpx.

  - inversion sim as [|? ? ? ? ? ? wf cov equ sim'];
      ginv; subst; cpx; clear sim.
    allapply @cequiv_open_hyps_snoc_implies; exrepnd; subst.
    allrw @vars_hyps_snoc; cpx.
    allrw @wf_hyps_snoc; repnd.
    allrw @hyps_free_vars_snoc.

    applydup @eq_vars_hyps_implies_eq_length in e as len.
    apply eq_free_vars_hyps_snoc in efvs; auto; repnd.

    eapply IHhs1 in ceq2; try (exact sim'); auto.

    dup cov as cov'.
    unfold cover_vars in cov'.
    rw efvs in cov'.

    apply similarity_snoc.
    rw e0.
    exists s0 s3 t1 t2 wf2 cov'; dands; auto.

    eapply cequivc_preserving_equality;[eauto|].

    introv x; apply ceq1 in x; spcast.
    unfold cequivc, lsubstc; simpl.
    apply lsubst_cequiv_congr; eauto 2 with slow;
      apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow;
        allrw @dom_csub_eq; allrw @cover_vars_eq;
          apply subvars_eq; auto.
Qed.

Lemma implies_wf_hyps_lsubst_hyps {o} :
  forall s (hs : @bhyps o),
    wf_hyps hs
    -> wf_sub s
    -> wf_hyps (lsubst_hyps s hs).
Proof.
  induction hs; introv wf1 wf2; simpl; auto.
  allrw @wf_hyps_cons; repnd; dands; tcsp.
  destruct a; allsimpl.
  allunfold @wf_hyp; allsimpl.
  apply lsubst_preserves_wf_term; auto.
Qed.

Lemma wf_hypotheses_implies_wf_hyps {o} :
  forall (hs : @bhyps o),
    wf_hypotheses hs -> wf_hyps hs.
Proof.
  induction hs using rev_list_ind; intro wf.
  - introv i; allsimpl; tcsp.
  - allrw @wf_hypotheses_snoc; repnd.
    apply IHhs in wf.
    apply wf_hyps_snoc; dands; auto.
    unfold wf_hyp.
    apply isprog_vars_implies_nt_wf in wf0; eauto 3 with slow.
Qed.

Lemma wf_hyps_app {o} :
  forall (hs1 hs2 : @bhyps o),
    wf_hyps (hs1 ++ hs2) <=> (wf_hyps hs1 # wf_hyps hs2).
Proof.
  introv; split; intro h; repnd; dands; introv i.
  - apply h; rw in_app_iff; sp.
  - apply h; rw in_app_iff; sp.
  - allrw in_app_iff; repndors.
    + apply h0; auto.
    + apply h; auto.
Qed.

Lemma lsubst_hyps_as_map {o} :
  forall s (hs : @bhyps o),
    lsubst_hyps s hs = map (fun h => lsubst_hyp s h) hs.
Proof.
  induction hs; introv; simpl; tcsp.
  rw IHhs; auto.
Qed.

Definition covered_csub {o} (sub1 : @Sub o) (sub2 : @CSub o) :=
  sub_range_sat sub1 (fun t => covered t (dom_csub sub2)).

Lemma covered_csub_nil {o} :
  forall (sub : @CSub o),
    covered_csub [] sub.
Proof.
  introv; unfold covered_csub, sub_range_sat; allsimpl; sp.
Qed.
Hint Resolve covered_csub_nil : slow.

Lemma covered_csub_cons {o} :
  forall v t (sub1 : @Sub o) sub2,
    covered_csub ((v,t) :: sub1) sub2
    <=> (covered t (dom_csub sub2) # covered_csub sub1 sub2).
Proof.
  unfold covered_csub, sub_range_sat; introv; split; intro k; repnd; dands; introv.
  - apply (k v t); simpl; sp.
  - intro i; apply (k v0 t0); simpl; sp.
  - intro i; simpl in i; dorn i; cpx.
    apply (k v0 t0); auto.
Qed.

Lemma covered_csub_cons_implies1 {o} :
  forall v t (s : @Sub o) cs,
    covered_csub ((v,t) :: s) cs -> cover_vars t cs.
Proof.
  introv h.
  allrw @covered_csub_cons; repnd.
  allrw @dom_csub_eq; auto.
Qed.

Lemma covered_csub_cons_implies2 {o} :
  forall v t (s : @Sub o) s',
    covered_csub ((v,t) :: s) s' -> covered_csub s s'.
Proof.
  introv h.
  allrw @covered_csub_cons; repnd.
  allrw @dom_csub_eq; auto.
Qed.

Lemma wf_sub_cons_implies1 {o} :
  forall v t (sub : @Sub o),
    wf_sub ((v, t) :: sub) -> wf_term t.
Proof.
  introv wf; apply wf_sub_cons_iff in wf; sp.
Qed.

Lemma wf_sub_cons_implies2 {o} :
  forall v t (sub : @Sub o),
    wf_sub ((v, t) :: sub) -> wf_sub sub.
Proof.
  introv wf; apply wf_sub_cons_iff in wf; sp.
Qed.

Fixpoint lsubstc_sub {o}
         (sub1 : @Sub o)
         (sub2 : CSub) :
  wf_sub sub1
  -> covered_csub sub1 sub2
  -> @CSub o :=
  match sub1 with
    | [] => fun wf cov => []
    | (v,t) :: s =>
      fun wf cov =>
        (v,lsubstc t (wf_sub_cons_implies1 v t s wf) sub2 (covered_csub_cons_implies1 v t s sub2 cov))
          :: lsubstc_sub s sub2 (wf_sub_cons_implies2 v t s wf) (covered_csub_cons_implies2 v t s sub2 cov)
  end.

Lemma dom_csub_lsubstc_sub {o} :
  forall (s : @Sub o) s1 w c,
    dom_csub (lsubstc_sub s s1 w c)
    = dom_sub s.
Proof.
  induction s; introv; simpl; auto.
  destruct a; simpl.
  rw IHs; auto.
Qed.
Hint Rewrite @dom_csub_lsubstc_sub : core.

Lemma eqset_progsub {o} :
  forall (t : @NTerm o) sub,
    prog_sub sub
    -> eqset (free_vars (lsubst t sub)) (remove_nvars (dom_sub sub) (free_vars t)).
Proof.
  introv ps.
  apply eqvars_is_eqset.
  apply eq_vars_progsub; auto.
Qed.

Lemma lsubst_sub_app_if_covered_csub {o} :
  forall (s : @Sub o) s1 s2,
    wf_sub s
    -> covered_csub s s1
    -> lsubst_sub s (csub2sub s1 ++ csub2sub s2)
       = lsubst_sub s (csub2sub s1).
Proof.
  induction s; introv wf cov; simpl; auto.
  destruct a.
  allrw @wf_sub_cons_iff; repnd.
  allrw @covered_csub_cons; repnd.
  rw IHs; auto.
  rw <- @prog_lsubst_app2; eauto 2 with slow.
  apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
  rw @dom_csub_eq.
  unfold covered in cov0; rw subvars_eq in cov0; auto.
Qed.

Lemma csub2sub_lsubstc_sub {o} :
  forall (s : @Sub o) s1 w c,
    csub2sub (lsubstc_sub s s1 w c)
    = lsubst_sub s (csub2sub s1).
Proof.
  induction s; introv; simpl; auto.
  destruct a; allsimpl.
  dup w as w'.
  allrw @wf_sub_cons_iff; repnd.
  dup c as c'.
  allrw @covered_csub_cons; repnd.
  rw IHs; auto.
Qed.

Lemma tequalityi_alphaeqc_l {o} :
forall lib n (a b c : @CTerm o),
  alphaeqc a b
  -> tequalityi lib n a c
  -> tequalityi lib n b c.
Proof.
  introv aeq teq.
  allunfold @tequalityi.
  eauto 3 with nequality.
Qed.
Hint Resolve tequalityi_alphaeqc_l : nequality.

Lemma tequalityi_alphaeqc_r {o} :
forall lib n (a b c : @CTerm o),
  alphaeqc b c
  -> tequalityi lib n a b
  -> tequalityi lib n a c.
Proof.
  introv aeq teq.
  allunfold @tequalityi.
  eauto 3 with nequality.
Qed.
Hint Resolve tequalityi_alphaeqc_r : nequality.

Lemma eqtypes_alphaeqc_l {o} :
  forall lib lvl (a b c : @CTerm o),
    alphaeqc a b
    -> eqtypes lib lvl a c
    -> eqtypes lib lvl b c.
Proof.
  introv aeq eqt.
  allunfold @eqtypes.
  destruct lvl; eauto 3 with nequality.
Qed.
Hint Resolve eqtypes_alphaeqc_l : nequality.

Lemma eqtypes_alphaeqc_r {o} :
  forall lib lvl (a b c : @CTerm o),
    alphaeqc b c
    -> eqtypes lib lvl a b
    -> eqtypes lib lvl a c.
Proof.
  introv aeq eqt.
  allunfold @eqtypes.
  destruct lvl; eauto 3 with nequality.
Qed.
Hint Resolve eqtypes_alphaeqc_r : nequality.

Lemma covered_csub_iff {o} :
  forall (s : @Sub o) s1,
    covered_csub s s1 <=> subset (sub_free_vars s) (dom_csub s1).
Proof.
  induction s; introv; simpl; split; intro h; eauto 3 with slow;
  destruct a; allsimpl; allrw @covered_csub_cons;
  allrw subset_app; repnd; dands; tcsp;
  try (apply IHs; tcsp);
  allunfold @covered; allrw subvars_eq; auto.
Qed.

Lemma sub_eq_hyps_snoc_subst {o} :
  forall lib hs (s1 s2 s3 s4 : @CSub o) s
         (wf : wf_sub s)
         (c1 : covered_csub s s1)
         (c2 : covered_csub s s2),
    sub_eq_hyps lib s1 s2 s3 s4 (lsubst_hyps s hs)
    <=> sub_eq_hyps lib (lsubstc_sub s s1 wf c1 ++ s1) (lsubstc_sub s s2 wf c2 ++ s2) s3 s4 hs.
Proof.
  induction hs using rev_list_ind; introv; simpl; split; intro h; tcsp;
  allrw @lsubst_hyps_snoc;
  try (complete (inversion h; subst; cpx)).

  - inversion h as [|? ? ? ? ? ? ? ? ? ? ? eqt seh]; cpx; clear h.
    autorewrite with slow core in *.

    apply (IHhs s1 s2 s0 s5 s wf c1 c2) in seh; clear IHhs.

    assert (wf_term (htyp a)) as wfa.
    { clear eqt seh.
      destruct a; allsimpl.
      apply lsubst_wf_term in w; auto. }

    assert (cover_vars (htyp a) ((lsubstc_sub s s1 wf c1 ++ s1) ++ s0)) as cov1.
    { clear eqt seh p2.
      destruct a; allsimpl.
      allrw @cover_vars_eq; allrw subvars_eq; introv i.
      allrw @dom_csub_app.
      autorewrite with core.
      rw <- app_assoc.
      eapply subset_eqset_l in p1;[|apply eqset_free_vars_disjoint].
      allrw subset_app; repnd.
      rw in_app_iff.
      destruct (in_deq _ deq_nvar x (dom_sub s)) as [d|d];[left;complete auto|right].
      apply p0.
      rw in_remove_nvars; sp. }

    assert (cover_vars (htyp a) ((lsubstc_sub s s2 wf c2 ++ s2) ++ s5)) as cov2.
    { clear eqt seh p1.
      destruct a; allsimpl.
      allrw @cover_vars_eq; allrw subvars_eq; introv i.
      allrw @dom_csub_app.
      autorewrite with core.
      rw <- app_assoc.
      eapply subset_eqset_l in p2;[|apply eqset_free_vars_disjoint].
      allrw subset_app; repnd.
      rw in_app_iff.
      destruct (in_deq _ deq_nvar x (dom_sub s)) as [d|d];[left;complete auto|right].
      apply p0.
      rw in_remove_nvars; sp. }

    apply (sub_eq_hyps_cons _ _ _ _ _ _ _ a hs wfa cov1 cov2); auto;[].

    clear seh.
    destruct a; allsimpl.

    assert (alphaeqc
              (lsubstc (lsubst htyp s) w (s1 ++ s0) p1)
              (lsubstc htyp wfa ((lsubstc_sub s s1 wf c1 ++ s1) ++ s0) cov1)) as aeq1.
    { unfold alphaeqc; simpl.
      unfold csubst; allrw <- @csub2sub_app.
      rw <- app_assoc.
      eapply alpha_eq_trans;[apply combine_sub_nest|].
      rw @lsubst_sub_app_if_covered_csub; auto.
      rw @csub2sub_lsubstc_sub; auto. }

    assert (alphaeqc
              (lsubstc (lsubst htyp s) w (s2 ++ s5) p2)
              (lsubstc htyp wfa ((lsubstc_sub s s2 wf c2 ++ s2) ++ s5) cov2)) as aeq2.
    { unfold alphaeqc; simpl.
      unfold csubst; allrw <- @csub2sub_app.
      rw <- app_assoc.
      eapply alpha_eq_trans;[apply combine_sub_nest|].
      rw @lsubst_sub_app_if_covered_csub; auto.
      rw @csub2sub_lsubstc_sub; auto. }

    eauto 3 with nequality.

  - inversion h as [|? ? ? ? ? ? ? ? ? ? ? eqt seh]; cpx; clear h.
    autorewrite with slow core in *.

    apply (IHhs s1 s2 s0 s5 s wf c1 c2) in seh; clear IHhs.

    assert (wf_term (htyp (lsubst_hyp s a))) as wfa.
    { clear eqt seh.
      destruct a; allsimpl.
      apply lsubst_preserves_wf_term; auto. }

    assert (cover_vars (htyp (lsubst_hyp s a)) (s1 ++ s0)) as cov1.
    { clear eqt seh p2.
      destruct a; allsimpl.
      allrw @cover_vars_eq; allrw subvars_eq; introv i.
      allrw @dom_csub_app.
      autorewrite with core in *.
      rw <- app_assoc in p1.
      apply eqset_free_vars_disjoint in i.
      allrw in_app_iff; allrw in_remove_nvars.
      repndors; repnd.
      - apply p1 in i0; allrw in_app_iff; tcsp.
      - apply in_sub_free_vars in i; exrepnd.
        apply in_sub_keep_first in i0; repnd.
        allrw @covered_csub_iff.
        left; apply c1.
        allapply @sub_find_some.
        apply in_sub_free_vars_iff; eexists; eexists; dands; eauto. }

    assert (cover_vars (htyp (lsubst_hyp s a)) (s2 ++ s5)) as cov2.
    { clear eqt seh p1.
      destruct a; allsimpl.
      allrw @cover_vars_eq; allrw subvars_eq; introv i.
      allrw @dom_csub_app.
      autorewrite with core in *.
      rw <- app_assoc in p2.
      apply eqset_free_vars_disjoint in i.
      allrw in_app_iff; allrw in_remove_nvars.
      repndors; repnd.
      - apply p2 in i0; allrw in_app_iff; tcsp.
      - apply in_sub_free_vars in i; exrepnd.
        apply in_sub_keep_first in i0; repnd.
        allrw @covered_csub_iff.
        left; apply c2.
        allapply @sub_find_some.
        apply in_sub_free_vars_iff; eexists; eexists; dands; eauto. }

    pose proof (sub_eq_hyps_cons lib t1 t2 _ _ _ _ _ (lsubst_hyps s hs) wfa cov1 cov2) as h.
    autorewrite with core slow in *.
    repeat (autodimp h hyp).

    clear seh.
    destruct a; allsimpl.

    assert (alphaeqc
              (lsubstc htyp w ((lsubstc_sub s s1 wf c1 ++ s1) ++ s0) p1)
              (lsubstc (lsubst htyp s) wfa (s1 ++ s0) cov1)) as aeq1.
    { unfold alphaeqc; simpl; apply alpha_eq_sym.
      unfold csubst; allrw <- @csub2sub_app.
      rw <- app_assoc.
      eapply alpha_eq_trans;[apply combine_sub_nest|].
      rw @lsubst_sub_app_if_covered_csub; auto.
      rw @csub2sub_lsubstc_sub; auto. }

    assert (alphaeqc
              (lsubstc htyp w ((lsubstc_sub s s2 wf c2 ++ s2) ++ s5) p2)
              (lsubstc (lsubst htyp s) wfa (s2 ++ s5) cov2)) as aeq2.
    { unfold alphaeqc; simpl; apply alpha_eq_sym.
      unfold csubst; allrw <- @csub2sub_app.
      rw <- app_assoc.
      eapply alpha_eq_trans;[apply combine_sub_nest|].
      rw @lsubst_sub_app_if_covered_csub; auto.
      rw @csub2sub_lsubstc_sub; auto. }

    eauto 3 with nequality.
Qed.

Lemma sub_eq_hyps_snoc_weak_dup1 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t1,
    LIn x (dom_csub s1)
    -> sub_eq_hyps lib s1 s2 s3 s4 hs
    -> sub_eq_hyps lib (snoc s1 (x, t1)) s2 s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nih seh;
  inversion seh; subst; cpx.

  assert (cover_vars (htyp a) (snoc s1 (x, t1) ++ s0))
    as p1' by (apply cover_vars_weak; sp).

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1') (p2 := p2); auto;[].

  pose proof (lsubstc_csubst_ex2 (htyp a) (snoc s1 (x, t1)) s0 w p1') as e.
  exrepnd.
  rw <- e1; clear e1.

  assert (wf_term (csubst (htyp a) s1)) as w1.
  { apply wf_term_csubst; sp. }
  assert (cover_vars (csubst (htyp a) s1) s0) as c1.
  { rw <- @cover_vars_csubst; sp. }

  assert (lsubstc (csubst (htyp a) (snoc s1 (x, t1))) w' s0 p'
          = lsubstc (csubst (htyp a) s1) w1 s0 c1) as eq1.
  { apply lsubstc_eq; sp; rw @csubst_snoc_dup; auto. }
  rw eq1; clear eq1.

  pose proof (lsubstc_csubst_ex (htyp a) s1 s0 w1 c1) as h; exrepnd.
  rw h1; clear h1.

  clear_irr; sp.
Qed.

Lemma sub_eq_hyps_snoc_weak_dup2 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t2,
    LIn x (dom_csub s2)
    -> sub_eq_hyps lib s1 s2 s3 s4 hs
    -> sub_eq_hyps lib s1 (snoc s2 (x, t2)) s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nih seh;
  inversion seh; subst; cpx.

  assert (cover_vars (htyp a) (snoc s2 (x, t2) ++ s5))
    as p2' by (apply cover_vars_weak; sp).

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2'); auto;[].

  pose proof (lsubstc_csubst_ex2 (htyp a) (snoc s2 (x, t2)) s5 w p2') as e; exrepnd.
  rewrite <- e1; clear e1.

  assert (wf_term (csubst (htyp a) s2)) as w2.
  { apply wf_term_csubst; sp. }
  assert (cover_vars (csubst (htyp a) s2) s5) as c2.
  { rw <- @cover_vars_csubst; sp. }

  assert (lsubstc (csubst (htyp a) (snoc s2 (x, t2))) w' s5 p'
          = lsubstc (csubst (htyp a) s2) w2 s5 c2) as eq2.
  { apply lsubstc_eq; sp; rw @csubst_snoc_dup; auto. }
  rewrite eq2; clear eq2.

  pose proof (lsubstc_csubst_ex (htyp a) s2 s5 w2 c2) as e; exrepnd.
  rw e1; clear e1.

  clear_irr; sp.
Qed.

Ltac clear_cover :=
  repeat match goal with
           | [ H : cover_vars _ _ |- _ ] => clear H
         end.

Lemma sub_eq_hyps_snoc_move1 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t1,
    !LIn x (dom_csub s1)
    -> sub_eq_hyps lib (snoc s1 (x, t1)) s2 s3 s4 hs
    -> sub_eq_hyps lib ((x,t1) :: s1) s2 s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nih seh;
  inversion seh; subst; cpx.

  assert (cover_vars (htyp a) ((x, t1) :: s1 ++ s0)) as p1'.
  { clear eqt seh seh0.
    allrw @cover_vars_eq; allrw subvars_eq.
    introv i; apply p1 in i; allsimpl.
    allrw @dom_csub_app; allrw @dom_csub_snoc; allsimpl.
    allrw in_app_iff; allrw in_snoc; tcsp. }

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1') (p2 := p2); auto;[].
  eapply eqtypes_alphaeqc_l;[|eauto].

  clear eqt seh seh0.

  unfold alphaeqc; simpl.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  introv i; simpl.
  repeat (rw <- @csub2sub_app).
  repeat (rw @csub2sub_snoc).
  repeat (rw @sub_find_app).
  repeat (rw @sub_find_snoc).
  boolvar.

  - rw @sub_find_none_if; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - remember (sub_find (csub2sub s1) v) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
Qed.

Lemma sub_eq_hyps_snoc_move2 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t2,
    !LIn x (dom_csub s2)
    -> sub_eq_hyps lib s1 (snoc s2 (x, t2)) s3 s4 hs
    -> sub_eq_hyps lib s1 ((x,t2) :: s2) s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nih seh;
  inversion seh; subst; cpx.

  assert (cover_vars (htyp a) ((x, t2) :: s2 ++ s5)) as p2'.
  { clear eqt seh seh0.
    allrw @cover_vars_eq; allrw subvars_eq.
    introv i; apply p2 in i; allsimpl.
    allrw @dom_csub_app; allrw @dom_csub_snoc; allsimpl.
    allrw in_app_iff; allrw in_snoc; tcsp. }

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2'); auto;[].
  eapply eqtypes_alphaeqc_r;[|eauto].

  clear eqt seh seh0.

  unfold alphaeqc; simpl.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  introv i; simpl.
  repeat (rw <- @csub2sub_app).
  repeat (rw @csub2sub_snoc).
  repeat (rw @sub_find_app).
  repeat (rw @sub_find_snoc).
  boolvar.

  - rw @sub_find_none_if; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - remember (sub_find (csub2sub s2) v) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
Qed.

Inductive cequiv_csub {o} (lib : library) : @CSub o -> @CSub o -> Type :=
| ceq_csub_nil : cequiv_csub lib [] []
| ceq_csub_cons :
    forall v t1 t2 s1 s2,
      cequivc lib t1 t2
      -> cequiv_csub lib s1 s2
      -> cequiv_csub lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors cequiv_csub.

Definition cequiv_csub_ext {o} lib (s1 s2 : @CSub o) :=
  in_ext lib (fun lib => Cast (cequiv_csub lib s1 s2)).

Lemma cequiv_csub_implies_eq_dom_csub {o} :
  forall lib (s1 s2 : @CSub o),
    cequiv_csub lib s1 s2 -> dom_csub s1 = dom_csub s2.
Proof.
  induction s1; introv ceq; inversion ceq; subst; cpx; clear ceq.
  simpl; f_equal; apply IHs1; auto.
Qed.

Lemma cequiv_csub_snoc {o} :
  forall lib (s1 s2 : @CSub o) v t1 t2,
    cequiv_csub lib s1 s2
    -> cequivc lib t1 t2
    -> cequiv_csub lib (snoc s1 (v,t1)) (snoc s2 (v,t2)).
Proof.
  induction s1; introv ceq1 ceq2; allsimpl; tcsp;
    inversion ceq1; subst; allsimpl; tcsp.
Qed.

Lemma tequalityi_cequivc_l {o} :
  forall lib n (a b c : @CTerm o),
    ccequivc_ext lib a b
    -> tequalityi lib n a c
    -> tequalityi lib n b c.
Proof.
  introv ceq teq.
  allunfold @tequalityi.
  eauto 3 with nequality.
Qed.
Hint Resolve tequalityi_cequivc_l : nequality.

Lemma tequalityi_cequivc_r {o} :
  forall lib n (a b c : @CTerm o),
    ccequivc_ext lib b c
    -> tequalityi lib n a b
    -> tequalityi lib n a c.
Proof.
  introv ceq teq.
  allunfold @tequalityi.
  eauto 3 with nequality.
Qed.
Hint Resolve tequalityi_cequivc_r : nequality.

Lemma eqtypes_cequivc_l {o} :
  forall lib lvl (a b c : @CTerm o),
    ccequivc_ext lib a b
    -> eqtypes lib lvl a c
    -> eqtypes lib lvl b c.
Proof.
  introv ceq eqt.
  allunfold @eqtypes.
  destruct lvl; eauto 3 with nequality.
Qed.
Hint Resolve eqtypes_cequivc_l : nequality.

Lemma eqtypes_cequivc_r {o} :
  forall lib lvl (a b c : @CTerm o),
    ccequivc_ext lib b c
    -> eqtypes lib lvl a b
    -> eqtypes lib lvl a c.
Proof.
  introv ceq eqt.
  allunfold @eqtypes.
  destruct lvl; eauto 3 with nequality.
Qed.
Hint Resolve eqtypes_cequivc_r : nequality.

Lemma cequiv_subst_iff_cequiv_csub {o} :
  forall lib (s1 s2 : @CSub o),
    cequiv_csub lib s1 s2 <=> cequiv_subst lib (csub2sub s1) (csub2sub s2).
Proof.
  induction s1; introv; split; intro h; allsimpl;
    try (complete (inversion h; subst; allsimpl; auto)).
  - inversion h; destruct s2; allsimpl; ginv.
  - inversion h; subst; allsimpl.
    constructor; auto.
    apply IHs1; auto.
  - destruct a; allsimpl.
    destruct s2; allsimpl; inversion h; subst; allsimpl.
    destruct p; allsimpl.
    constructor; auto.
    apply IHs1; auto.
Qed.

Lemma implies_cequiv_csub {o} :
  forall lib (s1 s2 s3 s4 : @CSub o),
    cequiv_csub lib s1 s3
    -> cequiv_csub lib s2 s4
    -> cequiv_csub lib (s1 ++ s2) (s3 ++ s4).
Proof.
  induction s1; introv ceq1 ceq2; inversion ceq1; subst; allsimpl; auto.
Qed.

Lemma cequiv_csub_refl {o} :
  forall lib (s : @CSub o),
    cequiv_csub lib s s.
Proof.
  induction s; introv; auto.
  destruct a; constructor; eauto 3 with slow.
Qed.
Hint Resolve cequiv_csub_refl : slow.

Lemma alpha_eq_hyps_sym {o} :
  forall (hs1 hs2 : @bhyps o),
    alpha_eq_hyps hs1 hs2
    -> alpha_eq_hyps hs2 hs1.
Proof.
  induction hs1; introv aeq; inversion aeq; subst; cpx; clear aeq.
  constructor; auto.
  apply alpha_eq_sym; auto.
Qed.

Lemma cequiv_csub_ext_implies_eq_dom_csub {o} :
  forall lib (s1 s2 : @CSub o),
    cequiv_csub_ext lib s1 s2 -> dom_csub s1 = dom_csub s2.
Proof.
  introv h.
  pose proof (h _ (lib_extends_refl lib)) as h; simpl in *; spcast.
  eapply cequiv_csub_implies_eq_dom_csub; eauto.
Qed.

Lemma sub_eq_hyps_cequiv_csub1 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 s',
    cequiv_csub_ext lib s1 s'
    -> sub_eq_hyps lib s1 s2 s3 s4 hs
    -> sub_eq_hyps lib s' s2 s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv ceq seh;
  inversion seh; subst; cpx.

  applydup @cequiv_csub_ext_implies_eq_dom_csub in ceq as edoms.

  assert (cover_vars (htyp a) (s' ++ s0)) as p1'.
  { clear eqt seh seh0.
    allrw @cover_vars_eq; allrw subvars_eq.
    introv i; apply p1 in i; allsimpl.
    allrw @dom_csub_app; allrw in_app_iff; repndors; tcsp.
    rw edoms in i; tcsp. }

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1') (p2 := p2); auto;
    [|eapply IHhs; eauto];[].
  clear IHhs.

  eapply eqtypes_cequivc_l;[|eauto].

  clear eqt seh seh0.

  introv x.
  pose proof (ceq _ x) as ceq; simpl in *.
  spcast.
  unfold cequivc; simpl.

  allrw @cover_vars_eq.
  allrw @subvars_eq.
  apply cequiv_lsubst.

  - apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - apply cequiv_subst_iff_cequiv_csub.
    apply implies_cequiv_csub; eauto 3 with slow.
Qed.

Lemma sub_eq_hyps_cequiv_csub2 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 s',
    cequiv_csub_ext lib s2 s'
    -> sub_eq_hyps lib s1 s2 s3 s4 hs
    -> sub_eq_hyps lib s1 s' s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv ceq seh;
  inversion seh; subst; cpx.

  applydup @cequiv_csub_ext_implies_eq_dom_csub in ceq as edoms.

  assert (cover_vars (htyp a) (s' ++ s5)) as p2'.
  { clear eqt seh seh0.
    allrw @cover_vars_eq; allrw subvars_eq.
    introv i; apply p2 in i; allsimpl.
    allrw @dom_csub_app; allrw in_app_iff; repndors; tcsp.
    rw edoms in i; tcsp. }

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2'); auto;
  [|eapply IHhs; eauto];[].

  eapply eqtypes_cequivc_r;[|eauto].

  clear eqt seh seh0.
  introv x.
  pose proof (ceq _ x) as ceq; simpl in *.
  spcast.
  unfold cequivc; simpl.

  allrw @cover_vars_eq.
  allrw @subvars_eq.
  apply cequiv_lsubst.

  - apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @dom_csub_eq; auto.

  - apply cequiv_subst_iff_cequiv_csub.
    apply implies_cequiv_csub; eauto 3 with slow.
Qed.
