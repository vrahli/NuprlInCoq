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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export alphaeq.
Require Export computation.
Require Export rel_nterm.
Require Export substitution2.
Require Export cequiv.

Lemma ext_alpha_eq_subs_vars {o}:
   forall vs1 vs2,
   forall sub1 sub2,
   (forall v, LIn v vs2 -> LIn v vs1) ->
   @ext_alpha_eq_subs o vs1 sub1 sub2 ->
   ext_alpha_eq_subs vs2 sub1 sub2.
Proof. introv cont eq a. apply cont in a. apply eq. auto.
Qed.

Definition cequiv_option {o} lib (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => cequiv_open lib t1 t2
    | None, None => True
    | _,_ => False
  end.

Lemma cequiv_open_trans {o} :
   forall lib (t1 t2 t3 : (@NTerm o)),
   cequiv_open lib t1 t2 -> 
   cequiv_open lib t2 t3 -> 
   cequiv_open lib t1 t3.
Proof. introv eq1 eq2.
       rw<- @fold_cequiv_open in eq1.
       rw<- @fold_cequiv_open in eq2.
       rw<- @fold_cequiv_open.
       eapply olift_trans; [ | |exact eq1 | exact eq2 ].
       introv a b. eapply cequiv_trans; eauto.
       apply respects_alpha_cequiv.
Qed.


Lemma cequiv_open_sym {o} :
   forall lib (t1 t2 : (@NTerm o)),
   cequiv_open lib t1 t2 -> 
   cequiv_open lib t2 t1.
Proof. introv eq.
       rw<- @fold_cequiv_open in eq.
       rw<- @fold_cequiv_open.
       destruct eq as [wf1 eq].
       destruct eq as [wf2 eq].
       split; auto; split; auto.
       introv wf isp1 isp2.
       apply cequiv_sym.
       eapply eq; eauto.
Qed.

Lemma cequiv_open_refl {o} :
   forall lib (t : (@NTerm o)),
   (nt_wf t) -> cequiv_open lib t t.
Proof. introv wf. rw<- @fold_cequiv_open.
       split; auto; split; auto.
       introv wfsub isp1 isp2.
       apply cequiv_refl; auto.
Qed.

Lemma cequiv_option_trans {o} :
   forall lib (t1 t3 : option (@NTerm o)) (t2 : @NTerm o),
   cequiv_option lib t1 (Some t2) -> 
   cequiv_option lib (Some t2) t3 -> 
   cequiv_option lib t1 t3.
Proof. introv eq1 eq2.
       destruct t1; destruct t3;
       allsimpl; auto.
       eapply cequiv_open_trans; eauto.
Qed.


Lemma cequiv_option_sym {o} :
   forall lib (t1 t2 : option (@NTerm o)),
   cequiv_option lib t1 t2 ->  
   cequiv_option lib t2 t1.
Proof. introv eq1.
       destruct t1; destruct t2;
       allsimpl; auto.
       apply cequiv_open_sym; auto.
Qed.

Definition ext_cequiv_subs {o} lib  (sub1 sub2 : @Sub o) :=
  eqset (dom_sub sub1) (dom_sub sub2)
  # forall v,
      LIn v (dom_sub sub1)
      -> cequiv_option lib (sub_find sub1 v) (sub_find sub2 v).

Lemma ext_cequiv_subs_trans {o} :
   forall lib  (sub1 sub2 sub3 : @Sub o),
   ext_cequiv_subs lib  sub1 sub2 -> 
   ext_cequiv_subs lib  sub2 sub3 -> 
   ext_cequiv_subs lib  sub1 sub3.
Proof. introv eq1 eq2. 
       destruct eq1 as [domeq1 eq1].
       destruct eq2 as [domeq2 eq2].
       split; intro.
       -  rw domeq1; rw domeq2; sp.
       -  introv indom. dup indom as indom2. rw domeq1 in indom2. 
           pose proof (eq1 v indom) as eqa; clear eq1.
           pose proof (eq2 v indom2) as eqb; clear eq2.
           apply in_dom_sub_exists in indom2; exrepnd.
           rw indom0 in eqa. 
           rw indom0 in eqb.
           eapply cequiv_option_trans; eauto.
Qed.

Lemma ext_cequiv_sym {o} :
   forall lib  (sub1 sub2 : @Sub o),
   ext_cequiv_subs lib  sub1 sub2 -> 
   ext_cequiv_subs lib  sub2 sub1.
Proof. introv eq1. 
       destruct eq1 as [domeq1 eq1].
       split; intro.
       -  rw domeq1;  sp.
       -  introv indom. rw<- domeq1 in indom. 
           pose proof (eq1 v indom) as eqa; clear eq1.
           remember (sub_find sub2 v) as a; destruct a;
          remember  (sub_find sub1 v) as b; destruct b;
          allsimpl; auto; apply cequiv_open_sym; auto.
Qed.

Lemma ext_alpha_eq_subs_implies_ext_cequiv_subs {o} :
    forall lib  (sub1 sub2 : @Sub o),
    (forall v : NVar, LIn v (dom_sub sub1) <=> LIn v (dom_sub sub2)) ->
    (forall v t,  sub_find sub1 v = Some t -> nt_wf t) ->
    (forall v t,  sub_find sub2 v = Some t -> nt_wf t) ->
    ext_alpha_eq_subs (dom_sub sub1) sub1 sub2 -> 
   ext_cequiv_subs lib  sub1 sub2.
Proof. introv samedom wf1 wf2 eq. split. auto. introv indom. 
       pose proof (eq v indom) as eq2.
       revert eq2.
       pose proof (wf1 v) as wfa.
       revert wfa. 
       pose proof (wf2 v) as wfb.
       revert wfb. 
       generalize (sub_find sub1 v); generalize (sub_find sub2 v).
       intros; destruct o0; destruct o1; allsimpl; auto.
       apply alpha_implies_cequiv_open; auto.
Qed. 

Lemma length_sub_filter_le {o} :
  forall (sub : @Sub o) vs,
    length (sub_filter sub vs) <= length sub.
Proof.
  induction sub as [|p sub]; introv; allsimpl; tcsp.
  destruct p as [v t]; boolvar; simpl; tcsp.
  pose proof (IHsub vs) as h; lia.
Qed.

Definition ext_subs {o} (vs : list NVar) (sub1 sub2 : @Sub o) :=
  forall v : NVar,
    LIn v vs -> sub_find sub1 v = sub_find sub2 v.

Lemma ext_subs_refl {o} :
  forall l (sub : @Sub o),
    ext_subs l sub sub.
Proof.
  introv i.
  remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.
Qed.
Hint Resolve ext_subs_refl : slow.

Lemma ext_subs_nil_vs {o} :
  forall (sub1 sub2 : @Sub o),
    ext_subs [] sub1 sub2.
Proof.
  introv i; allsimpl; tcsp.
Qed.
Hint Resolve ext_subs_nil_vs : slow.

Lemma ext_subs_implies_ext_alpha_eq_subs {o} :
  forall vs (sub1 sub2 : @Sub o),
    ext_subs vs sub1 sub2 -> ext_alpha_eq_subs vs sub1 sub2.
Proof.
  introv ext i.
  apply ext in i; rw i; eauto 3 with slow.
Qed.
Hint Resolve ext_subs_implies_ext_alpha_eq_subs : slow.

Inductive cequiv_open_subst {p} (lib : @library p) : @Sub p -> @Sub p -> Type :=
| ceq_open_sub_nil : cequiv_open_subst lib [] []
| ceq_open_sub_cons :
    forall v t1 t2 s1 s2,
      cequiv_open lib t1 t2
      -> cequiv_open_subst lib s1 s2
      -> cequiv_open_subst lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors cequiv_open_subst.

Lemma ext_cequiv_to_cequiv_open_subst {o} :
   forall lib,
   forall sub1 sub2 : @Sub o,
   ext_cequiv_subs lib  sub1 sub2  ->
   { suba : @Sub o $
   { subb : @Sub o $ 
     ext_subs (dom_sub sub1) suba sub1 #
     ext_subs (dom_sub sub1) subb sub2 #
     eqset (dom_sub suba) (dom_sub sub1) #
     eqset (dom_sub subb) (dom_sub sub2) #
     (prog_sub sub1 -> prog_sub suba) #
     (prog_sub sub2 -> prog_sub subb) #
     cequiv_open_subst lib suba subb
   }}.
Proof.
  intros lib sub1.
  remember (length sub1) as len.
  revert dependent sub1.

  induction len as [n ind] using comp_ind_type; introv eqlen ext.

  destruct n as [|n]; cpx.

  - exists ([] : @Sub o) ([] : @Sub o); simpl; dands; eauto 3 with slow.
    unfold ext_cequiv_subs in ext; allsimpl; tcsp.

  - destruct sub1 as [|p sub1]; allsimpl; ginv.
    unfold ext_cequiv_subs in ext; repnd; allsimpl.

    pose proof (ext p0) as cop; autodimp cop hyp.
    boolvar; tcsp; allsimpl.
    remember (sub_find sub2 p0) as sf; symmetry in Heqsf; destruct sf; tcsp.

    pose proof (ind (length (sub_filter sub1 [p0]))) as h; clear ind.
    autodimp h hyp.
    { pose proof (length_sub_filter_le sub1 [p0]) as l; lia. }
    
    pose proof (h (sub_filter sub1 [p0])) as q; clear h; autodimp q hyp.
    pose proof (q (sub_filter sub2 [p0])) as ih; clear q.
    autodimp ih hyp.
    { split.
      - allrw <- @dom_sub_sub_filter.
        introv; allrw in_remove_nvars.
        rw <- ext0; allrw in_single_iff; simpl.
        split; tcsp.
      - introv i; allrw <- @dom_sub_sub_filter; allrw in_remove_nvars; repnd.
        allrw in_single_iff.
        allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; tcsp.
        pose proof (ext v) as h; autodimp h hyp.
        boolvar; tcsp. }

    exrepnd.

    exists ((p0,p) :: suba) ((p0,n) :: subb).
    allrw <- @dom_sub_sub_filter.
    dands.

    + introv i; allsimpl; repndors; subst; boolvar; tcsp.
      pose proof (ih0 v) as h; rw in_remove_nvars in h; autodimp h hyp; simpl; tcsp.
      rw @sub_find_sub_filter_eq in h; allrw memvar_singleton; boolvar; tcsp.

    + introv i; allsimpl; repndors; subst; boolvar; tcsp.
      pose proof (ih2 v) as h; rw in_remove_nvars in h; autodimp h hyp; simpl; tcsp.
      rw @sub_find_sub_filter_eq in h; allrw memvar_singleton; boolvar; tcsp.

    + simpl.
      split; introv i; allsimpl; repndors; tcsp.
      * apply ih3 in i; allrw in_remove_nvars; tcsp.
      * rw ih3; rw in_remove_nvars; rw in_single_iff.
        destruct (deq_nvar p0 x); subst; tcsp.
        right; tcsp.

    + simpl.
      split; introv i; allsimpl; repndors; subst; tcsp.
      * apply ext0; simpl; tcsp.
      * apply ih4 in i; allrw in_remove_nvars; tcsp.
      * rw ih4; rw in_remove_nvars; rw in_single_iff.
        destruct (deq_nvar p0 x); subst; tcsp.
        right; tcsp.

    + allrw @prog_sub_cons; introv i; repnd; dands; auto.
      apply ih5; eauto 2 with slow.

    + allrw @prog_sub_cons; introv i; repnd; dands; auto;
      try (apply ih6; eauto 2 with slow).
      rw <- @prog_sub_eq in i.
      allapply @sub_find_some; allapply @in_sub_eta; repnd; eauto 3 with slow.

    + constructor; auto.
Qed.

Lemma cequiv_open_subst_implies_cequiv_subst {o} :
  forall lib (suba subb : @Sub o),
    prog_sub suba
    -> prog_sub subb
    -> cequiv_open_subst lib suba subb
    -> cequiv_subst lib suba subb.
Proof.
  induction suba; introv ispa ispb ceq.
  - inversion ceq; subst; auto.
  - inversion ceq as [|? ? ? ? ? ceq1 ceq2]; subst; clear ceq.
    allrw @prog_sub_cons; repnd.
    constructor; auto.
    apply cequiv_open_cequiv; eauto 2 with slow.
Qed.

Lemma cequiv_lsubst_if_ext_cequiv {o} :
  forall lib,
  forall (t1 t2 : @NTerm o) sub1 sub2,
    cequiv_open lib t1 t2
    -> ext_cequiv_subs lib sub1 sub2
    -> prog_sub sub1
    -> prog_sub sub2
    -> isprogram (lsubst t1 sub1)
    -> isprogram (lsubst t2 sub2)
    -> cequiv lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv aeq ext ps1 ps2 isp1 isp2.

  apply cequiv_open_cequiv; auto.

  applydup @ext_cequiv_to_cequiv_open_subst in ext; exrepnd.
  applydup @isprogram_lsubst_iff in isp1 as X1.
  destruct isp1 as [c1 wf1].
  applydup @isprogram_lsubst_iff in isp2 as X2.
  destruct isp2 as [c2 wf2].

  allapply @ext_subs_implies_ext_alpha_eq_subs.

  assert (forall v : NVar, LIn v (free_vars t1) -> LIn v (dom_sub sub1)) as t1sub1.
  { introv mem. destruct X1 as [b c]. apply c in mem; exrepnd.
    apply sub_find_some_implies_memvar_true in mem1.
    apply assert_memvar. rw mem1. constructor.  }

  assert (ext_alpha_eq_subs (free_vars t1) sub1 suba).
  { eapply ext_alpha_eq_subs_vars;
    [auto | apply ext_alpha_eq_subs_sym; exact ext1].
  }

  assert (forall v : NVar, LIn v (free_vars t2) -> LIn v (dom_sub sub1)) as t2sub1.
  { introv mem. destruct X2 as [b c]. apply c in mem; exrepnd.
    apply sub_find_some_implies_memvar_true in mem1.
    destruct ext as [samedom ext]. rw samedom.
    apply assert_memvar. rw mem1. constructor.  } 
 
  assert (ext_alpha_eq_subs (free_vars t2) sub2 subb).
  { eapply ext_alpha_eq_subs_vars;
    [auto | apply ext_alpha_eq_subs_sym; exact ext2].
  }

  assert ( nt_wf (lsubst t1 suba)).
  { eapply alphaeq_preserves_wf; [  | exact wf1].
    apply alpha_eq_lsubst_if_ext_eq;  eauto 3 with slow.
  }

  assert ( nt_wf (lsubst t2 subb)).
  { eapply alphaeq_preserves_wf; [  | exact wf2].
    apply alpha_eq_lsubst_if_ext_eq;  eauto 3 with slow.
  }

  assert (cequiv_open lib (lsubst t1 sub1) (lsubst t1 suba)) as eq1.
  { apply alpha_implies_cequiv_open; auto.
    apply alpha_eq_lsubst_if_ext_eq; eauto 3 with slow. 
  }

  assert (cequiv_open lib (lsubst t2 sub2) (lsubst t2 subb)) as eq2.
   { apply alpha_implies_cequiv_open; auto.
     apply alpha_eq_lsubst_if_ext_eq; eauto 3 with slow. 
   }

   assert (cequiv_subst lib suba subb) as ceqs.
   { apply cequiv_open_subst_implies_cequiv_subst; tcsp. }

  assert (cequiv_open lib (lsubst t1 suba) (lsubst t2 subb)) as eq3.
   { apply cequiv_implies_cequiv_open.
     apply lsubst_cequiv_congr; auto;
     apply isprogram_lsubst_iff; split; repnd; auto; introv mem.
     - pose proof (X1 v mem) as Z; exrepnd.
       apply t1sub1 in mem.
       apply ext1 in mem.
       destruct (sub_find sub1 v).
       destruct (sub_find suba v).
       allsimpl. ginv.
       exists n0; dands; auto.
       +  apply alphaeq_preserves_wf in mem. apply mem; auto.
       +  apply alphaeq_preserves_closed in mem. apply mem; auto.
       + inversion mem.
       + inversion Z1.
    - pose proof (X2 v mem) as Z; exrepnd.
       apply t2sub1 in mem.
       apply ext2 in mem.
       destruct (sub_find sub2 v).
       destruct (sub_find subb v).
       allsimpl. ginv.
       exists n0; dands; auto.
       +  apply alphaeq_preserves_wf in mem. apply mem; auto.
       +  apply alphaeq_preserves_closed in mem. apply mem; auto.
       + inversion mem.
       + inversion Z1.
     }
  eapply cequiv_open_trans; [exact eq1 |].
  eapply cequiv_open_trans; [exact eq3 | apply cequiv_open_sym; auto].
Qed.
