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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_subtype_rel.
Require Export sterm.
Require Export sequents_tacs.
Require Export per_props_tequality.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export sequents2.
Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export variables.




(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)
(* end hide *)

(**
  We can use  (T subtype_rel T) which is (\x.x in T -> T) to
  express the judgement that T is a type.
  

 *)
Definition mk_istype {o} (T : @NTerm o) :=
  mk_subtype_rel T T.
Definition mkc_istype {o} (T : @CTerm o) :=
  mkc_subtype_rel T T.

Lemma wf_mk_istype {p} : forall T : NTerm, wf_term (mk_istype T) <-> @wf_term  p T.
Proof. unfold mk_istype. intros. split; intro. 
   rw @wf_subtype_rel_iff in H. exrepnd. auto.
   rw @wf_subtype_rel_iff . split; auto.
Qed.

Lemma cover_vars_mk_istype {p} : forall (T : NTerm) (s : CSub), cover_vars (@mk_istype p T) s <-> cover_vars T s.
Proof. unfold mk_istype. intros. split; intros.
  rw @cover_vars_subtype_rel in H. exrepnd. auto.
   rw @cover_vars_subtype_rel . split; auto.
Qed.

Lemma lsubstc_mk_istype {o} :
  (forall (T: @NTerm o)(s : CSub) (wf : wf_term (mk_istype T)) (c : cover_vars (mk_istype T) s),
    {w : wf_term T $
    {c': cover_vars T s $
      alphaeqc (lsubstc (mk_istype T) wf s c)  (mkc_istype (lsubstc T w s c'))}}).
Proof. intros. unfold mk_istype. unfold mkc_istype.
       eexists. eexists.
       lsubst_tac. 
       assert (alphaeqc (mkc_subtype_rel (lsubstc T w1 s c1) (lsubstc T w1 s c1))
  (mkc_subtype_rel (lsubstc T w1 s c1) (lsubstc T w1 s c1))). apply alphaeqc_refl.
       refine X.
   Unshelve. rw @wf_mk_istype in wf. auto.
             rw @cover_vars_mk_istype in c. auto.
Qed.

Lemma equality_subtype_rel_refl {o} :
    forall lib (A: @CTerm o),
      type lib A ->
      equality lib mkc_axiom mkc_axiom (mkc_subtype_rel A A).
Proof. intros.
       rw @equality_in_subtype_rel. 
         split. spcast. eauto 2 with slow. split. spcast. eauto 2 with slow.
         split; auto. split; auto. unfold subtype_rel. auto.
Qed.

Lemma tequality_subtype_rel_refl {o} :
    forall lib (A B: @CTerm o),
      tequality lib A B ->
      tequality lib  (mkc_subtype_rel A A) (mkc_subtype_rel B B) .
Proof. intros. rw @mkc_subtype_rel_eq. rw @mkc_subtype_rel_eq. apply tequality_mkc_member_sp.
       split.
       2:{ right. spcast. eauto 2 with slow. }
       apply tequality_fun. split; auto.
Qed.

Lemma teq_and_eq_istype {o} :
   forall lib (T : @NTerm o) (s1 s2: CSub) 
    (wf1 : wf_term (mk_istype T)) 
    (wf : wf_term T)
    (c : cover_vars  T s1)
    (c' : cover_vars T s2)
    (c1 : cover_vars (mk_istype T) s1)
    (c2 : cover_vars (mk_istype T) s2),
 tequality lib (lsubstc T wf s1 c)  (lsubstc T wf s2 c') ->   
tequality lib (lsubstc (mk_istype T) wf1 s1 c1)  (lsubstc (mk_istype T) wf1 s2 c2)
# equality lib mkc_axiom mkc_axiom (lsubstc (mk_istype T) wf1 s1 c1).
Proof.
   unfold mk_istype. intros. lsubst_tac.
   generalize_lsubstc_terms A.
   generalize_lsubstc_terms B. clear - H.
   split.
   apply @tequality_subtype_rel_refl. auto.
   apply @equality_subtype_rel_refl. 
   unfold type. eapply tequality_refl. eauto.
Qed.

Lemma cover_vars_family {o} :
   forall  (x y : NVar) (B : NTerm) (s : CSub) (a : CTerm),
cover_vars_upto B (csub_filter s [x]) [x] -> cover_vars (subst B x (@mk_var  o y)) (snoc s (y, a)).
Proof. intros. unfold cover_vars_upto in H. unfold cover_vars. unfold over_vars.
  simpl in H. rw @dom_csub_csub_filter in H.
  rw @dom_csub_snoc. simpl. 
  unfold subvars in H. rw assert_sub_vars in H. 
  unfold subvars. rw assert_sub_vars.
  intros. rw in_snoc.
  assert ( LIn x0 (remove_nvars [x] (free_vars B)) + (x0 = y)). 
  2: {destruct X0.  rw in_remove_nvars in l. exrepnd. 
      specialize (H x0 l0) as H. left. 
      rw @in_cons_iff in H. destruct H. destruct l. simpl. auto.
      rw @in_remove_nvars in l1. exrepnd. auto. right. auto.
      }
  rw @in_remove_nvars. pose proof (deq_nvar x0 y). destruct H0;auto. left.
  unfold subst in X.
  pose proof (deq_nvar x0 x). destruct H0. rewrite <- e in X. clear e.
  assert (False). 2:{ destruct H0. }
  Search (free_vars (lsubst _ _)).
   admit.
  pose proof (@free_vars_lsubst2 o B [(x, mk_var y)] x0 X) as xx. destruct xx.
  split; auto. simpl. intro. destruct H0; auto.
  exrepnd. assert (False). 2:{ destruct H0. }
  simpl in s1. destruct s1;auto. inversion e. rewrite <- H2 in s0. simpl in s0.
  destruct s0; auto.
    
Admitted.

(* This rule says that in order to prove that T is a type
   it is enough to prove that it is inhabited.

    H |-  istype(T)
        By inhabitedType t
    H |-  t in T
*)

Definition rule_inhabited_type {o}
           (H : barehypotheses)
           (T t: @NTerm o) :=
  
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype T)))
    [ mk_baresequent H (mk_conclax (mk_member t T))
    ]
    [].

Lemma tequality_preserves_member {p} :
  forall lib (a b t: @CTerm p),
    tequality lib a b
    ->  member lib t a
    ->  member lib t b.
Proof.
  introv teq inh.
  allunfold @tequality; exrepnd.
  allunfold @member.
  allunfold @equality; exrepnd.
  generalize (nuprl_uniquely_valued lib a eq eq0); intro i; repeat (dest_imp i hyp).
  apply nuprl_refl with (t2 := b); sp.
  exists eq; sp.
  apply nuprl_refl with (t2 := a); sp.
  apply nuprl_sym; sp.
  rw i; sp.
Qed.

Lemma rule_inhabited_type_true {o} :
  forall lib (H : barehypotheses)
         (T t: @NTerm o),
    rule_true lib (rule_inhabited_type H T t).
Proof.
  unfold rule_inhabited_type, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_istype.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  lsubst_tac.
  allrw (@equality_in_member o).
  exrepnd.
  generalize_lsubstc_terms T1.
  generalize_lsubstc_terms T2.
  revert hyp0.
  generalize_lsubstc_terms t1.
  generalize_lsubstc_terms t2.
  intro.
  split.
  - (* tequality *)
    rw @mkc_subtype_rel_eq.
    rw @mkc_subtype_rel_eq.
    rw @tequality_mkc_member in hyp0.
    exrepnd.
    unfold mkc_subtype_rel.
    rw @tequality_mkc_member.
    assert (tequality lib (mkc_fun T1 T1) (mkc_fun T2 T2)) by
          (rw @tequality_mkc_fun; split; auto).
    split. auto. split. split; intro.
   pose proof (@tequality_preserves_member o lib (mkc_fun T1 T1) (mkc_fun T2 T2) mkc_id) as xx.
   apply xx; auto.
   pose proof (@tequality_preserves_member o lib (mkc_fun T2 T2) (mkc_fun T1 T1) mkc_id) as xx.
   apply xx; auto. apply tequality_sym; auto.
   right. spcast. auto.
  - (* equality *)
  apply equality_in_subtype_rel. split. auto. split. auto.
  assert (type lib T1).
  eapply inhabited_implies_tequality. eauto.
  split. auto. split; auto. 
  unfold subtype_rel. auto.
Qed.

Lemma mk_istype_true2_implies {o} :
   forall lib (H : barehypotheses) 
           (A : @NTerm o),
           (sequent_true2 lib (mk_baresequent H (mk_conclax (mk_istype A)))) -> 
       (forall (s1 s2 : CSub)
               (w : wf_term A)
              (c1 : cover_vars A s1)
              (c2 : cover_vars A s2)
       ,
       hyps_functionality lib s1 H ->
       similarity lib s1 s2 H -> 
        (type lib (lsubstc A w s1 c1) 
        # (tequality lib (lsubstc A w s1 c1) (lsubstc A w s2 c2)))).
Proof. 
    unfold mk_istype.
    intros. destruct X as [ ws1 hyp1 ].
    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2) as hyp; clear hyp1.
    repeat (autodimp hyp hh).
    exrepnd.
    lsubst_tac.
    apply equality_in_subtype_rel in hyp1; repnd.
    split. auto.
    generalize_lsubstc_terms T1.
    generalize_lsubstc_terms T2.
    clear - hyp0.
    rw @mkc_subtype_rel_eq in hyp0.
    rw @mkc_subtype_rel_eq in hyp0.
    rw @tequality_mkc_member_sp in hyp0.
    exrepnd.
    rw @tequality_mkc_fun in hyp1.
    exrepnd.
    auto.
Qed.

(* We can prove that a:A -> B, a:A x B, {a:A | B}, and isect(a:A,B) are types when
    A is a type and  a:A |-  B is a type  *)

(*  Here is the rule for the function type:

    H |-  istype(a:A->B)
        By functionType 
    H |-  istype(A)
    H, a:A |- istype(B)
*)

Definition rule_function_type {o}
           (H : barehypotheses)
           x y
           (A B: @NTerm o) :=
  
  mk_rule
    (mk_baresequent H (mk_conclax (mk_istype (mk_function A x B))))
    [ mk_baresequent H (mk_conclax (mk_istype A)),
      mk_baresequent (snoc H (mk_hyp y A)) (mk_conclax (mk_istype (subst B x (mk_var y))))
    ]
    [ sarg_var y ].

Lemma rule_function_type_true3 {o} :
   forall lib (H : barehypotheses) x y
           (A B: @NTerm o),
   rule_true3 lib (rule_function_type H x y A B).
Proof.

  unfold rule_function_type, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  
(* We will use the first Hyp to get that A is a type, i.e. functional *)
  pose proof (@mk_istype_true2_implies o lib H A Hyp) as Atype.
(* We will use the second Hyp0 to get that B is a type family *)
  pose proof (@mk_istype_true2_implies o lib (snoc H (mk_hyp y A)) (subst B x (mk_var y)) Hyp0) as Btype.
  destruct Hyp as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_conclax (mk_istype (mk_function A x B))))) as wfc.
  {
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; eauto 2 with slow.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.
  clear hyp1 hyp2.

  (* We prove some simple facts on our sequents *)
  assert ((y <> x -> !LIn y (free_vars B))
          # !LIn y (free_vars A)
          # !LIn y (vars_hyps H)) as vhyps.

  { dwfseq.
    sp;
      try (complete (generalize (wfc0 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc1 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp));
      try (complete (generalize (wfc2 y); intro p;
                     allrw in_app_iff;
                     allrw in_remove_nvars; allsimpl;
                     autodimp p hyp; tcsp;
                     right; tcsp)).
  }

  destruct vhyps as [ nyB vhyps ].
  destruct vhyps as [ nyA vhyps ].
  (* done with proving these simple facts *)
  vr_seq_true.
  lsubst_tac.
  assert (
  forall (s s' : CSub) (ca1 : cover_vars mk_axiom s) (cb2 : cover_vars mk_axiom s')
  (pC1 : cover_vars (mk_istype (mk_function A x B)) s)
  (pC2 : cover_vars (mk_istype (mk_function A x B)) s'),
   hyps_functionality lib s H ->
   similarity lib s s' H ->
   tequality lib (lsubstc (mk_istype (mk_function A x B)) wf1 s pC1)
  (lsubstc (mk_istype (mk_function A x B)) wf1 s' pC2) # 
   equality lib (@mkc_axiom o)  (@mkc_axiom o)
  (lsubstc (mk_istype (mk_function A x B)) wf1 s pC1)). 
 2: {
  pose proof (@teq_and_eq_if_equality o lib (mk_istype (mk_function A x B))
 (@mk_axiom o) (@mk_axiom o) s1 s2 H wf1 wfce0 wfce0 pt1 pt2 pt1 pt2 pC1 pC2 eqh sim) as xx.
  exrepnd.
  autodimp xx G. eapply H0; eauto.
  }
  clear pt1 pt2 eqh sim pC1 pC2 s1 s2. intros.
  eapply @teq_and_eq_istype; eauto.
   rw @wf_mk_istype in wf1.
  rw @cover_vars_mk_istype in pC1.
  rw @cover_vars_mk_istype in pC2.
  assert ( forall (w : wf_term (mk_function A x B)) 
                  (c1 : cover_vars (mk_function A x B) s)
                  (c2 : cover_vars (mk_function A x B) s'),
   
     tequality lib (lsubstc (mk_function A x B) w s c1) (lsubstc (mk_function A x B) w s' c2)).
   2 : { apply H2. }
   clear pC1 pC2 ca1 cb2.
   intros.
   lsubst_tac.
   
   apply tequality_function.
   exrepnd.
   split. apply Atype; auto.
   intros.
   pose proof (@sim_cons o lib a a' s s' (mk_hyp y A) H w1 c0 H2 H1) as simX.
   simpl in simX.
   assert (hyps_functionality lib (snoc s (y, a)) (snoc H (mk_hyp y A))).
   pose proof (@hyps_functionality_snoc o lib H (mk_hyp y A) s a) as xx.
   simpl in xx. apply xx. intros. proof_irr; GC. apply Atype; auto. auto.
    rw @wf_mk_istype in wfct.
   assert (cover_vars (subst B x (mk_var y)) (snoc s (y, a))) as csy.
   rw @cover_vars_function in c1. exrepnd.
   apply @cover_vars_family. auto.
  assert (cover_vars (subst B x (mk_var y)) (snoc s' (y, a'))) as csy'.
    rw @cover_vars_function in c1. exrepnd.
   apply @cover_vars_family. auto.
   assert (tequality lib (lsubstc (subst B x (mk_var y)) wfct (snoc s (y, a)) csy)
            (lsubstc (subst B x (mk_var y)) wfct (snoc s' (y, a')) csy')).
     intros. apply Btype; auto.
    assert (forall (s:CSub) a (csy : cover_vars (subst B x (mk_var y)) (snoc s (y, a)))
            (c3 : cover_vars_upto B (csub_filter s [x]) [x]),
((lsubstc (subst B x (mk_var y)) wfct (snoc s (y, a)) csy) 
             = (lsubstc_vars B w2 (csub_filter s [x]) [x] c3) [[x \\ a]])).
     admit.
  pose proof (H5 s a csy c3) as xx. rewrite <- xx.
  pose proof (H5 s' a' csy' c5) as yy. rewrite <- yy.
  auto.

Admitted.
  
 

(* begin hide *)

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
