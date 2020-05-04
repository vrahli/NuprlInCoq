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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms_swap.
Require Export computation_swap.
Require Export approx_star0.



Lemma computes_to_val_like_in_max_k_steps_swap_cs1_implies {p} :
  forall lib k n1 n2 n3 v,
    wf_term n1
    -> wf_term n2
    -> wf_term n3
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
         v
         k
    -> {c1, c2 : choice_sequence_name
       $ { k1 , k2 : nat
       $ k1+k2+1 <= k
       # computes_to_can_in_max_k_steps lib k1 n1 (mk_choice_seq c1)
       # computes_to_can_in_max_k_steps lib k2 n2 (mk_choice_seq c2)
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd (mk_choice_seq c1),
                   nobnd (mk_choice_seq c2),
                   nobnd n3])
           (k1+k2)
       # computes_to_val_like_in_max_k_steps lib
           (mk_swap_cs2 (c1,c2) n3)
           v
           (k - (k1 + k2 + 1))
       }}
       [+]
       {en, e : NTerm
       $ {k1 : nat
       $ k1 + 1 <= k
       # v = mk_exception en e
       # computes_to_exception_in_max_k_steps lib en n1 e k1
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd v,
                   nobnd n2,
                   nobnd n3])
           k1
       }}
       [+]
       {en, e : @NTerm p
       $ {w : NTerm
       $ {k1 , k2 : nat
       $ k1+k2+1 <= k
       # v = mk_exception en e
       # computes_to_can_in_max_k_steps lib k1 n1 w
       # computes_to_exception_in_max_k_steps lib en n2 e k2
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd w,
                   nobnd v,
                   nobnd n3])
           (k1+k2)
       }}}.
Proof.
  induction k; introv wf1 wf2 wf3 comp.

  - destruct comp as [r is].
    inversion r; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1));[].
    dopid o as [can1|ncan1|nsw1|exc1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (csunf comp1; allsimpl; ginv));[].
      dopid o as [can2|ncan2|nsw2|exc2|abs2] SCase.

      * SCase "Can".
        csunf comp1; simpl in *.
        apply compute_step_swap_cs1_aux_success_implies in comp1; exrepnd; subst; simpl in *; ginv.
        inversion comp6; subst; simpl in *; clear comp6.
        left.
        exists n1 n2 0 0; simpl; dands; auto; try omega;
          allrw @computes_to_can_in_max_k_steps_0;
          allrw @reduces_in_atmost_k_steps_0;
          autorewrite with slow; dands; eauto 3 with slow.

      * SCase "NCan".
        csunf comp1; simpl in comp1.
        apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
        apply IHk in comp0; eauto 3 with slow;[].
        repndors; exrepnd; subst; simpl in *.

        { left; exists c1 c2 k1 (S k2); simpl; dands; auto; try omega.
          { rw @computes_to_can_in_max_k_steps_S; eexists; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. }
          rw  <- plus_n_Sm; autorewrite with slow.
          assert (k1 + S k2 = k1 + k2 + 1) as e by omega; rewrite e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { right; right.
          exists en e w k1 (S k2); dands; auto; try omega.
          { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. } }

      * SCase "NSwapCs2".
        csunf comp1; simpl in *.
        apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
        apply IHk in comp0; eauto 3 with slow;[].
        repndors; exrepnd; subst; simpl in *.

        { left; exists c1 c2 k1 (S k2); simpl; dands; auto; try omega.
          { rw @computes_to_can_in_max_k_steps_S; eexists; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. }
          rw  <- plus_n_Sm; autorewrite with slow.
          assert (k1 + S k2 = k1 + k2 + 1) as e by omega; rewrite e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { right; right.
          exists en e w k1 (S k2); dands; auto; try omega.
          { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. } }

      * SCase "Exc".
        csunf comp1; simpl in comp1; ginv.
        right; right.
        apply wf_exception_implies in wf2; exrepnd; tcsp; subst; fold_terms.
        apply computes_to_val_like_in_max_k_steps_exc_iff in comp0; subst.
        exists a t (oterm (Can can1) l) 0 0; simpl; dands; auto; try omega;
          allrw @computes_to_can_in_max_k_steps_0;
          allrw @reduces_in_atmost_k_steps_0; tcsp.

      * SCase "Abs".
        csunf comp1; simpl in comp1.
        apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
        apply IHk in comp0; eauto 3 with slow;[].
        repndors; exrepnd; subst; simpl in *.

        { left; exists c1 c2 k1 (S k2); simpl; dands; auto; try omega.
          { rw @computes_to_can_in_max_k_steps_S; eexists; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. }
          rw  <- plus_n_Sm; autorewrite with slow.
          assert (k1 + S k2 = k1 + k2 + 1) as e by omega; rewrite e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { right; right.
          exists en e w k1 (S k2); dands; auto; try omega.
          { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. } }

    + Case "NCan".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists c1 c2 (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

      * right; right.
        exists en e w (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

    + Case "NSwapCs2".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists c1 c2 (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

      * right; right.
        exists en e w (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply wf_exception_implies in wf1; exrepnd; subst; simpl in *; fold_terms.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right; left.
      exists a t 0; dands; auto; try omega.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists c1 c2 (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

      * right; right.
        exists en e w (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.
Qed.

Lemma approx_starbts_nil_left {o} :
  forall (lib : @plibrary o) c bs,
    approx_starbts c lib [] bs
    -> bs = [].
Proof.
  introv apr; unfold approx_starbts in *; simpl in *.
  unfold lblift_sub in *; simpl in *; repnd.
  destruct bs; simpl in *; ginv.
Qed.

Lemma implies_approx_star_mk_swap_cs1 {o} :
  forall lib (a b c u v w : @NTerm o),
    approx_star lib a u
    -> approx_star lib b v
    -> approx_star lib c w
    -> approx_star lib (mk_swap_cs1 a b c) (mk_swap_cs1 u v w).
Proof.
  introv apra aprb aprc.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_swap_cs1 : slow.

Lemma implies_approx_star_mk_swap_cs2 {o} :
  forall lib sw (c d : @NTerm o),
    approx_star lib c d
    -> approx_star lib (mk_swap_cs2 sw c) (mk_swap_cs2 sw d).
Proof.
  introv apra.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_swap_cs2 : slow.

Lemma nrut_sub_app_implies_disjoint_l {o} :
  forall lib (a b : @NTerm o) sub,
    nrut_sub (get_utokens_lib lib a ++ get_utokens_lib lib b) sub
    -> disjoint (sub_free_vars sub) (all_vars a).
Proof.
  introv nrut.
  unfold nrut_sub in *; repnd.
  apply ut_sub_implies_cl_sub in nrut0.
  rewrite sub_free_vars_if_cl_sub; auto.
Qed.
Hint Resolve nrut_sub_app_implies_disjoint_l : slow.

Lemma nrut_sub_app_implies_disjoint_r {o} :
  forall lib (a b : @NTerm o) sub,
    nrut_sub (get_utokens_lib lib a ++ get_utokens_lib lib b) sub
    -> disjoint (sub_free_vars sub) (all_vars b).
Proof.
  introv nrut.
  unfold nrut_sub in *; repnd.
  apply ut_sub_implies_cl_sub in nrut0.
  rewrite sub_free_vars_if_cl_sub; auto.
Qed.
Hint Resolve nrut_sub_app_implies_disjoint_r : slow.

Lemma lsubst_mk_choice_seq {o} :
  forall c (sub : @Sub o),
    lsubst (mk_choice_seq c) sub = mk_choice_seq c.
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @lsubst_mk_choice_seq : slow.

Lemma isprogram_lsubst_push_swap_cs_can_implies {o} :
  forall sw can (bs : list (@BTerm o)) sub,
    isprogram (lsubst (push_swap_cs_can sw can bs) sub)
    -> isprogram (lsubst (oterm (Can can) bs) sub).
Proof.
  introv isp.
  allrw @isprogram_lsubst_iff; repnd.
  apply nt_wf_push_swap_cs_can_implies in isp0; dands; auto.
  introv i.
  apply isp; simpl in *; autorewrite with slow; auto.
Qed.

Lemma implies_compute_at_most_k_steps_mk_swap_cs1 {o} :
  forall lib k1 k2 (a b t : @NTerm o) v u,
    iscan v
    -> compute_at_most_k_steps lib k1 a = csuccess v
    -> compute_at_most_k_steps lib k2 b = csuccess u
    -> {j : nat & j <= k1 + k2 # compute_at_most_k_steps lib j (mk_swap_cs1 a b t) = csuccess (mk_swap_cs1 v u t)}.
Proof.
  induction k2; introv isc comp1 comp2; simpl in *; ginv.

  { apply (computes_atmost_ksteps_prinarg lib NSwapCs1 _ [nobnd u, nobnd t]) in comp1; exrepnd; fold_terms.
    exists j; dands; try omega; auto. }

  remember (compute_at_most_k_steps lib k2 b) as comp; symmetry in Heqcomp; destruct comp; ginv;[].
  eapply (IHk2 a b t) in Heqcomp; eauto; exrepnd.
  destruct n as [x|op bs]; simpl in *.
  { csunf comp2; simpl in *; ginv. }
  destruct op; simpl in *.
  { csunf comp2; simpl in *; ginv.
    exists j; dands; try omega; auto. }
  { exists (S j); dands; try omega.
    simpl; allrw.
    unfold mk_swap_cs1, nobnd, mk_choice_seq.
    apply iscan_implies in isc; exrepnd; subst.
    rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow; allrw; auto. }
  { exists (S j); dands; try omega.
    simpl; allrw.
    unfold mk_swap_cs1, nobnd, mk_choice_seq.
    apply iscan_implies in isc; exrepnd; subst.
    rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow; allrw; auto. }
  { csunf comp2; simpl in *; ginv.
    exists j; dands; try omega; auto. }
  { exists (S j); dands; try omega.
    simpl; allrw.
    unfold mk_swap_cs1, nobnd, mk_choice_seq.
    apply iscan_implies in isc; exrepnd; subst.
    rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow; allrw; auto. }
Qed.

Lemma implies_reduces_to_mk_swap_cs1 {o} :
  forall lib (a b t : @NTerm o) v u,
    a =v>(lib) v
    -> reduces_to lib b u
    -> reduces_to lib (mk_swap_cs1 a b t) (mk_swap_cs1 v u t).
Proof.
  introv comp1 comp2.
  unfold computes_to_value, reduces_to in *; exrepnd.
  eapply implies_compute_at_most_k_steps_mk_swap_cs1 in comp3; try exact comp2; exrepnd; eauto 3 with slow.
Qed.

Lemma implies_reduces_to_mk_swap_cs1_val {o} :
  forall lib (a b t : @NTerm o) c1 c2,
    a =v>(lib) (mk_choice_seq c1)
    -> b =v>(lib) (mk_choice_seq c2)
    -> reduces_to lib (mk_swap_cs1 a b t) (mk_swap_cs1 (mk_choice_seq c1) (mk_choice_seq c2) t).
Proof.
  introv comp1 comp2.
  unfold computes_to_value, reduces_to in *; exrepnd.
  eapply implies_compute_at_most_k_steps_mk_swap_cs1 in comp4; try exact comp0; exrepnd; eauto 3 with slow.
Qed.

Lemma approx_starbts_cons_implies {o} :
  forall lib op (b : @BTerm o) bs l,
    approx_starbts lib op (b :: bs) l -> {a : BTerm & {k : list BTerm & l = a :: k}}.
Proof.
  introv aps.
  unfold approx_starbts in *.
  unfold lblift_sub in *; simpl in *; repnd.
  destruct l; simpl in *; tcsp.
  eexists; eexists; dands; eauto.
Qed.

Lemma implies_alpha_eq_bterm_mk_swap_cs2 {o} :
  forall sw l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq_bterm (bterm l1 (mk_swap_cs2 sw t1)) (bterm l2 (mk_swap_cs2 sw t2)).
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst.
  eapply al_bterm; autorewrite with slow; eauto.
  repeat (rewrite lsubst_mk_swap_cs2_choice_seq_var_ren; try rewrite computation_mark.sub_free_vars_var_ren; eauto 3 with slow; try omega).
Qed.
Hint Resolve implies_alpha_eq_bterm_mk_swap_cs2 : slow.

Lemma flat_map_trivial :
  forall {T} (l : list T),
    flat_map (fun x => [x]) l = l.
Proof.
  induction l; introv; simpl; auto; try congruence.
Qed.
Hint Rewrite @flat_map_trivial : slow.

Lemma alpha_eq_change_bvars_alpha {o} :
  forall l (t : @NTerm o),
    alpha_eq (change_bvars_alpha l t) t.
Proof.
  introv.
  pose proof (change_bvars_alpha_spec t l) as q; simpl in *; repnd; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_change_bvars_alpha : slow.

Lemma lsubst_sw_sub_alpha_eq_aux {o} :
  forall (t : @NTerm o) sw l,
    alpha_eq (lsubst t (sw_sub sw l)) (lsubst_aux t (sw_sub sw l)).
Proof.
  introv; unfold lsubst; autorewrite with slow.
  rewrite flat_map_map; unfold compose; simpl; autorewrite with slow; boolvar; eauto 3 with slow.
Qed.
Hint Resolve lsubst_sw_sub_alpha_eq_aux : slow.

Lemma implies_approx_star_push_swap_cs_sub_term {o} :
  forall lib sw l (c d : @NTerm o),
    approx_star lib c d
    -> approx_star lib (push_swap_cs_sub_term sw l c) (push_swap_cs_sub_term sw l d).
Proof.
  introv apra.
  unfold push_swap_cs_sub_term.
  apply (lsubst_approx_star_congr3 _ _ _ (sw_sub sw l)) in apra; eauto 3 with slow.
Qed.
Hint Resolve implies_approx_star_push_swap_cs_sub_term : slow.

Lemma implies_alpha_eq_bterm_mk_swap_cs2_push_swap_cs_sub_term {o} :
  forall sw l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq_bterm
         (bterm l1 (mk_swap_cs2 sw (push_swap_cs_sub_term sw l1 t1)))
         (bterm l2 (mk_swap_cs2 sw (push_swap_cs_sub_term sw l2 t2))).
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst; clear aeq.
  econstructor; try exact lenb; auto.

  { unfold all_vars in *; simpl in *; autorewrite with slow; tcsp. }

  allrw disjoint_app_r; repnd.
  repeat (rewrite lsubst_lsubst_aux; simpl; autorewrite with slow;
          [|rewrite flat_map_free_var_vars_range; auto; eauto 2 with slow; try omega];[]).
  apply implies_alpha_eq_mk_swap_cs2.
  unfold push_swap_cs_sub_term.

  repeat (rewrite lsubst_aux_sw_sub_var_ren; auto; try omega;[]).
  repeat (rewrite <- lsubst_push_swap_cs_sub_term_var_ren_eq2; auto; allrw disjoint_app_r; tcsp;[]).
  apply implies_alpha_eq_lsubst_aux_sw_sub; auto.
Qed.
Hint Resolve implies_alpha_eq_bterm_mk_swap_cs2_push_swap_cs_sub_term : slow.

Lemma approx_star_bterm_push_swap_cs_bterm {o} :
  forall lib can sw (b1 b2 : @BTerm o),
    approx_star_bterm (Can can) lib b1 b2
    -> approx_star_bterm
         (Can (swap_cs_can sw can))
         lib
         (push_swap_cs_bterm sw b1)
         (push_swap_cs_bterm sw b2).
Proof.
  introv apr.
  unfold approx_star_bterm in *.
  unfold blift_sub in *; exrepnd.
  destruct b1 as [l1 t1].
  destruct b2 as [l2 t2].
  simpl in *.

  exists lv (mk_swap_cs2 sw (push_swap_cs_sub_term sw lv nt1)) (mk_swap_cs2 sw (push_swap_cs_sub_term sw lv nt2)).
  dands; eauto 3 with slow;[].
  repndors; exrepnd;[left|right]; ginv.
  dands; tcsp; try (complete(intro xx; inversion xx)); eauto 3 with slow.
Qed.
Hint Resolve approx_star_bterm_push_swap_cs_bterm : slow.

Lemma approx_star_push_swap_cs_can {o} :
  forall lib sw can (bs1 bs2 : list (@BTerm o)),
    nt_wf (push_swap_cs_can sw can bs2)
    -> approx_starbts (Can can) lib bs1 bs2
    -> approx_star lib (push_swap_cs_can sw can bs1) (push_swap_cs_can sw can bs2).
Proof.
  introv wf aps.
  apply approx_star_congruence2; auto.
  clear wf.
  revert dependent bs2; induction bs1; introv aps.
  { apply approx_starbts_nil_left in aps; subst; simpl; eauto 3 with slow. }
  applydup @approx_starbts_cons_implies in aps; exrepnd; subst.
  apply approx_starbts_cons in aps; repnd.
  apply IHbs1 in aps; simpl.
  apply approx_starbts_cons; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve approx_star_push_swap_cs_can : slow.

(*Lemma implies_compute_at_most_k_steps_mk_swap_cs2 {o} :
  forall lib k sw (t u : @NTerm o),
    compute_at_most_k_steps lib k t = csuccess u
    -> {j : nat & j <= k # compute_at_most_k_steps lib j (mk_swap_cs2 sw t) = csuccess (mk_swap_cs2 sw u)}.
Proof.
  introv comp.
  apply (computes_atmost_ksteps_prinarg lib (NSwapCs2 sw) _ []) in comp; exrepnd; fold_terms.
  exists j; dands; try omega; auto.
Qed.*)

(*Lemma implies_reduces_to_mk_swap_cs2 {o} :
  forall lib sw (t u : @NTerm o),
    t =v>(lib) u
    -> reduces_to lib (mk_swap_cs2 sw t) (mk_swap_cs2 sw u).
Proof.
  introv comp1.
  unfold computes_to_value, reduces_to in *; exrepnd.
  eapply implies_compute_at_most_k_steps_mk_swap_cs2 in comp2; exrepnd; eauto.
Qed.*)

Lemma swap_cs_soterm_idem {o} :
  forall (r : cs_swap)
         (t : @SOTerm o),
    swap_cs_soterm r (swap_cs_soterm r t) = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; auto;[|].

  { Case "sovar".
    f_equal.
    rewrite map_map; unfold compose; simpl.
    apply eq_map_l; introv i.
    apply ind in i; auto. }

  { Case "soterm".
    autorewrite with slow.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i.
    destruct x; apply ind in i.
    simpl; f_equal; auto. }
Qed.
Hint Rewrite @swap_cs_soterm_idem : slow.

Lemma swap_cs_choice_seq_vals_idem {o} :
  forall sw (vals : @ChoiceSeqVals o),
    swap_cs_choice_seq_vals sw (swap_cs_choice_seq_vals sw vals) = vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals.
  rewrite map_map; unfold compose; simpl.
  apply eq_map_l; introv i; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_vals_idem : slow.

Lemma swap_cs_choice_seq_restr_idem {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    swap_cs_choice_seq_restr sw (swap_cs_choice_seq_restr sw restr)
    = restr.
Proof.
  destruct restr; simpl; autorewrite with slow; dands; f_equal.

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }

(*  { apply functional_extensionality; introv; autorewrite with slow; auto. }

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }*)
Qed.
Hint Rewrite @swap_cs_choice_seq_restr_idem : slow.

Lemma swap_cs_choice_seq_entry_idem {o} :
  forall sw (entry : @ChoiceSeqEntry o),
    swap_cs_choice_seq_entry
      sw
      (swap_cs_choice_seq_entry sw entry)
    = entry.
Proof.
  introv.
  unfold swap_cs_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_entry_idem : slow.

Lemma swap_cs_lib_entry_idem {o} :
  forall sw (e : @library_entry o),
    swap_cs_lib_entry sw (swap_cs_lib_entry sw e) = e.
Proof.
  introv; destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow.

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Rewrite @swap_cs_lib_entry_idem : slow.

Lemma swap_cs_plib_idem {o} :
  forall sw (lib : @plibrary o),
    swap_cs_plib sw (swap_cs_plib sw lib) = lib.
Proof.
  induction lib; introv; simpl; dands; auto.
  autorewrite with slow; tcsp; try congruence.
Qed.
Hint Rewrite @swap_cs_plib_idem : slow.

Lemma swap_cs_bterm_idem {o} :
  forall sw (b : @BTerm o),
    swap_cs_bterm sw (swap_cs_bterm sw b) = b.
Proof.
  introv; destruct b; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_bterm_idem : slow.

Lemma implies_alpha_eq_bterm_swap_cs_bterm {o} :
  forall sw (a b : @BTerm o),
    alpha_eq_bterm a b
    -> alpha_eq_bterm (swap_cs_bterm sw a) (swap_cs_bterm sw b).
Proof.
  introv aeq; destruct a, b; simpl in *.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst; clear aeq.
  econstructor; autorewrite with slow; eauto.
  apply (implies_alpha_eq_swap_cs_term sw) in aeq'.
  repeat rewrite <- lsubst_swap_cs_term in aeq'; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_alpha_eq_bterm_swap_cs_bterm : slow.

Lemma implies_wf_sub_swap_cs_sub {o} :
  forall sw (sub : @Sub o),
    wf_sub sub
    -> wf_sub (swap_cs_sub sw sub).
Proof.
  induction sub; introv wf; repnd; simpl in *; auto.
  allrw @wf_sub_cons_iff; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_wf_sub_swap_cs_sub : slow.

Lemma swap_cs_sub_idem {o} :
  forall sw (sub : @Sub o),
    swap_cs_sub sw (swap_cs_sub sw sub) = sub.
Proof.
  induction sub; introv; repnd; simpl; auto; autorewrite with slow; auto; try congruence.
Qed.
Hint Rewrite @swap_cs_sub_idem : slow.

Lemma implies_approx_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx lib a b
    -> approx (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  cofix ind; introv apx.
  applydup @approx_relates_only_progs in apx as isp; repnd.
  constructor; unfold close_comput; dands; eauto 2 with slow;[|].

  { (* VAL case *)
    introv comp.
    apply (@swap_computes_to_value o sw) in comp.
    autorewrite with slow in comp; simpl in *.

    eapply approx_canonical_form in apx;[|eauto]; exrepnd.
    apply (@swap_computes_to_value o sw) in apx1.
    simpl in *; autorewrite with slow in *.
    eexists; dands; eauto.
    unfold lblift in *; autorewrite with slow in *; repnd; dands; auto.
    introv len; applydup apx0 in len.
    unfold blift in *; exrepnd.
    exists lv (swap_cs_term sw nt1) (swap_cs_term sw nt2).
    rewrite selectbt_map in len2; auto.
    apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len2.
    apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len1.
    simpl in *; autorewrite with slow in *.
    rewrite selectbt_map; auto; try congruence;[].
    dands; auto;[].

    introv.
    unfold approx_open, olift in *; repnd; dands; eauto 3 with slow;[].
    introv wf ispa ispb; left.
    pose proof (len0 (swap_cs_sub sw sub)) as len0.
    apply (implies_isprogram_swap_cs_term sw) in ispa.
    apply (implies_isprogram_swap_cs_term sw) in ispb.
    rewrite swap_cs_term_lsubst in ispa.
    rewrite swap_cs_term_lsubst in ispb.
    autorewrite with slow in *.
    repeat (autodimp len0 hyp); eauto 2 with slow.
    apply (ind _ sw) in len0.
    repeat rewrite <- lsubst_swap_cs_term in len0.
    autorewrite with slow in len0; exact len0. }

  { (* EXC case *)

    introv comp.
    apply (@swap_reduces_to o sw) in comp.
    autorewrite with slow in comp; simpl in *; fold_terms.

    eapply exception_approx in comp; eauto; exrepnd; repndors; tcsp;
      try (complete (inversion comp2)); try (complete (inversion comp1));[].
    apply (@swap_reduces_to o sw) in comp0; simpl in *; fold_terms.
    eexists; eexists; dands; eauto; left.
    { apply (ind _ sw) in comp2; autorewrite with slow in *; auto. }
    { apply (ind _ sw) in comp1; autorewrite with slow in *; auto. } }
Qed.

Lemma implies_approx_open_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx_open lib a b
    -> approx_open (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  introv apx.
  unfold approx_open, olift in *; repnd; dands; eauto 3 with slow.
  introv wf ispa ispb.
  pose proof (apx (swap_cs_sub sw sub)) as apx.
  apply (implies_isprogram_swap_cs_term sw) in ispa.
  apply (implies_isprogram_swap_cs_term sw) in ispb.
  rewrite swap_cs_term_lsubst in ispa.
  rewrite swap_cs_term_lsubst in ispb.
  autorewrite with slow in *.
  repeat (autodimp apx hyp); eauto 2 with slow.
  apply (implies_approx_swap_cs_term _ sw) in apx.
  repeat rewrite swap_cs_term_lsubst in apx.
  autorewrite with slow in *; auto.
Qed.

Lemma alpha_eq_bterm_preserves_osize_bterm {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> osize_bterm b1 = osize_bterm b2.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst; clear aeq.
  apply alpha_eq_preserves_osize in aeq'.
  repeat (rewrite lsubst_allvars_preserves_osize in aeq'; eauto 3 with slow).
Qed.

Lemma swap_cs_sub_if_nrut_sub {o} :
  forall sw (sub : @Sub o) l,
    nrut_sub l sub
    -> swap_cs_sub sw sub = sub.
Proof.
  induction sub; introv h; repnd; simpl; auto.
  allrw @nrut_sub_cons; exrepnd; subst; simpl in *; fold_terms.
  erewrite IHsub; eauto.
Qed.

Lemma implies_approx_star_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx_star lib a b
    -> approx_star (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv apx.
  { inversion apx as [? ? ? apx'|]; subst; clear apx.
    apply (implies_approx_open_swap_cs_term _ sw) in apx'; simpl in *.
    constructor; auto. }

  inversion apx as [|? ? ? ? ? len bl apo]; subst; clear apx; simpl in *.
  apply (implies_approx_open_swap_cs_term _ sw) in apo; simpl in *.
  apply (apso _ _ _ _ (map (swap_cs_bterm sw) lbt1')); autorewrite with slow; auto;[].
  unfold lblift_sub in *; repnd; autorewrite with slow in *; dands; auto; GC.
  introv len'; applydup bl in len'.
  repeat (rewrite selectbt_map; auto; try congruence);[].
  unfold blift_sub in *; exrepnd.
  exists lv (swap_cs_term sw nt1) (swap_cs_term sw nt2).
  apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len'1.
  apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len'2.
  simpl in *; dands; auto;[].
  repndors; exrepnd;[left|right].

  { dands; auto.
    { destruct op; simpl in *; tcsp; try (complete (intro xx; ginv)). }
    remember (bs {[n]}) as bt; destruct bt as [l t].
    eapply (ind t nt1 l); auto.
    { allrw; apply selectbt_in; auto. }
    apply alpha_eq_bterm_preserves_osize_bterm in len'2.
    simpl in *; autorewrite with slow in *; allrw; eauto 3 with slow. }

  subst; simpl in *.
  remember (bs {[n]}) as bt; destruct bt as [l t].
  eapply (ind t _ l) in len'4;
    try (complete (allrw; apply selectbt_in; auto));
    try (complete (rewrite simple_osize_lsubst; eauto 3 with slow;
                   apply alpha_eq_bterm_preserves_osize_bterm in len'2;
                   simpl in *; autorewrite with slow in *; allrw; eauto 3 with slow)).
  repeat rewrite <- lsubst_swap_cs_term in len'4.
  repeat (erewrite swap_cs_sub_if_nrut_sub in len'4; eauto).
  exists sub; dands; autorewrite with slow; auto.
Qed.

Lemma isprogram_mk_swap_cs2_implies {o} :
  forall sw (t : @NTerm o),
    isprogram (mk_swap_cs2 sw t)
    -> isprogram t.
Proof.
  introv isp.
  unfold isprogram, closed in *; simpl in *; autorewrite with slow in *; repnd; dands; auto.
  apply nt_wf_mk_swap_cs2_implies in isp; auto.
Qed.

Lemma isprogram_swap_cs_term_implies {o} :
  forall sw (t : @NTerm o),
    isprogram (swap_cs_term sw t)
    -> isprogram t.
Proof.
  introv isp.
  unfold isprogram, closed in *; simpl in *; autorewrite with slow in *; repnd; dands; auto.
  apply (implies_nt_wf_swap_cs_term sw) in isp; autorewrite with slow in *; auto.
Qed.

Lemma swap_cs_in_lib_entry_idem {o} :
  forall sw (e : @library_entry o),
    swap_cs_in_lib_entry sw (swap_cs_in_lib_entry sw e) = e.
Proof.
  introv; destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow.

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Rewrite @swap_cs_in_lib_entry_idem : slow.

Lemma swap_cs_in_plib_idem {o} :
  forall sw (lib : @plibrary o),
    swap_cs_in_plib sw (swap_cs_in_plib sw lib) = lib.
Proof.
  induction lib; introv; simpl; dands; auto.
  autorewrite with slow; tcsp; try congruence.
Qed.
Hint Rewrite @swap_cs_in_plib_idem : slow.
