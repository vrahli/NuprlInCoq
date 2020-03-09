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


Require Export approx_star0.


Lemma isprogram_swap_cs1_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NSwapCs1) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c]
           # isprogram a
           # isprogram b
           # isprogram c }}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b, b0, b1; simpl in *; ginv.
  destruct l, l0, l1; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto;
    dLin_hyp; allapply @isprogram_bt_nobnd; auto.
Qed.

Lemma isprogram_swap_cs1_iff {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NSwapCs1) bterms)
    <=> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
        $ bterms = [bterm [] a, bterm [] b, bterm [] c]
        # isprogram a
        # isprogram b
        # isprogram c }}}.
Proof.
  introv; split; intro k.
  apply isprogram_swap_cs1_implies in k; auto.
  exrepnd; subst.
  apply isprogram_ot_iff; unfold num_bvars; simpl; sp; subst;
    apply implies_isprogram_bt0; auto.
Qed.

Lemma compute_step_swap_cs1_aux_success_implies {o} :
  forall can1 can2 l1 l2 bs (t : @NTerm o) u,
    compute_step_swap_cs1_aux can1 can2 l1 l2 bs t = csuccess u
    -> {n1 : choice_sequence_name
       & {n2 : choice_sequence_name
       & {w : NTerm
       & can1 = Ncseq n1
       # can2 = Ncseq n2
       # l1 = []
       # l2 = []
       # bs = [bterm [] w]
       # u = mk_swap_cs2 n1 n2 w }}}.
Proof.
  introv comp.
  unfold compute_step_swap_cs2 in comp.
  destruct can1; simpl in comp; ginv.
  destruct can2; simpl in comp; ginv.
  destruct l1; simpl in comp; ginv.
  destruct l2; simpl in comp; ginv.
  destruct bs as [|b]; ginv.
  destruct b; simpl in *; ginv.
  destruct l; simpl in *; ginv.
  destruct bs; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto.
Qed.

Hint Rewrite @minus0 : slow.
Hint Rewrite @Nat.add_0_r : slow.

Lemma on_success_csuccess {o} :
  forall (r : @Comput_Result o) f t,
    on_success r f = csuccess t
    -> {u : NTerm & r = csuccess u # t = f u}.
Proof.
  introv h.
  destruct r; simpl in *; ginv; eauto.
Qed.

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
           (mk_swap_cs2 c1 c2 n3)
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
    dopid o as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (csunf comp1; allsimpl; ginv));[].
      dopid o as [can2|ncan2|exc2|abs2] SCase.

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
    approx_starbts lib c [] bs
    -> bs = [].
Proof.
  introv apr; unfold approx_starbts in *; simpl in *.
  unfold lblift_sub in *; simpl in *; repnd.
  destruct bs; simpl in *; ginv.
Qed.

Lemma implies_isprog_vars_mk_swap_cs1 {o} :
  forall l n1 n2 (t : @NTerm o),
    isprog_vars l n1
    -> isprog_vars l n2
    -> isprog_vars l t
    -> isprog_vars l (mk_swap_cs1 n1 n2 t).
Proof.
  introv ispa ipsb ispc.
  unfold mk_swap_cs1; apply isprog_vars_ot_iff; simpl; dands; tcsp.
  introv i; repndors; subst; tcsp; unfold nobnd in *; ginv; autorewrite with slow; auto.
Qed.
Hint Resolve implies_isprog_vars_mk_swap_cs1 : slow.

Lemma implies_isprog_vars_mk_swap_cs2 {o} :
  forall l n1 n2 (t : @NTerm o),
    isprog_vars l t
    -> isprog_vars l (mk_swap_cs2 n1 n2 t).
Proof.
  introv ispa.
  unfold mk_swap_cs2; apply isprog_vars_ot_iff; simpl; dands; tcsp.
  introv i; repndors; subst; tcsp; unfold nobnd in *; ginv; autorewrite with slow; auto.
Qed.
Hint Resolve implies_isprog_vars_mk_swap_cs2 : slow.

Lemma implies_isprogram_mk_swap_cs1 {o} :
  forall n1 n2 (t : @NTerm o),
    isprogram n1
    -> isprogram n2
    -> isprogram t
    -> isprogram (mk_swap_cs1 n1 n2 t).
Proof.
  introv ispa ipsb ispc.
  allrw @isprogram_eq; allrw @isprog_vars_nil_iff_isprog; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_swap_cs1 : slow.

Lemma implies_isprogram_mk_swap_cs2 {o} :
  forall n1 n2 (t : @NTerm o),
    isprogram t
    -> isprogram (mk_swap_cs2 n1 n2 t).
Proof.
  introv ispa.
  allrw @isprogram_eq; allrw @isprog_vars_nil_iff_isprog; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_swap_cs2 : slow.

Lemma isprog_vars_mk_choice_seq {o} :
  forall l n, @isprog_vars o l (mk_choice_seq n).
Proof.
  introv; apply isprog_vars_ot_iff; simpl; dands; tcsp.
Qed.
Hint Resolve isprog_vars_mk_choice_seq : slow.

Lemma implies_isprogram_push_swap_cs_can {o} :
  forall c1 c2 can (bs : list (@BTerm o)),
    isprogram (oterm (Can can) bs)
    -> isprogram (push_swap_cs_can c1 c2 can bs).
Proof.
  introv isp.
  unfold push_swap_cs_can.
  allrw @isprogram_ot_iff; simpl; autorewrite with slow in *; repnd; dands; auto.
  introv i.
  unfold push_swap_cs_bterms in i; apply in_map_iff in i; exrepnd; subst.
  destruct a; simpl.
  apply isp in i1.
  allrw @isprogram_bt_iff_isprog_vars; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_push_swap_cs_can : slow.

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
  forall lib a b (c d : @NTerm o),
    approx_star lib c d
    -> approx_star lib (mk_swap_cs2 a b c) (mk_swap_cs2 a b d).
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

Lemma nt_wf_mk_swap_cs1_implies {o} :
  forall (a b c : @NTerm o),
    nt_wf (mk_swap_cs1 a b c)
    -> nt_wf a # nt_wf b # nt_wf c.
Proof.
  introv wf.
  unfold mk_swap_cs1 in *.
  allrw @nt_wf_oterm_iff; autorewrite with slow in *; repnd; dands; auto;
    simpl in *; dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_mk_swap_cs2_implies {o} :
  forall a b (c : @NTerm o),
    nt_wf (mk_swap_cs2 a b c)
    -> nt_wf c.
Proof.
  introv wf.
  unfold mk_swap_cs1 in *.
  allrw @nt_wf_oterm_iff; autorewrite with slow in *; repnd; dands; auto;
    simpl in *; dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_push_swap_cs_can_implies {o} :
  forall c1 c2 can (bs : list (@BTerm o)),
    nt_wf (push_swap_cs_can c1 c2 can bs)
    -> nt_wf (oterm (Can can) bs).
Proof.
  introv wf.
  unfold push_swap_cs_can in *.
  allrw @nt_wf_oterm_iff; simpl in *; autorewrite with slow in *; repnd; dands; auto.
  introv i.
  pose proof (wf (push_swap_cs_bterm c1 c2 b)) as wf.
  autodimp wf hyp.
  { apply in_map_iff; eexists; dands; eauto. }
  destruct b; simpl in *.
  allrw @bt_wf_iff.
  apply nt_wf_mk_swap_cs2_implies in wf; tcsp.
Qed.

Lemma isprogram_lsubst_push_swap_cs_can_implies {o} :
  forall c1 c2 can (bs : list (@BTerm o)) sub,
    isprogram (lsubst (push_swap_cs_can c1 c2 can bs) sub)
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

Lemma isprogram_swap_cs2_implies {p} :
  forall nfo (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NSwapCs2 nfo)) bterms)
    -> {a : NTerm $ bterms = [bterm [] a] # isprogram a }.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; simpl in *; ginv.
  destruct l; simpl in *; ginv.
  eexists; dands; eauto; dLin_hyp; allapply @isprogram_bt_nobnd; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_swap_cs2_implies {o} :
  forall lib k nfo n (v : @NTerm o),
    wf_term n
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NCan (NSwapCs2 nfo)) [nobnd n])
         v
         k
    -> {can : CanonicalOp
       $ {bs : list BTerm
       $ {k1 : nat
       $ k1+1 <= k
       # computes_to_can_in_max_k_steps lib k1 n (oterm (Can can) bs)
       # reduces_in_atmost_k_steps lib
           (oterm (NCan (NSwapCs2 nfo)) [nobnd n])
           (oterm (NCan (NSwapCs2 nfo))
                  [nobnd (oterm (Can can) bs)])
           k1
       # computes_to_val_like_in_max_k_steps lib
           (push_swap_cs_can (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) can bs)
           v
           (k - (k1 + 1))
       }}}
       [+]
       {en, e : NTerm
       $ {k1 : nat
       $ k1 + 1 <= k
       # v = mk_exception en e
       # computes_to_exception_in_max_k_steps lib en n e k1
       # reduces_in_atmost_k_steps lib
           (oterm (NCan (NSwapCs2 nfo)) [nobnd n])
           (oterm (NCan (NSwapCs2 nfo)) [nobnd v])
           k1
       }}.
Proof.
  induction k; introv wf comp.

  - destruct comp as [r is].
    inversion r; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n; try (complete (inversion comp1));[].
    dopid o0 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf comp1; simpl in *; ginv.
      left.
      exists can1 l 0; simpl; dands; try omega;
        allrw @computes_to_can_in_max_k_steps_0;
        allrw @reduces_in_atmost_k_steps_0;
        autorewrite with slow; dands; eauto 3 with slow.

    + Case "NCan".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists can bs (S k1); dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply wf_exception_implies in wf; exrepnd; subst; simpl in *; fold_terms.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right.
      exists a t 0; dands; auto; try omega.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists can bs (S k1); dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.
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
  forall n1 n2 l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq_bterm (bterm l1 (mk_swap_cs2 n1 n2 t1)) (bterm l2 (mk_swap_cs2 n1 n2 t2)).
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst.
  eapply al_bterm; autorewrite with slow; eauto.
  repeat (rewrite lsubst_mk_swap_cs2_choice_seq_var_ren; try rewrite computation_mark.sub_free_vars_var_ren; eauto 3 with slow; try omega).
Qed.
Hint Resolve implies_alpha_eq_bterm_mk_swap_cs2 : slow.

Lemma approx_star_bterm_push_swap_cs_bterm {o} :
  forall lib can n1 n2 (b1 b2 : @BTerm o),
    approx_star_bterm lib (Can can) b1 b2
    -> approx_star_bterm
         lib
         (Can (swap_cs_can (n1, n2) can))
         (push_swap_cs_bterm n1 n2 b1)
         (push_swap_cs_bterm n1 n2 b2).
Proof.
  introv apr.
  unfold approx_star_bterm in *.
  unfold blift_sub in *; exrepnd.
  destruct b1 as [l1 t1].
  destruct b2 as [l2 t2].
  simpl in *.

  exists lv (mk_swap_cs2 n1 n2 nt1) (mk_swap_cs2 n1 n2 nt2).
  dands; eauto 3 with slow.
  repndors; exrepnd;[left|right]; ginv.
  dands; tcsp; try (complete(intro xx; inversion xx)); eauto 3 with slow.
Qed.
Hint Resolve approx_star_bterm_push_swap_cs_bterm : slow.

Lemma approx_star_push_swap_cs_can {o} :
  forall lib n1 n2 can (bs1 bs2 : list (@BTerm o)),
    nt_wf (push_swap_cs_can n1 n2 can bs2)
    -> approx_starbts lib (Can can) bs1 bs2
    -> approx_star lib (push_swap_cs_can n1 n2 can bs1) (push_swap_cs_can n1 n2 can bs2).
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

Lemma implies_compute_at_most_k_steps_mk_swap_cs2 {o} :
  forall lib k a b (t u : @NTerm o),
    compute_at_most_k_steps lib k t = csuccess u
    -> {j : nat & j <= k # compute_at_most_k_steps lib j (mk_swap_cs2 a b t) = csuccess (mk_swap_cs2 a b u)}.
Proof.
  introv comp.
  apply (computes_atmost_ksteps_prinarg lib (NSwapCs2 (MkSwapCsNfo a b)) _ []) in comp; exrepnd; fold_terms.
  exists j; dands; try omega; auto.
Qed.

Lemma implies_reduces_to_mk_swap_cs2 {o} :
  forall lib a b (t u : @NTerm o),
    t =v>(lib) u
    -> reduces_to lib (mk_swap_cs2 a b t) (mk_swap_cs2 a b u).
Proof.
  introv comp1.
  unfold computes_to_value, reduces_to in *; exrepnd.
  eapply implies_compute_at_most_k_steps_mk_swap_cs2 in comp2; exrepnd; eauto.
Qed.
