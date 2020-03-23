(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University
  Copyright 2019 Cornell University

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


Require Export rules_choice_util5.


Definition swap_cs_bterms {o} sw (bs : list (@BTerm o)) :=
  map (swap_cs_bterm sw) bs.

Lemma swap_cs_bterms_twice {o} :
  forall sw (bs : list (@BTerm o)),
    map (swap_cs_bterm sw) (map (swap_cs_bterm sw) bs)
    = bs.
Proof.
  induction bs; simpl;auto; allrw;autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_bterms_twice : slow.

Lemma compute_step_swap_implies_cs2 {o} :
  forall (cond : @LibCond o) (lib : @plibrary o) n1 n2 t (u : NTerm),
    n1 <> n2
    -> sw_not_in_lib (n1, n2) lib
    -> lib_nodup lib
    -> im_swap_lib lib
    -> strong_sat_cond_lib cond lib
    -> lib_cond_no_cs cond
    -> compute_step lib (swap_cs_term (n1,n2) t) = csuccess u
    -> reduces_to lib (mk_swap_cs2 n1 n2 t) (mk_swap_cs2 n1 n2 (swap_cs_term (n1,n2) u)).
Proof.
  introv d ni nodup im sat nocs comp.
  apply (swap_compute_step (n1,n2)) in comp; autorewrite with slow in comp.
  erewrite swap_cs_plib_trivial_if_no_cs in comp; eauto.
  eapply reduces_to_prinarg; eauto 3 with slow.
Qed.

Lemma free_vars_bterms_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    free_vars_bterms (swap_cs_bterms sw bs)
    = free_vars_bterms bs.
Proof.
  introv.
  unfold free_vars_bterms.
  unfold swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_bterms_swap_cs_bterms : slow.

Lemma map_num_bvars_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    map num_bvars (swap_cs_bterms sw bs)
    = map num_bvars bs.
Proof.
  introv; unfold swap_cs_bterms.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl; tcsp.
Qed.
Hint Rewrite @map_num_bvars_swap_cs_bterms : slow.

Lemma implies_isvalue_can_push_swap_cs_bterms_swap {o} :
  forall n1 n2 can (bs : list (@BTerm o)),
    isvalue (oterm (Can can) bs)
    -> isvalue (oterm (Can can) (push_swap_cs_bterms n1 n2 (swap_cs_bterms (n1, n2) bs))).
Proof.
  introv isv.
  allrw @isvalue_iff; repnd; dands; eauto 3 with slow.
  unfold isprogram in *; repnd.
  unfold closed in *; simpl in *; autorewrite with slow; dands; auto.
  allrw @nt_wf_oterm_iff; repnd.
  autorewrite with slow; dands; auto.
  introv i.
  apply in_map_iff in i; exrepnd; subst.
  apply in_map_iff in i1; exrepnd; subst; simpl in *.
  apply isv in i1.
  destruct a0; simpl in *.
  allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_can_push_swap_cs_bterms_swap : slow.

Lemma computes_to_value_swap_implies_cs2 {o} :
  forall (cond : @LibCond o) (lib : @plibrary o) n1 n2 t can (bs : list BTerm),
    n1 <> n2
    -> sw_not_in_lib (n1, n2) lib
    -> lib_nodup lib
    -> im_swap_lib lib
    -> strong_sat_cond_lib cond lib
    -> lib_cond_no_cs cond
    -> (swap_cs_term (n1,n2) t) =v>(lib) (oterm (Can can) bs)
    -> (mk_swap_cs2 n1 n2 t) =v>(lib) (oterm (Can can) (push_swap_cs_bterms n1 n2 (swap_cs_bterms (n1,n2) bs))).
Proof.
  introv d ni nodup im sat nocs comp.
  unfold computes_to_value in *; repnd; dands; eauto 3 with slow;[].

  apply (@swap_reduces_to o (n1,n2)) in comp0; autorewrite with slow in comp0.
  erewrite swap_cs_plib_trivial_if_no_cs in comp0; eauto.
  eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|]; fold_terms.
  apply reduces_to_if_step; csunf; simpl; auto.
  unfold push_swap_cs_can; simpl; autorewrite with slow; auto.
Qed.

Lemma length_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    length (swap_cs_bterms sw bs) = length bs.
Proof.
  introv; unfold swap_cs_bterms; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_swap_cs_bterms : slow.

Lemma csubst_mk_swap_cs2 {o} :
  forall n1 n2 (t : @NTerm o) s,
    csubst (mk_swap_cs2 n1 n2 t) s = mk_swap_cs2 n1 n2 (csubst t s).
Proof.
  introv.
  unfold csubst.
  change_to_lsubst_aux4; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @csubst_mk_swap_cs2 : slow.

Lemma approx_swap {o} :
  forall (cond : @LibCond o) lib n1 n2 (t : @NTerm o),
    n1 <> n2
    -> sw_not_in_lib (n1, n2) lib
    -> lib_nodup lib
    -> im_swap_lib lib
    -> strong_sat_cond_lib cond lib
    -> lib_cond_no_cs cond
    -> isprogram t
    -> approx
         lib
         (swap_cs_term (n1,n2) t)
         (mk_swap_cs2 n1 n2 t).
Proof.
  cofix ind; introv d ni nodup im sat nocs isp.
  constructor.
  unfold close_comput; dands; eauto 2 with slow;[|].

  { introv comp.
    apply (computes_to_value_swap_implies_cs2 cond) in comp; auto.
    eexists; dands; eauto.
    unfold lblift; autorewrite with slow; dands; auto.
    introv len; autorewrite with slow.
    unfold push_swap_cs_bterms.
    rewrite selectbt_map; autorewrite with slow; auto.
    unfold swap_cs_bterms.
    rewrite selectbt_map; autorewrite with slow; auto.

    remember (selectbt tl_subterms n) as b; destruct b; simpl.
    unfold blift.

    exists l n0 (mk_swap_cs2 n1 n2 (swap_cs_term (n1,n2) n0)).
    dands; eauto 3 with slow.

    apply olift_iff_oliftp; eauto 3 with slow.
    { apply respects_alpha_sum; eauto 3 with slow.
      apply respects_alpha_approx. }

    unfold oliftp; dands; eauto 3 with slow.

    { admit. }
    { admit. }

    introv cova covb; left.
    autorewrite with slow.

    pose proof (ind cond lib n1 n2 (csubst n0 sub)) as ind.
    repeat (autodimp ind hyp).

    { admit. }

    apply (swap_approx (n1,n2)) in ind; autorewrite with slow in ind.
    erewrite swap_cs_plib_trivial_if_no_cs in ind; eauto.
    simpl in ind; boolvar; tcsp; GC; fold_terms.

SearchAbout approx swap_cs_term.
SearchAbout lsubst swap_cs_term.
SearchAbout csubst mk_apply.
SearchAbout respects_alpha.
SearchAbout olift.

Qed.
