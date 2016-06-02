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


Require Export csubst6.
Require Export natk2.


Lemma mkcv_natk_substc {o} :
  forall v a (t : @CTerm o),
    alphaeqc
      (substc t v (mkcv_natk [v] a))
      (mkc_natk (substc t v a)).
Proof.
  introv.
  rw @mkc_natk_eq.
  rw @mkcv_natk_eq.

  destruct_cterms.
  unfold alphaeqc; simpl.

  (* brute force *)

  remember (newvar x0) as nv1.
  pose proof (newvar_prop x0) as nvp1; rw <- Heqnv1 in nvp1.
  clear Heqnv1.
  rw @cl_subst_subst_aux; eauto 2 with slow.
  unfold subst_aux; simpl; allrw @sub_filter_nil_r; allrw memvar_singleton.
  pose proof (newvar_prog (@mk_void o)) as nvv; autodimp nvv hyp; tcsp;eauto 2 with slow;[].
  rw nvv.

  remember (newvar (mk_less_than (mk_var nv1) x0)) as nv2.
  pose proof (newvar_prop (mk_less_than (mk_var nv1) x0)) as nvp2; rw <- Heqnv2 in nvp2.
  clear Heqnv2.
  allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  boolvar; allsimpl; tcsp.

  { constructor; simpl; auto; [].
    unfold selectbt; simpl.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms.
    allrw @lsubst_aux_nil.
    eapply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto.
    rw @subst_trivial; auto.

    pose proof (ex_fresh_var (nv1 :: nv2
                                  :: nvarx
                                  :: newvar (mk_less_than (mk_var nvarx) x0)
                                  :: bound_vars x0
                                  ++ free_vars x0)) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r;[].
      apply disjoint_singleton_l.
      rw nvv.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.
      repeat (boolvar; tcsp; allsimpl;
              allrw @lsubst_aux_nil;
              allrw remove_nvars_cons;
              allrw remove_nvars_nil_l;
              allrw app_nil_r).
      repeat (allrw in_app_iff; allsimpl; allrw in_remove).
      allrw not_over_or; dands; tcsp. }

    rw nvv.
    remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
    pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
    rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.

    allrw memvar_singleton.
    allrw @sub_filter_nil_r.
    boolvar; allsimpl; tcsp; fold_terms;[|].

    { rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow.
      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }

    { allrw memvar_singleton; simpl; boolvar; tcsp.
      simpl; boolvar; tcsp; fold_terms.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow).
      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }
  }

  { allrw memvar_singleton; simpl.
    repeat (boolvar; tcsp; simpl; allrw memvar_singleton; allrw @lsubst_aux_nil; fold_terms;GC).

    { apply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto;[].
      rw @subst_trivial; auto.

      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k;[].
      unfold selectbt; simpl.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: newvar (mk_less_than (mk_var nvarx) x0)
                                    :: bound_vars x0
                                    ++ free_vars x0)) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.
      allrw memvar_singleton.
      repeat (boolvar; tcsp; simpl); fold_terms.
      allrw not_over_or; repnd; GC.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow).

      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }

    { constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.
      unfsubst.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx,x)]))
                                    :: (bound_vars (lsubst_aux x0 [(nvarx, x)]))
                                    ++ (free_vars (lsubst_aux x0 [(nvarx, x)])))) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx, x)]))) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx, x)]))) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC).
      fold_terms.
      assert (closed (lsubst_aux x0 [(nvarx,x)])) as c
          by (apply closed_lsubst_aux; simpl; eauto 3 with slow).
      repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(nvarx,x)])); auto).

      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
      rw c; simpl; tcsp.
    }

    { constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.
      apply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto;[].
      rw @subst_trivial; auto.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: newvar (mk_less_than (mk_var nvarx) x0)
                                    :: bound_vars x0
                                    ++ free_vars x0)) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC);
        fold_terms;
        repeat (rw (lsubst_aux_trivial_cl_term2 x0); eauto 3 with slow).

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }
    }

    { rw @cl_subst_subst_aux; eauto 3 with slow; unfold subst_aux.
      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: v
                                    :: newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))
                                    :: bound_vars (lsubst_aux x0 [(v,x)])
                                    ++ free_vars (lsubst_aux x0 [(v,x)]))) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v0]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC);
        fold_terms;
        assert (closed (lsubst_aux x0 [(v,x)])) as c
            by (apply closed_lsubst_aux; simpl; eauto 3 with slow);
        repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(v,x)])); auto).

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }
    }
  }
Qed.

Hint Rewrite remove_nvars_nil_l : slow.
Hint Rewrite @sub_filter_nil_r : slow.

Lemma alpha_eq_csubst_mk_natk {o} :
  forall (t : @NTerm o) s,
    alpha_eq (csubst (mk_natk t) s) (mk_natk (csubst t s)).
Proof.
  introv.
  unfold csubst.
  repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
  unfold mk_natk, mk_natk_aux.
  simpl; autorewrite with slow.

  fold_terms.
  repeat prove_alpha_eq4.

  {
    rewrite <- sub_filter_app_r; simpl.

    remember (newvar t) as nv1.
    pose proof (newvar_prop t) as p1.
    rewrite <- Heqnv1 in p1.

    remember (newvar (mk_less_than (vterm nv1) t)) as nv2.
    pose proof (newvar_prop (mk_less_than (vterm nv1) t)) as p2.
    rewrite <- Heqnv2 in p2.

    remember (newvar (lsubst_aux t (csub2sub s))) as nv3.
    pose proof (newvar_prop (lsubst_aux t (csub2sub s))) as p3.
    rewrite <- Heqnv3 in p3.

    remember (newvar (@mk_void o)) as nv4.
    pose proof (newvar_prop (@mk_void o)) as p4.
    rewrite <- Heqnv4 in p4.

    assert (nv1 <> nv2) as d1.
    {
      allsimpl; autorewrite with slow in *.
      allrw not_over_or; repnd; auto.
    }

    assert (nv4 = nvarx) as e1 by auto.

    pose proof (ex_fresh_var ((newvar (mk_less_than (mk_var nv3) (lsubst_aux t (csub2sub s))))
                                ::nv1
       :: (remove_nvars [nv2]
             (nv1
              :: free_vars
                   (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2]))) ++
           nvarx
           :: nv4
              :: nvarx
                 :: nv2
                    :: bound_vars
                         (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2])) ++
                       [nvarx]) ++
          all_vars
            (mk_prod (mk_le mk_zero (vterm nv3))
               (mk_less_than (vterm nv3) (lsubst_aux t (csub2sub s)))))) as fv1; exrepnd.

    apply (al_bterm_aux [v]); simpl; autorewrite with slow; auto.

    {
      apply disjoint_singleton_l; auto.
      simpl in *.
      allrw not_over_or; repnd; dands; auto.
    }

    fold_terms.
    autorewrite with slow.
    repeat (rewrite (not_eq_beq_var_false nv1 nv2); auto;[]).

    remember (newvar (mk_less_than (mk_var nv3) (lsubst_aux t (csub2sub s)))) as nv5.
    pose proof (newvar_prop (mk_less_than (mk_var nv3) (lsubst_aux t (csub2sub s)))) as p5.
    rewrite <- Heqnv5 in p5.

    assert (nv3 <> nv5) as d2.
    {
      simpl in p5; autorewrite with slow in *.
      rw not_over_or in p5; sp.
    }

    assert (nv5 <> v) as d3.
    {
      simpl in fv0; autorewrite with slow in *.
      rw not_over_or in fv0; sp.
    }

    repeat (rewrite (not_eq_beq_var_false nv3 nv5); auto;[]).
    simpl.
    autorewrite with slow.

    unfold mk_product, mk_not, mk_fun, mk_function, mk_less, nobnd.
    repeat prove_alpha_eq4.

    {
      apply alpha_eq_bterm_congr.
      boolvar; simpl; autorewrite with slow; boolvar; tcsp; eauto 2 with slow.
    }

    {
      pose proof (ex_fresh_var (v
      :: (free_vars
            (lsubst_aux (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2]))
               [(nv1, vterm v)]) ++
          bound_vars
            (lsubst_aux (lsubst_aux t (sub_filter (csub2sub s) [nv1, nv2]))
               [(nv1, vterm v)]) ++ [nvarx]) ++
         all_vars
           (mk_less_than (vterm v)
                         (lsubst_aux (lsubst_aux t (csub2sub s)) [(nv3, vterm v)]))))
        as fv2; exrepnd.
      apply (al_bterm_aux [v0]); simpl; autorewrite with slow; auto.

      {
        apply disjoint_singleton_l; auto.
      }

      simpl.

      assert (nv2 <> v) as d4.
      {
        allsimpl; autorewrite with slow in *.
        rw in_app_iff in fv0; allsimpl.
        allrw not_over_or; repnd; auto.
        autorewrite with slow in *.
        rw in_app_iff in fv5; allsimpl.
        allrw not_over_or; repnd; auto.
      }

      repeat (rewrite (not_eq_beq_var_false nv2 v); auto;[]).
      simpl.
      autorewrite with slow.

      repeat (rewrite (not_eq_beq_var_false nv5 v); auto;[]).
      simpl.
      autorewrite with slow.

      assert (!LIn nv2 (free_vars t)) as ni1.
      {
        intro h.
        simpl in p2; autorewrite with slow in p2.
        rw not_over_or in p2; sp.
      }

      assert (!LIn nv1 (free_vars (lsubst_aux t (csub2sub s)))) as ni2.
      {
        introv h.
        apply free_vars_lsubst_aux_subset in h.
        rewrite sub_free_vars_if_cl_sub in h; eauto 2 with slow.
        autorewrite with slow in h.
        apply in_remove_nvars in h; sp.
      }

      assert (!LIn nv2 (free_vars (lsubst_aux t (csub2sub s)))) as ni3.
      {
        introv h.
        apply free_vars_lsubst_aux_subset in h.
        rewrite sub_free_vars_if_cl_sub in h; eauto 2 with slow.
        autorewrite with slow in h.
        apply in_remove_nvars in h; sp.
      }

      assert (!LIn nv5 (free_vars (lsubst_aux t (csub2sub s)))) as ni4.
      {
        introv h.
        simpl in p5; autorewrite with slow in p5.
        apply not_over_or in p5; sp.
      }

      repeat prove_alpha_eq4.

      {
        rewrite lsubst_aux_sub_filter;
        [|apply disjoint_cons_r; dands; auto;
          apply disjoint_singleton_r; auto];[].

        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v)]);
          [|simpl;apply disjoint_singleton_r; auto];[].

        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].

        rewrite (lsubst_aux_trivial_cl_term _ [(nv3,vterm v)]);
          [|simpl;apply disjoint_singleton_r; auto];[].

        rewrite (lsubst_aux_trivial_cl_term _ [(nv5,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].

        eauto 3 with slow.
      }

      {
        apply alpha_eq_bterm_congr.
        remember (beq_var nv2 nvarx) as b1; symmetry in Heqb1.
        remember (beq_var nv5 nvarx) as b2; symmetry in Heqb2.

        destruct b1, b2; simpl; try (rewrite Heqb1); try (rewrite Heqb2); eauto 3 with slow.
      }
    }
  }
Qed.

Lemma substc_mkcv_natk2nat {o} :
  forall v (t : @CVTerm o [v]) a,
    alphaeqc
      (substc a v (mkcv_natk2nat [v] t))
      (natk2nat (substc a v t)).
Proof.
  introv; unfold mkcv_natk2nat.
  eapply alphaeqc_trans;[apply substc_mkcv_fun|].
  unfold natk2nat.
  autorewrite with slow.
  apply alphaeqc_mkc_fun; eauto 3 with slow.
  eapply alphaeqc_trans;[apply mkcv_natk_substc|].
  eauto 3 with slow.
Qed.

Definition natU {o} : @CTerm o := mkc_bunion mkc_tnat mkc_unit.

Definition mk_natU {o} : @NTerm o := mk_bunion mk_tnat mk_unit.
Definition mk_nat2nat {o} : @NTerm o := mk_fun mk_tnat mk_tnat.
Definition mk_natk2nat {o} (t : @NTerm o) : @NTerm o := mk_fun (mk_natk t) mk_tnat.

Lemma wf_tnat {p} : @wf_term p mk_tnat.
Proof.
  sp.
Qed.
Hint Resolve wf_tnat : slow.

Lemma wf_term_mk_natk2nat {o} :
  forall (t : @NTerm o),
    wf_term (mk_natk2nat t) <=> wf_term t.
Proof.
  introv.
  unfold mk_natk2nat.
  rw @wf_fun_iff.
  rw @wf_term_mk_natk.
  split; tcsp.
Qed.

Lemma wf_term_mk_natk2nat_implies {o} :
  forall (t : @NTerm o),
    wf_term (mk_natk2nat t) -> wf_term t.
Proof.
  introv w.
  rw @wf_term_mk_natk2nat in w; auto.
Qed.

Lemma cover_vars_mk_natk2nat {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_natk2nat t) s <=> cover_vars t s.
Proof.
  introv.
  unfold mk_natk2nat.
  rw @cover_vars_fun.
  rw @cover_vars_mk_natk.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_mk_natk2nat_implies {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_natk2nat t) s -> cover_vars t s.
Proof.
  introv cv.
  rw @cover_vars_mk_natk2nat in cv; auto.
Qed.

Lemma wf_term_mk_natU {o} :
  @wf_term o mk_natU.
Proof.
  introv.
  unfold mk_natU.
  apply wf_bunion; dands; tcsp.
Qed.
Hint Resolve wf_term_mk_natU.

Lemma lsubstc_vars_mk_natk2nat_as_mkcv {o} :
  forall (t : @NTerm o) w s vs c,
    {w1 : wf_term t
     & {c1 : cover_vars_upto t s vs
     & alphaeqcv
         vs
         (lsubstc_vars (mk_natk2nat t) w s vs c)
         (mkcv_natk2nat
            vs
            (lsubstc_vars t w1 s vs c1)) }}.
Proof.
  introv.
  unfold mk_natk2nat in *.
  pose proof (lsubstc_vars_mk_fun_as_mkcv
                (mk_natk t) mk_tnat
                w s vs c) as h.
  exrepnd.

  dup w1 as w'.
  rw @wf_term_mk_natk in w'.
  exists w'.

  dup c1 as c'.
  rw @cover_vars_upto_natk in c'.
  exists c'.

  eapply alphaeqcv_trans;[exact h1|].
  unfold mkcv_natk2nat.
  autorewrite with slow.

  unfold alphaeqcv; simpl.
  apply alpha_eq_mk_fun; eauto 2 with slow.
  apply alpha_eq_csubst_mk_natk.
Qed.

Lemma lsubstc_mk_natk2nat {o} :
  forall (t : @NTerm o) w s c,
    {w1 : wf_term t
     & {c1 : cover_vars t s
     & alphaeqc
         (lsubstc (mk_natk2nat t) w s c)
         (natk2nat (lsubstc t w1 s c1)) }}.
Proof.
  introv.
  unfold mk_natk2nat in *.
  pose proof (lsubstc_mk_fun_ex
                (mk_natk t) mk_tnat
                s w c) as h.
  exrepnd.

  dup wA as w'.
  rw @wf_term_mk_natk in w'.
  exists w'.

  dup cA as c'.
  rw @cover_vars_mk_natk in c'.
  exists c'.

  eapply alphaeqc_trans;[exact h1|].
  unfold natk2nat.
  autorewrite with slow.

  unfold alphaeqc; simpl.
  apply alpha_eq_mk_fun; eauto 2 with slow.
  apply alpha_eq_csubst_mk_natk.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
