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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export natk.
Require Export per_props_nat.


Definition natU {o} : @CTerm o := mkc_bunion mkc_tnat mkc_unit.

Definition mk_natU {o} : @NTerm o := mk_bunion mk_tnat mk_unit.
Definition mk_nat2nat {o} : @NTerm o := mk_fun mk_tnat mk_tnat.
Definition mk_natk2nat {o} (t : @NTerm o) : @NTerm o := mk_fun (mk_natk t) mk_tnat.

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

Lemma lsubstc_mk_natk2nat_sp1 {o} :
  forall v (t : @CTerm o) w s c,
    alphaeqc
      (lsubstc (mk_natk2nat (mk_var v)) w ((v,t) :: s) c)
      (natk2nat t).
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  simpl.
  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  allrw @sub_find_sub_filter_trivial2.
  allrw memvar_singleton.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw memvar_singleton.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw @sub_find_sub_filter_trivial.
  allrw @sub_find_sub_filter_trivial2.
  allrw <- beq_var_refl.
  fold_terms.

  destruct_cterms; allsimpl.
  unfold mk_fun, mk_function, nobnd.
  prove_alpha_eq4.

  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[].
  apply alphaeqbt_nilv2.

  unfold mk_natk, mk_natk_aux, mk_set, nobnd.
  prove_alpha_eq4;[].
  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[].

  pose proof (ex_fresh_var (newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v))
                                   :: (newvar (mk_less_than (mk_var (newvar x)) x))
                                   :: (all_vars
         (@mk_product o
            (mk_function (mk_less_than (mk_var (newvar (@mk_var o v))) mk_zero)
               (newvar (@mk_void o)) mk_void)
            (newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)))
            (mk_less_than (mk_var (newvar (@mk_var o v))) x)) ++
       all_vars
         (mk_prod (mk_le mk_zero (mk_var (newvar x)))
            (mk_less_than (mk_var (newvar x)) x))))) as fv.
  exrepnd.
  rw @in_cons_iff in fv0.
  rw @in_cons_iff in fv0.
  rw not_over_or in fv0.
  rw not_over_or in fv0.
  repnd.

  apply (al_bterm_aux [v0]); auto.

  { apply disjoint_singleton_l; fold_terms; auto. }

  simpl.
  allrw @sub_filter_nil_r.
  allrw memvar_singleton.
  fold_terms.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw <- beq_var_refl.
  repeat (rw (beq_var_newvar_trivial1 (newvar (@mk_var o v))
                                      (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)));
          simpl; tcsp;[]).
  repeat (rw (beq_var_newvar_trivial1 (newvar x)
                                      (mk_less_than (mk_var (newvar x)) x));
          simpl; tcsp;[]).
  allrw <- beq_var_refl.
  allrw memvar_singleton; simpl.

  repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 2 with slow;[]).

  unfold mk_product, nobnd.
  prove_alpha_eq4.
  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[|].

  { apply alphaeqbt_nilv2.

    unfold mk_function, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[|].

    { apply alphaeqbt_nilv2.
      unfold mk_less, nobnd.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      repeat (boolvar; simpl); tcsp.
    }

    { apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      repeat (boolvar; simpl); tcsp.
    }
  }

  { pose proof (ex_fresh_var ((newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)))
                                :: (newvar (mk_less_than (mk_var (newvar x)) x))
                                :: (all_vars
         (mk_less (mk_var v0) x
            mk_true
            (mk_approx mk_axiom
               (mk_fix
                  (mk_lam nvarx
                     match
                       sub_find
                         (if beq_var (newvar (@mk_var o v)) nvarx
                          then []
                          else [(newvar (@mk_var o v), mk_var v0)]) nvarx
                     with
                     | Some t => t
                     | None => mk_var nvarx
                     end)))) ++
       all_vars
         (mk_less (mk_var v0) x mk_true
            (mk_approx mk_axiom
               (mk_fix
                  (mk_lam nvarx
                     match
                       sub_find
                         (if beq_var (newvar x) nvarx
                          then []
                          else [(newvar x, mk_var v0)]) nvarx
                     with
                     | Some t => t
                     | None => mk_var nvarx
                     end))))))) as fv.
    exrepnd.
    rw @in_cons_iff in fv3.
    rw @in_cons_iff in fv3.
    rw not_over_or in fv3.
    rw not_over_or in fv3.
    repnd.

    apply (al_bterm_aux [v1]); auto.

    { apply disjoint_singleton_l; fold_terms; auto. }

    simpl.
    fold_terms.
    repeat (rw not_eq_beq_var_false;tcsp;[]).
    repeat (rw (not_eq_beq_var_false (newvar (mk_less_than (mk_var (newvar x)) x))); tcsp;[]).

    repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 2 with slow;[]).

    unfold mk_less, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    repeat (boolvar; subst; simpl; tcsp);
      try (complete (rw not_over_or in Heqb; tcsp));
      try (complete (rw not_over_or in Heqb0; tcsp)).
  }
Qed.


Lemma tequality_natk2nat {o} :
  forall lib (a b : @CTerm o),
    tequality lib (natk2nat a) (natk2nat b)
     <=> {k1 : Z
          , {k2 : Z
          , (a) ===>(lib) (mkc_integer k1)
          # (b) ===>(lib) (mkc_integer k2)
          # (forall k : Z,
               (0 <= k)%Z ->
               ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z)}}.
Proof.
  introv.
  unfold natk2nat.
  rw @tequality_mkc_fun.
  rw @tequality_mkc_natk.
  split; intro k; exrepnd; dands; eauto 3 with slow.

  - spcast; exists k1 k0; dands; spcast; auto.

  - spcast; exists k1 k2; dands; spcast; auto.

  - introv inh; apply type_tnat.
Qed.

Lemma lsubstc_mk_unit {o} :
  forall w (s : @CSub o) c,
    lsubstc mk_unit w s c = mkc_unit.
Proof.
  introv.
  unfold mk_unit, mkc_unit.
  rw @lsubstc_mk_true; apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_natU {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_natU w s c) natU.
Proof.
  introv.
  unfold mk_natU, natU.
  pose proof (lsubstc_mk_bunion_ex mk_tnat mk_unit s w c) as h.
  exrepnd.
  eapply alphaeqc_trans;[exact h1|]; clear h1.
  rw @lsubstc_mkc_tnat.
  rw @lsubstc_mk_unit.
  apply alphaeqc_refl.
Qed.

Lemma type_natU {o} :
  forall (lib : @library o),
    type lib natU.
Proof.
  introv.
  apply tequality_bunion; dands; eauto 3 with slow.
  - apply type_tnat.
  - apply tequality_unit.
Qed.

(* !!MOVE *)
Hint Resolve alphaeqc_trans : slow.
Hint Resolve alphaeqc_sym : slow.

Lemma respects_alphaeqc_alphaeqc {o} : respects2 alphaeqc (@alphaeqc o).
Proof.
  unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
Qed.
Hint Resolve respects_alphaeqc_alphaeqc : respects.

Lemma lsubstc_mk_nat2nat {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_nat2nat w s c) nat2nat.
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 2 with slow.

  simpl.

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  fold_terms.
  auto.
Qed.

Lemma type_nat2nat {o} :
  forall (lib : @library o), type lib nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply type_mkc_fun; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2nat : slow.

Lemma member_respects_alphaeqc_l {o} :
  forall lib (t1 t2 T : @CTerm o),
    alphaeqc t1 t2 -> member lib t1 T -> member lib t2 T.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply equality_respects_alphaeqc_left;[exact aeq|].
  eapply equality_respects_alphaeqc_right;[exact aeq|].
  auto.
Qed.

Lemma member_respects_alphaeqc_r {o} :
  forall lib (t T1 T2 : @CTerm o),
    alphaeqc T1 T2 -> member lib t T1 -> member lib t T2.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply alphaeqc_preserving_equality; eauto.
Qed.

Lemma respects_alphaeqc_member {o} :
  forall (lib : @library o), respects2 alphaeqc (member lib).
Proof.
  introv; unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
  - eapply member_respects_alphaeqc_l; eauto.
  - eapply member_respects_alphaeqc_r; eauto.
Qed.
Hint Resolve respects_alphaeqc_member : respects.

Lemma respects_alphaeqc_equorsq3 {o} :
  forall lib (t1 t2 T1 T2 : @CTerm o),
    alphaeqc T1 T2
    -> equorsq lib t1 t2 T1
    -> equorsq lib t1 t2 T2.
Proof.
  introv aeq e.
  eauto 3 with slow.
  pose proof (respects_alphaeqc_equorsq lib) as h.
  destruct h as [h1 h]; repnd.
  eapply h; eauto.
Qed.

Lemma equality_natk_to_tnat {o} :
  forall lib (n1 n2 k : @CTerm o),
    equality lib n1 n2 (mkc_natk k)
    -> equality lib n1 n2 mkc_tnat.
Proof.
  introv e.

  apply equality_in_natk in e; exrepnd; spcast.
  apply equality_in_tnat.
  exists m; dands; spcast; auto.
Qed.

Lemma equality_nat2nat_to_natk2nat {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_tnat
    -> equality lib f g nat2nat
    -> equality lib f g (natk2nat n).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { apply type_mkc_natk.
    exists (Z.of_nat k); spcast; auto. }

  introv en.
  apply equality_natk_to_tnat in en; apply e in en; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
