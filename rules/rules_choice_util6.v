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

(*Lemma compute_step_swap_implies_cs2 {o} :
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
Qed.*)

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

(*Lemma implies_isvalue_can_push_swap_cs_bterms_swap {o} :
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
  allrw @bt_wf_iff; eauto 4 with slow.
Qed.
Hint Resolve implies_isvalue_can_push_swap_cs_bterms_swap : slow.*)

(*Lemma computes_to_value_swap_implies_cs2 {o} :
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
Qed.*)

Lemma length_swap_cs_bterms {o} :
  forall sw (bs : list (@BTerm o)),
    length (swap_cs_bterms sw bs) = length bs.
Proof.
  introv; unfold swap_cs_bterms; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_swap_cs_bterms : slow.

Lemma csubst_mk_swap_cs2 {o} :
  forall sw (t : @NTerm o) s,
    csubst (mk_swap_cs2 sw t) s = mk_swap_cs2 sw (csubst t s).
Proof.
  introv.
  unfold csubst.
  change_to_lsubst_aux4; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @csubst_mk_swap_cs2 : slow.

Definition mkc_swap_per {o} (sw : cs_swap) (p : per(o)) : per(o) :=
  fun a b => p (mkc_swap_cs sw a) (mkc_swap_cs sw b).

Definition mkc_swap_lib_per {o} {lib}
           (sw : cs_swap)
           (p  : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => mkc_swap_per sw (p _ x)).
  introv; unfold mkc_swap_per; introv; apply lib_per_cond.
Defined.

Definition mkc_swap_lib_per_fam {o} {lib}
           (sw  : cs_swap)
           {eqa : lib-per(lib,o)}
           (p   : lib-per-fam(lib,eqa,o)) : lib-per-fam(lib,mkc_swap_lib_per sw eqa,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) a b (e : mkc_swap_lib_per sw eqa lib' x a b) =>
            mkc_swap_per sw (p _ x (mkc_swap_cs sw a) (mkc_swap_cs sw b) e)).
  introv; unfold mkc_swap_per; introv; apply lib_per_fam_cond.
Defined.

Lemma lib_extends_preserves_strong_sat_lib_cond {o} :
  forall (lib1 lib2 : @library o),
    lib_nodup lib2
    -> lib_extends lib1 lib2
    -> strong_sat_lib_cond lib2
    -> strong_sat_lib_cond lib1.
Proof.
  introv nodup ext sat.
  apply sat_lib_cond_implies_strong; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_strong_sat_lib_cond : slow.

Lemma mkc_swap_per_bar_eq {o} :
  forall sw (lib : library) (nodup : lib_nodup lib) (sat : strong_sat_lib_cond lib) (eq : per(o)) (eqa : lib-per(lib,o)),
    (eq <=2=> (per_bar_eq lib eqa))
    -> (mkc_swap_per sw eq) <=2=> (per_bar_eq lib (mkc_swap_lib_per sw eqa)).
Proof.
  introv nodup sat eqiff.
  introv; unfold mkc_swap_per; simpl.
  rw eqiff; tcsp.
Qed.

Lemma push_swap_cs_otermc_base {o} :
  forall sw, @push_swap_cs_otermc o sw mkc_base = mkc_base.
Proof.
  introv; apply cterm_eq; simpl; tcsp.
Qed.
Hint Rewrite @push_swap_cs_otermc_base : slow.

Definition push_swap_cs_sub_cvterm {o} vs (sw : cs_swap) (t : @CVTerm o vs) :=
  let (a,p) := t in
  exist (isprog_vars vs) (push_swap_cs_sub_term sw vs a) (implies_isprog_vars_push_swap_cs_sub_term vs sw vs a p).

Lemma push_swap_cs_sub_term_nil {o} :
  forall sw (t : @NTerm o),
    push_swap_cs_sub_term sw [] t = t.
Proof.
  introv; unfold push_swap_cs_sub_term; autorewrite with slow; auto.
Qed.
Hint Rewrite @push_swap_cs_sub_term_nil : slow.

Lemma push_swap_cs_otermc_function {o} :
  forall sw (a : @CTerm o) v b,
    push_swap_cs_otermc sw (mkc_function a v b)
    = mkc_function (mkc_swap_cs sw a) v (mkcv_swap_cs _ sw (push_swap_cs_sub_cvterm _ sw b)).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    try (unfold push_swap_cs_can; simpl; autorewrite with slow; auto).
Qed.
Hint Rewrite @push_swap_cs_otermc_function : slow.

Lemma push_swap_cs_otermc_union {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_union a b)
    = mkc_union (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    try (unfold push_swap_cs_can; simpl; autorewrite with slow; auto).
Qed.
Hint Rewrite @push_swap_cs_otermc_union : slow.

Lemma push_swap_cs_otermc_approx {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_approx a b)
    = mkc_approx (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    try (unfold push_swap_cs_can; simpl; autorewrite with slow; auto).
Qed.
Hint Rewrite @push_swap_cs_otermc_approx : slow.

Lemma push_swap_cs_otermc_cequiv {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_cequiv a b)
    = mkc_cequiv (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    try (unfold push_swap_cs_can; simpl; autorewrite with slow; auto).
Qed.
Hint Rewrite @push_swap_cs_otermc_cequiv : slow.

Lemma push_swap_cs_otermc_axiom {o} :
  forall sw,
    @push_swap_cs_otermc o sw mkc_axiom
    = mkc_axiom.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_axiom : slow.

Lemma computes_to_value_implies_computes_to_val_like_in_max_k_steps {o} :
  forall lib (a b : @NTerm o),
    a =v>(lib) b
    -> {k : nat & computes_to_val_like_in_max_k_steps lib a b k # isvalue b}.
Proof.
  introv comp.
  unfold computes_to_value in *; repnd.
  unfold reduces_to in *; exrepnd.
  exists k; dands; auto; split; eauto 3 with slow.
Qed.

Lemma push_swap_cs_can_eq_integer_implies {o} :
  forall sw (can : @CanonicalOp o) bs k,
    push_swap_cs_can sw can bs = mk_integer k
    -> can = Nint k # bs = [].
Proof.
  introv h.
  destruct can; simpl in *; ginv.
  destruct bs; simpl in *; ginv; tcsp.
  inversion h; auto.
Qed.

Lemma implies_approx_swap_cs2 {o} :
  forall sw lib (a b : @NTerm o),
    approx lib a b
    -> approx lib (mk_swap_cs2 sw a) (mk_swap_cs2 sw b).
Proof.
  introv apx.
  applydup @approx_relates_only_progs in apx; repnd.
  unfold mk_swap_cs2; repeat (prove_approx);sp.
Qed.

Lemma implies_approxc_swap_cs {o} :
  forall sw lib (a b : @CTerm o),
    approxc lib a b
    -> approxc lib (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv apx; destruct_cterms; unfold approxc in *; simpl in *.
  apply implies_approx_swap_cs2; auto.
Qed.
Hint Resolve implies_approxc_swap_cs : slow.

Lemma implies_cequiv_swap_cs2 {o} :
  forall sw lib (a b : @NTerm o),
    cequiv lib a b
    -> cequiv lib (mk_swap_cs2 sw a) (mk_swap_cs2 sw b).
Proof.
  introv ceq; destruct ceq as [c1 c2]; split; apply implies_approx_swap_cs2; auto.
Qed.

Lemma implies_cequivc_swap_cs2 {o} :
  forall sw lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_swap_cs2 sw a) (mkc_swap_cs2 sw b).
Proof.
  unfold cequivc; introv ceq; destruct_cterms; simpl in *.
  apply implies_cequiv_swap_cs2; auto.
Qed.

Lemma implies_cequivc_swap_cs {o} :
  forall sw lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv ceq; apply implies_cequivc_swap_cs2; auto.
Qed.
Hint Resolve implies_cequivc_swap_cs : slow.

Lemma isprogram_mk_swap_cs2_iff {o} :
  forall sw (t : @NTerm o),
    isprogram (mk_swap_cs2 sw t) <=> isprogram t.
Proof.
  introv; split; intro h; try apply implies_isprogram_mk_swap_cs2; auto.
  destruct h as [cl wf]; split; unfold closed in *; simpl in *; autorewrite with slow in *; auto.
  apply nt_wf_oterm_iff in wf; repnd; simpl in *.
  dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_axiom_implies {o} :
  forall sw lib (t : @CTerm o),
  (mkc_swap_cs sw t) ===>(lib) mkc_axiom
  -> t ===>(lib) mkc_axiom.
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  destruct_cterms; unfold computes_to_valc, cequivc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in ext1; auto; exrepnd; subst.
  eapply cequiv_axiom in ext0; eauto 3 with slow.
  apply computes_to_value_if_iscan in ext0; eauto 3 with slow; subst.
  inversion ext0; autorewrite with slow in *; subst; simpl in *.
  destruct bs; simpl in *; ginv.
  apply (@swap_computes_to_value o sw) in ext3; autorewrite with slow in ext3.
  exists (@mkc_axiom o); dands; spcast; tcsp.
Qed.

Lemma mkc_swap_equality_of_int_bar {o} :
  forall sw lib (eq : per(o)),
    (eq <=2=> (equality_of_int_bar lib))
    -> (mkc_swap_per sw eq) <=2=> (equality_of_int_bar lib).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold equality_of_int in *; exrepnd.

  { exists k.
    apply mkc_swap_ccomputes_to_valc_ext_integer_implies in h1.
    apply mkc_swap_ccomputes_to_valc_ext_integer_implies in h0; tcsp. }

  { exists k.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in h1.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
    autorewrite with slow in *; auto. }
Qed.

Lemma mkc_swap_equality_of_nat_bar {o} :
  forall sw lib (eq : per(o)),
    (eq <=2=> (equality_of_nat_bar lib))
    -> (mkc_swap_per sw eq) <=2=> (equality_of_nat_bar lib).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold equality_of_nat in *; exrepnd.

  { exists n.
    apply mkc_swap_ccomputes_to_valc_ext_integer_implies in h1.
    apply mkc_swap_ccomputes_to_valc_ext_integer_implies in h0; tcsp. }

  { exists n.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in h1.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
    autorewrite with slow in *; auto. }
Qed.

Lemma mkc_swap_computes_to_valc_integer_implies {o} :
  forall sw lib (t : @CTerm o) k,
    computes_to_valc lib (mkc_swap_cs sw t) (mkc_integer k)
    -> computes_to_valc lib t (mkc_integer k).
Proof.
  introv comp; exrepnd; spcast.
  destruct_cterms; unfold computes_to_valc, cequivc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in comp; auto; exrepnd; subst.
  inversion comp1 as [xx]; autorewrite with slow in *; subst; clear comp1.
  destruct bs; simpl in *; ginv.
  apply (@swap_computes_to_value o sw) in comp0; autorewrite with slow in comp0; auto.
Qed.

Lemma mkc_swap_computes_to_valc_nat_implies {o} :
  forall sw lib (t : @CTerm o) k,
    computes_to_valc lib (mkc_swap_cs sw t) (mkc_nat k)
    -> computes_to_valc lib t (mkc_nat k).
Proof.
  introv comp.
  apply mkc_swap_computes_to_valc_integer_implies in comp; auto.
Qed.

Lemma are_same_qnat_mkc_swap_implies {o} :
  forall sw lib c (t1 t2 : @CTerm o),
    are_same_qnats lib c (mkc_swap_cs sw t1) (mkc_swap_cs sw t2)
    <-> are_same_qnats lib c t1 t2.
Proof.
  introv; split; introv same ext.
  { apply same in ext; exrepnd; spcast.
    exists n.
    apply mkc_swap_computes_to_valc_nat_implies in ext1.
    apply mkc_swap_computes_to_valc_nat_implies in ext0.
    dands; spcast; auto. }
  { apply same in ext; exrepnd; spcast.
    exists n.
    apply (mkc_swap_preserves_computes_to_valc sw) in ext1.
    apply (mkc_swap_preserves_computes_to_valc sw) in ext0.
    autorewrite with slow in *.
    dands; spcast; auto. }
Qed.

Lemma sat_qnat_cond_mkc_swap_implies {o} :
  forall sw lib c (t : @CTerm o),
    sat_qnat_cond lib c (mkc_swap_cs sw t)
    <-> sat_qnat_cond lib c t.
Proof.
  introv; split; introv same h exta extb compa compb; subst.
  { apply (mkc_swap_preserves_computes_to_valc sw) in compa.
    apply (mkc_swap_preserves_computes_to_valc sw) in compb.
    autorewrite with slow in *.
    eapply same; eauto. }
  { apply mkc_swap_computes_to_valc_nat_implies in compa.
    apply mkc_swap_computes_to_valc_nat_implies in compb.
    eapply same; eauto. }
Qed.

Lemma mkc_swap_equality_of_qnat_bar {o} :
  forall sw lib (eq : per(o)) c,
    (eq <=2=> (equality_of_qnat_bar lib c))
    -> (mkc_swap_per sw eq) <=2=> (equality_of_qnat_bar lib c).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold equality_of_qnat in *; exrepnd;
        dands; auto;
          allrw @are_same_qnat_mkc_swap_implies;
          allrw @sat_qnat_cond_mkc_swap_implies;
          auto.
Qed.

Lemma swap_cs_can_inj {o} :
  forall sw (c1 c2 : @CanonicalOp o),
    swap_cs_can sw c1 = swap_cs_can sw c2 -> c1 = c2.
Proof.
  introv h.
  destruct c1, c2; simpl in *; auto; ginv.
  inversion h as [xx].
  apply swap_cs_inj in xx; subst; auto.
Qed.

Lemma swap_cs2_alpha_eq_implies {o} :
  forall sw (t : @NTerm o) u,
    alpha_eq (mk_swap_cs2 sw t) u
    -> {z : NTerm & u = mk_swap_cs2 sw z # alpha_eq t z}.
Proof.
  introv aeq; apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst.
  unfold alpha_eq_bterms in *; simpl in *; repnd.
  repeat (destruct bs'; simpl in *; tcsp; ginv).
  pose proof (aeq0 (nobnd t) b) as aeq0; autodimp aeq0 hyp.
  apply alpha_eq_bterm_nobnd in aeq0; exrepnd; subst.
  exists u; dands; auto.
Qed.

Lemma lsubst_aux_eq_swap2_implies {o} :
  forall t l k sw (u : @NTerm o),
    disjoint k (all_vars t)
    -> length l = length k
    -> lsubst_aux t (var_ren l k) = mk_swap_cs2 sw u
    -> {z : NTerm & t = mk_swap_cs2 sw z # u = lsubst_aux z (var_ren l k)}.
Proof.
  introv disj len h.
  destruct t as [v|op bs]; simpl in *.
  { rewrite sub_find_var_ren_as_option_map in h.
    remember (renFind (mk_swapping l k) v) as x; destruct x; simpl in *; ginv. }
  inversion h as [xx]; subst; clear h.
  repeat (destruct bs; simpl in *; tcsp; ginv).
  destruct b; simpl in *.
  destruct l0; simpl in *; unfold nobnd in *; ginv; fold_terms.
  exists n; dands; autorewrite with slow; auto.
Qed.

Lemma lsubst_eq_swap2_implies {o} :
  forall t l k sw (u : @NTerm o),
    disjoint k (all_vars t)
    -> length l = length k
    -> lsubst t (var_ren l k) = mk_swap_cs2 sw u
    -> {z : NTerm & t = mk_swap_cs2 sw z # u = lsubst z (var_ren l k)}.
Proof.
  introv disj len h.
  rewrite lsubst_lsubst_aux2 in h; auto;
    [|apply disjoint_sym; apply disjoint_app_r in disj; tcsp].
  apply lsubst_aux_eq_swap2_implies in h; auto; exrepnd; subst.
  eexists; dands; eauto.
  rewrite lsubst_lsubst_aux2; auto.
  apply disjoint_app_r in disj; simpl in *; autorewrite with slow in disj; repnd; eauto 3 with slow.
Qed.

Lemma implies_cover_vars_mk_swap_cs2 {o} :
  forall sw (t : @NTerm o) sub,
    cover_vars t sub
    -> cover_vars (mk_swap_cs2 sw t) sub.
Proof.
  introv cov.
  allrw @cover_vars_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Resolve implies_cover_vars_mk_swap_cs2 : slow.

Lemma push_swap_cs_exc_2nobnd_eq {o} :
  forall sw (a b : @NTerm o),
    push_swap_cs_exc sw [nobnd a, nobnd b]
    = mk_exception (mk_swap_cs2 sw a) (mk_swap_cs2 sw b).
Proof.
  introv; unfold push_swap_cs_exc; simpl; autorewrite with slow; fold_terms; auto.
Qed.

Lemma reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc {o} :
  forall sw lib (t : @NTerm o) x e,
    reduces_to lib t (mk_exception x e)
    -> mk_swap_cs2 sw t =e>(mk_swap_cs2 sw x,lib) (mk_swap_cs2 sw e).
Proof.
  introv comp.
  unfold computes_to_exception.
  eapply reduces_to_trans;
    [eapply implies_reduces_to_mk_swap_cs2;
     apply (@swap_reduces_to o sw) in comp; eauto|].
  autorewrite with slow.
  apply reduces_to_if_step.
  csunf; simpl.
  rewrite push_swap_cs_exc_2nobnd_eq; auto.
Qed.

Lemma swap_cs2_computes_to_exc_implies {o} :
  forall lib sw (t : @NTerm o) x e,
    wf_term t
    -> (mk_swap_cs2 sw t) =e>(x,lib) e
    -> t =e>(x,lib) e.
Proof.
  introv wf comp.
  unfold computes_to_exception, reduces_to in *; exrepnd.

  pose proof (computes_to_val_like_in_max_k_steps_swap_cs2_implies
                lib k sw t (mk_exception x e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
  repndors; exrepnd; subst; simpl in *; ginv.

  { apply computes_to_val_like_in_max_k_steps_if_isvalue_like in q0; eauto 3 with slow; ginv. }

  exists k1; auto.
  unfold computes_to_exception_in_max_k_steps in *.
  apply (@swap_reduces_in_atmost_k_steps o sw) in q3.
  autorewrite with slow in *.
  simpl in *; fold_terms.
Abort.

Lemma implies_isprogram_lsust_mk_swap_cs2 {o} :
  forall sw (t : @NTerm o) sub,
    isprogram (lsubst t sub)
    -> isprogram (lsubst (mk_swap_cs2 sw t) sub).
Proof.
  introv isp.
  unfold lsubst in *; simpl in *; autorewrite with slow in *.
  boolvar; apply implies_isprogram_mk_swap_cs2; auto.
Qed.
Hint Resolve implies_isprogram_lsust_mk_swap_cs2 : sow.

Lemma lsubst_push_swap_cs_sub_term_var_ren_as {o} :
  forall sw (t : @NTerm o) (l k : list NVar),
    no_repeats k
    -> length l = length k
    -> disjoint k (all_vars t)
    -> lsubst (push_swap_cs_sub_term sw l t) (var_ren l k)
       = lsubst_aux (lsubst t (var_ren l k)) (sw_sub sw k).
Proof.
  introv norep len disj.
  rewrite lsubst_push_swap_cs_sub_term_var_ren_eq; auto.
  rewrite lsubst_push_swap_cs_sub_term_var_ren_eq2; auto.
Qed.

Lemma renFind_implies_in :
  forall l k v w,
    renFind (mk_swapping l k) v = Some w
    -> LIn v l.
Proof.
  induction l; introv h; simpl in *; ginv.
  destruct k; simpl in *; tcsp; boolvar; subst; tcsp.
  apply IHl in h; tcsp.
Qed.

Lemma change_bvars_alpha_norep_bterm {o} :
  forall (b : @BTerm o) (lv : list NVar),
    {u : BTerm $ disjoint lv (bound_vars_bterm u) # alpha_eq_bterm b u # no_repeats (bound_vars_bterm u)}.
Proof.
  introv.
  pose proof (change_bvars_alpha_norep (oterm (Can NAxiom) [b]) lv) as h; exrepnd.
  apply alpha_eq_oterm_implies_combine2 in h2; exrepnd; subst.
  unfold alpha_eq_bterms in *; simpl in *; repnd.
  repeat (destruct bs'; simpl in *; ginv); autorewrite with slow in *.
  pose proof (h3 b b0) as h3; autodimp h3 hyp; eauto.
Qed.

Lemma implies_alpha_eq_bterm_push_swap_cs_bterm {o} :
  forall sw (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> alpha_eq_bterm (push_swap_cs_bterm sw b1) (push_swap_cs_bterm sw b2).
Proof.
  introv aeq; unfold push_swap_cs_bterm.
  destruct b1 as [l1 t1], b2 as [l2 t2]; simpl in *.
  inversion aeq as [? ? ? ? ? disj1 lena1 lenb1 norep1 aeq1]; subst; clear aeq.
  econstructor; try exact lenb1; autorewrite with slow; auto.
  repeat rewrite lsust_mk_swap_cs2_eq.
  apply implies_alpha_eq_mk_swap_cs2.
  repeat (rewrite lsubst_push_swap_cs_sub_term_var_ren_eq; auto;
          try (complete (allrw disjoint_app_r; tcsp));[]).
  repeat (rewrite <- lsubst_push_swap_cs_sub_term_var_ren_eq2; auto;
          try (complete (allrw disjoint_app_r; tcsp));[]).
  apply implies_alpha_eq_lsubst_aux_sw_sub; auto.
Qed.

Lemma change_bvars_to {o} :
  forall (b : @BTerm o) l lv,
    length l = num_bvars b
    -> disjoint l (free_vars_bterm b)
    -> no_repeats l
    -> {t : NTerm
        & alpha_eq_bterm b (bterm l t)
        # no_repeats (bound_vars t)
        # disjoint l (bound_vars t)
        # disjoint lv (bound_vars t)}.
Proof.
  introv len disj norep.
  pose proof (change_bvars_alpha_norep_bterm b (l ++ lv ++ free_vars_bterm b)) as q; exrepnd.
  allrw disjoint_app_l; repnd.
  destruct u; simpl in *.
  applydup @alphaeqbt_numbvars in q2.
  unfold num_bvars in *; simpl in *.
  rewrite q5 in *.
  allrw no_repeats_app; repnd.
  allrw disjoint_app_r; repnd.
  exists (lsubst_aux n (var_ren l0 l)).
  rewrite boundvars_lsubst_aux_vars; auto;[].
  dands; auto.
  eapply alpha_eq_bterm_trans;[eauto|].
  pose proof (fresh_vars (length l0) (l0 ++ l ++ all_vars n ++ all_vars (lsubst_aux n (var_ren l0 l)))) as w; exrepnd.
  symmetry in w0.
  econstructor; try exact w0; auto.
  { allrw disjoint_app_r; repnd; dands; auto. }
  repeat (rewrite lsubst_lsubst_aux;
          [|rewrite flat_map_free_var_vars_range; allrw disjoint_app_r; repnd; eauto 2 with slow; try omega];[]).
  rewrite lsubst_aux_nest_vars_same; auto;
    allrw disjoint_app_l; allrw disjoint_app_r; repnd; dands; auto; try omega.
  apply alpha_eq_bterm_preserves_free_vars in q2; simpl in *.
  rewrite q2 in *.
  introv i j; applydup disj in i; destruct i0; apply in_remove_nvars; dands; auto.
Qed.

Lemma num_bvars_bterm {o} :
  forall l (t : @NTerm o),
    num_bvars (bterm l t) = length l.
Proof.
  tcsp.
Qed.
Hint Rewrite @num_bvars_bterm : slow.

Lemma num_bvars_push_swap_cs_bterm {o} :
  forall sw (x : @BTerm o),
    num_bvars (push_swap_cs_bterm sw x) = num_bvars x.
Proof.
  introv; unfold num_bvars, push_swap_cs_bterm; destruct x; simpl; auto.
Qed.
Hint Rewrite @num_bvars_push_swap_cs_bterm : slow.

Lemma isprog_oterm_implies_null_free_vars_bterm {o} :
  forall op (bs : list (@BTerm o)) n,
    isprog (oterm op bs)
    -> null (free_vars_bterm (selectbt bs n)).
Proof.
  introv isp.
  apply isprog_ot_iff in isp; repnd.
  destruct (lt_dec n (length bs)) as [d|d].
  { pose proof (isp (selectbt bs n)) as isp; autodimp isp hyp.
    { apply selectbt_in; auto. }
    unfold isprog_bt in isp; repnd.
    allrw @assert_nullb; tcsp. }
  { unfold selectbt in *.
    rewrite nth_overflow; try omega; simpl; autorewrite with slow; auto. }
Qed.
Hint Resolve isprog_oterm_implies_null_free_vars_bterm : slow.

Lemma isprog_oterm_implies_disjoint_free_vars_bterm {o} :
  forall op (bs : list (@BTerm o)) l n,
    isprog (oterm op bs)
    -> disjoint l (free_vars_bterm (selectbt bs n)).
Proof.
  introv isp.
  apply (isprog_oterm_implies_null_free_vars_bterm _ _ n) in isp.
  apply null_iff_nil in isp; rewrite isp; auto.
Qed.
Hint Resolve isprog_oterm_implies_disjoint_free_vars_bterm : slow.

Lemma isvalue_oterm_implies_disjoint_free_vars_bterm {o} :
  forall op (bs : list (@BTerm o)) l n,
    isvalue (oterm op bs)
    -> disjoint l (free_vars_bterm (selectbt bs n)).
Proof.
  introv isv.
  apply (isprog_oterm_implies_disjoint_free_vars_bterm op).
  inversion isv; subst; auto; eauto 3 with slow.
Qed.
Hint Resolve isvalue_oterm_implies_disjoint_free_vars_bterm : slow.

Hint Rewrite @sub_bound_vars_var_ren : slow.

Lemma lsubst_sub_var_ren {o} :
  forall l1 l2 l,
    length l1 = length l
    -> length l2 = length l
    -> no_repeats l
    -> @lsubst_sub o (var_ren l1 l) (var_ren l l2) = var_ren l1 l2.
Proof.
  induction l1; introv lena lenb norep; simpl in *; auto.
  destruct l; simpl in *; cpx.
  destruct l2; simpl in *; cpx.
  allrw no_repeats_cons; repnd.
  repeat rewrite var_ren_cons.
  rewrite lsubst_lsubst_aux; simpl; auto; boolvar.
  f_equal.
  try fold (@var_ren o l1 l).
  rewrite lsubst_sub_cons_r_not_in; autorewrite with slow; auto.
  rewrite computation_mark.sub_free_vars_var_ren; auto.
Qed.

Lemma lsubst_aux_app_left {o} :
  forall (t : @NTerm o) sub1 sub2,
    disjoint (free_vars t) (dom_sub sub2)
    -> lsubst_aux t (sub1 ++ sub2) = lsubst_aux t sub1.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv disj; auto.

  { rewrite sub_find_app.
    remember (sub_find sub1 v) as x; destruct x; simpl; auto.
    allrw disjoint_singleton_l.
    rewrite sub_find_none_if; auto. }

  f_equal.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  rewrite sub_filter_app.
  eapply ind; eauto.
  rewrite <- dom_sub_sub_filter.
  eapply disjoint_flat_map_l in disj; eauto; simpl in *.
  apply disjoint_remove_nvars_l; auto.
Qed.

Lemma disjoint_bound_vars_change_bvars_alpha {o} :
  forall l (t : @NTerm o),
    disjoint (bound_vars (change_bvars_alpha l t)) l.
Proof.
  introv.
  pose proof (change_bvars_alpha_spec t l) as q; simpl in *; repnd; eauto 2 with slow.
Qed.
Hint Resolve disjoint_bound_vars_change_bvars_alpha : slow.

Lemma disjoint_bound_vars_change_bvars_alpha_subset {o} :
  forall l k (t : @NTerm o),
    subset l k
    -> disjoint (bound_vars (change_bvars_alpha k t)) l.
Proof.
  introv ss.
  pose proof (change_bvars_alpha_spec t l) as q; simpl in *; repnd; eauto 2 with slow.
Qed.
Hint Resolve disjoint_bound_vars_change_bvars_alpha_subset : slow.

Lemma alpha_lsubst_app_left {o} :
  forall (t : @NTerm o) sub1 sub2,
    disjoint (dom_sub sub2) (free_vars t)
    -> alpha_eq (lsubst t (sub1 ++ sub2)) (lsubst t sub1).
Proof.
  introv disj.
  unfold lsubst; allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  rewrite sub_free_vars_app.
  boolvar; allrw disjoint_app_r; repnd;
    try (complete (rewrite lsubst_aux_app_left; autorewrite with slow; eauto 2 with slow;
                   apply lsubst_aux_alpha_congr_same_disj; eauto 3 with slow)).
Qed.

Lemma alpha_eq_bterm_ren_1side2 {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq t1 (lsubst t2 (var_ren l2 l1)).
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.
  apply (lsubst_alpha_congr2 _ _ (var_ren lv l1)) in a.
  allrw disjoint_app_r; repnd.

  eapply alpha_eq_trans in a;[|apply alpha_eq_sym;apply combine_sub_nest].
  apply alpha_eq_sym in a.
  eapply alpha_eq_trans in a;[|apply alpha_eq_sym;apply combine_sub_nest].
  apply alpha_eq_sym in a.

  repeat (rewrite lsubst_sub_var_ren in a; auto; try omega;[]).
  eapply alpha_eq_trans in a;[|apply alpha_eq_sym;apply alpha_lsubst_app_left];
    [|rewrite dom_sub_var_ren; auto];[].
  apply alpha_eq_sym in a.
  eapply alpha_eq_trans in a;[|apply alpha_eq_sym;apply alpha_lsubst_app_left];
    [|rewrite dom_sub_var_ren; auto];[].
  apply alpha_eq_sym in a.
  eapply alpha_eq_trans in a;[|apply alpha_eq_sym;apply lsubst_trivial_alpha]; auto.
Qed.

Definition cl_olift {o} R (t1 t2 : @NTerm o) l :=
  nt_wf t1
  # nt_wf t2
  # forall ts,
      length l = length ts
      -> areprograms ts
      -> R (lsubst t1 (combine l ts)) (lsubst t2 (combine l ts)).

Lemma areprograms_implies_prog_sub_combine {o} :
  forall l (ts : list (@NTerm o)),
    areprograms ts
    -> prog_sub (combine l ts).
Proof.
  induction l; introv aps; simpl in *; eauto 3 with slow.
  destruct ts; simpl in *; eauto 3 with slow.
  allrw @areprograms_cons; allrw @prog_sub_cons; repnd; dands; auto.
Qed.
Hint Resolve areprograms_implies_prog_sub_combine : slow.

Lemma are_programs_implies_isprogram_lsubst_combine {o} :
  forall (t : @NTerm o) l ts,
    nt_wf t
    -> areprograms ts
    -> length l = length ts
    -> subset (free_vars t) l
    -> isprogram (lsubst t (combine l ts)).
Proof.
  introv wf aps len ss.
  apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
  rewrite dom_sub_combine_le; allrw; auto.
Qed.
Hint Resolve are_programs_implies_isprogram_lsubst_combine : slow.

Fixpoint sub2terms {o} (sub : @Sub o) d l : list NTerm :=
  match l with
  | [] => []
  | v :: vs =>
    match sub_find sub v with
    | Some t => t :: sub2terms sub d vs
    | None => d :: sub2terms sub d vs
    end
  end.

Lemma length_sub2terms {o} :
  forall (sub : @Sub o) d l,
    length (sub2terms sub d l) = length l.
Proof.
  induction l; simpl; auto.
  destruct (sub_find sub a); simpl; try congruence.
Qed.
Hint Rewrite @length_sub2terms : slow.

Lemma sub_find_some_implies_in_range {o} :
  forall (sub : @Sub o) v t,
    sub_find sub v = Some t
    -> LIn t (range sub).
Proof.
  induction sub; introv h; simpl in *; repnd; boolvar; simpl in *; ginv; tcsp.
  apply IHsub in h; tcsp.
Qed.

Lemma implies_cl_sub_combine_sub2terms {o} :
  forall (sub : @Sub o) d l,
    closed d
    -> cl_sub sub
    -> cl_sub (combine l (sub2terms sub d l)).
Proof.
  induction l; introv cla clb; simpl in *; eauto 2 with slow.
  remember (sub_find sub a) as sf; symmetry in Heqsf; destruct sf; simpl;
    allrw @cl_sub_cons; dands; auto.
  apply sub_find_some in Heqsf.
  rw @cl_sub_eq in clb; apply clb.
  apply in_sub_eta in Heqsf; tcsp.
Qed.
Hint Resolve implies_cl_sub_combine_sub2terms : slow.

Lemma sub_find_combine_sub2terms {o} :
  forall (sub : @Sub o) d l v,
    sub_find (combine l (sub2terms sub d l)) v
    = if in_deq _ deq_nvar v l
      then Some (match sub_find sub v with
                 | Some t => t
                 | None => d
                 end)
      else None.
Proof.
  induction l; introv; simpl; auto; boolvar; repndors; subst; tcsp; GC;
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl in *;
      boolvar; subst; tcsp;
        try (apply not_over_or in n; repnd; tcsp);
        try (apply not_over_or in n0; repnd; tcsp);
        try (complete (remember (sub_find sub a) as sf'; symmetry in Heqsf'; destruct sf'; simpl in *;
                       tcsp; boolvar; subst; tcsp; allrw; boolvar; tcsp)).
Qed.

Hint Resolve areprograms_nil : slow.
Hint Resolve lsubst_program_implies : slow.

Lemma implies_areprograms_sub2terms {o} :
  forall (sub : @Sub o) d l,
    prog_sub sub
    -> isprogram d
    -> areprograms (sub2terms sub d l).
Proof.
  induction l; introv ps isp; simpl in *; eauto 3 with slow.
  remember (sub_find sub a) as sf; symmetry in Heqsf; destruct sf;
    allrw @areprograms_cons; dands; eauto 2 with slow.
  rw <- @prog_sub_eq in ps; apply ps; eauto 3 with slow.
  apply sub_find_some_implies_in_range in Heqsf; auto.
Qed.
Hint Resolve implies_areprograms_sub2terms : slow.

Lemma lsubst_as_combine {o} :
  forall (t : @NTerm o) sub l,
    prog_sub sub
    -> subset (free_vars t) l
    -> subset (free_vars t) (dom_sub sub)
    -> {ts : list NTerm
        & length l = length ts
        # lsubst t sub = lsubst t (combine l ts)
        # areprograms ts
        # ts = sub2terms sub mk_axiom l}.
Proof.
  introv cl ssa ssb.
  exists (sub2terms sub mk_axiom l).
  autorewrite with slow; dands; auto; eauto 2 with slow;[].
  apply cl_eq_lsubst_if_ext_eq; eauto 3 with slow;[].
  introv i.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl.

  { applydup ssa in i.
    rewrite sub_find_combine_sub2terms; allrw; boolvar; tcsp. }

  { apply ssb in i.
    apply sub_find_none2 in Heqsf; tcsp. }
Qed.

Lemma simpl_olift_as_cl_olift {o} :
  forall R (t1 t2 : @NTerm o) l,
    subset (free_vars t1) l
    -> subset (free_vars t2) l
    -> (simpl_olift R t1 t2 <=> cl_olift R t1 t2 l).
Proof.
  introv ssa ssb; split; introv h; unfold cl_olift, simpl_olift in *; repnd; dands; auto; introv.

  { introv len aps.
    apply h; eauto 2 with slow. }

  { introv ps ispa ispb.
    pose proof (lsubst_as_combine t1 sub l) as qa.
    repeat (autodimp qa hyp); eauto 2 with slow; exrepnd;[].
    pose proof (lsubst_as_combine t2 sub l) as qb.
    repeat (autodimp qb hyp); eauto 2 with slow; exrepnd;[].
    rewrite <- qa0 in qb0; subst ts0; clear qa0.
    rewrite qa2, qb2 in *.
    apply h; auto. }
Qed.

Lemma approx_open_cl_equiv {o} :
  forall l lib (a b : @NTerm o),
    subset (free_vars a) l
    -> subset (free_vars b) l
    -> cl_olift (approx lib) a b l
    -> approx_open lib a b.
Proof.
  introv ssa ssb cl.
  apply approx_open_simpler_equiv.
  eapply simpl_olift_as_cl_olift; eauto.
Qed.

Lemma computes_to_value_can_implies_swap_cs2 {o} :
  forall sw lib (t : @NTerm o) c bs,
    t =v>(lib) (oterm (Can c) bs)
    -> mk_swap_cs2 sw t =v>(lib) (push_swap_cs_can sw c bs).
Proof.
  introv comp.
  unfold computes_to_value in *; repnd.
  dands; eauto 3 with slow.
  eapply reduces_to_trans;
    [eapply implies_reduces_to_mk_swap_cs2;
     eapply swap_reduces_to;eauto|].
  autorewrite with slow.
  apply reduces_to_if_step; auto.
Qed.

Definition sw_sub_ts2 {o} a b l (k : list (@NTerm o)) : @Sub o :=
  combine l (map (fun t => mk_swap_cs2 a b (mk_swap_cs2 a b t)) k).

Lemma implies_areprograms_map_mk_swap_cs2 {o} :
  forall a b (ts : list (@NTerm o)),
    areprograms ts
    -> areprograms (map (mk_swap_cs2 a b) ts).
Proof.
  introv aps i; apply in_map_iff in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve implies_areprograms_map_mk_swap_cs2 : slow.

Lemma lsubst_sw_sub_lsubst_aux_combine_eq2 {o} :
  forall a b (t : @NTerm o) l ts,
    length l = length ts
    -> no_repeats l
    -> areprograms ts
    -> disjoint (bound_vars t) l
    -> subset (free_vars t) l
    -> lsubst (lsubst_aux t (sw_sub a b l)) (sw_sub_ts a b l ts)
       = lsubst t (sw_sub_ts2 a b l ts).
Proof.
  introv len norep aps disj ss.
  unfold sw_sub_ts.
  rewrite lsubst_sw_sub_lsubst_aux_combine_eq; autorewrite with slow; eauto 2 with slow; auto.
  unfold sw_sub_ts, sw_sub_ts2.
  rewrite map_map; auto.
Qed.

Lemma areprograms_implies_prog_sw_sub_ts2 {o} :
  forall a b l (ts : list (@NTerm o)),
    areprograms ts
    -> prog_sub (sw_sub_ts2 a b l ts).
Proof.
  unfold sw_sub_ts2; induction l; introv aps; simpl in *; eauto 3 with slow.
  destruct ts; simpl in *; eauto 3 with slow.
  allrw @areprograms_cons; repnd.
  allrw @prog_sub_cons; dands; eauto 3 with slow.
Qed.
Hint Resolve areprograms_implies_prog_sw_sub_ts2 : slow.

Lemma dom_sub_sw_sub_ts2 {o} :
  forall a b l k,
    length l = length k
    -> @dom_sub o (sw_sub_ts2 a b l k) = l.
Proof.
  introv len.
  unfold sw_sub_ts2.
  rewrite dom_sub_combine_le; autorewrite with slow; auto; try omega.
Qed.

Lemma implies_isprogram_lsubst_sw_sub_ts2 {o} :
  forall (t : @NTerm o) a b l ts,
    nt_wf t
    -> subset (free_vars t) l
    -> length l = length ts
    -> areprograms ts
    -> isprogram (lsubst t (sw_sub_ts2 a b l ts)).
Proof.
  introv wf ss len aps.
  apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
  rewrite dom_sub_sw_sub_ts2; auto.
Qed.
Hint Resolve implies_isprogram_lsubst_sw_sub_ts2 : slow.

Lemma implies_approx_sub_combine {o} :
  forall lib l (ts1 ts2 : list (@NTerm o)),
    length l = length ts1
    -> length l = length ts2
    -> (forall t1 t2, LIn (t1,t2) (combine ts1 ts2) -> approx lib t1 t2)
    -> approx_sub lib (combine l ts1) (combine l ts2).
Proof.
  induction l; introv lena lenb imp; simpl in *; cpx.
  destruct ts1, ts2; simpl in *; cpx.
Qed.

Lemma implies_clearbots_olift {o} :
  forall lib (nt1 nt2 : @NTerm o),
    approx_open lib nt1 nt2
    -> olift (approx_aux lib bot2 \2/ bot2) nt1 nt2.
Proof.
  introv h; apply clearbots_olift; auto.
Qed.

Inductive rel_sub {o} (r : bin_rel (@NTerm o)) : Sub -> Sub -> tuniv :=
  rel_sub_nil : rel_sub r [] []
| rel_sub_cons :
    forall (v : NVar) (t1 t2 : NTerm) (s1 s2 : Sub),
      r t1 t2
      -> rel_sub r s1 s2
      -> rel_sub r ((v, t1) :: s1) ((v, t2) :: s2).

Definition rel_open {o} (r : bin_rel (@NTerm o)) t1 t2 :=
  forall l, cl_olift r t1 t2 l.

Definition is_congr {o} (r : bin_rel (@NTerm o)) :=
  forall t1 t2 sub1 sub2,
    rel_sub r sub1 sub2
    -> rel_open r t1 t2
    -> isprogram (lsubst t1 sub1)
    -> isprogram (lsubst t2 sub2)
    -> r (lsubst t1 sub1) (lsubst t2 sub2).

Theorem approx_acc_resp_tr {p} :
  forall (lib : plibrary)
         (l r0 : bin_rel (@NTerm p))
         (resp_l_l : respects_alpha_l l)
         (resp_r_l : respects_alpha_r l)
         (resp_l_r0 : respects_alpha_l r0)
         (resp_r_r0 : respects_alpha_r r0)
         (trans : trans_rel (r0 \2/ l))
         (OBG : forall (r: bin_rel NTerm)
                       (INC: r0 =2> r)
                       (CIH: l =2> r)
                       (resp_r : respects_alpha_r r)
                       (resp_l : respects_alpha_l r)
                       (trans : trans_rel r),
                  l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros.
  assert (SIM: approx_aux lib (r0 \2/ l) x0 x1) by (apply OBG; eauto 3 with slow).
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna c Hcl. repnd.
  unfold close_comput.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    repndors; tcsp.
    left.
    apply CIH; apply OBG; eauto 3 with slow.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd.
    exists a' e'; dands; auto; repndors; auto; tcsp;
    try (complete (left; apply CIH; apply OBG; tcsp; eauto 3 with slow)).
Qed.

Theorem approx_acc_resp_cg {p} :
  forall (lib : plibrary)
         (l r0 : bin_rel (@NTerm p))
         (resp_l_l : respects_alpha_l l)
         (resp_r_l : respects_alpha_r l)
         (resp_l_r0 : respects_alpha_l r0)
         (resp_r_r0 : respects_alpha_r r0)
         (congr : is_congr (r0 \2/ l))
         (trans : trans_rel (r0 \2/ l))
         (OBG : forall (r: bin_rel NTerm)
                       (INC: r0 =2> r)
                       (CIH: l =2> r)
                       (resp_r : respects_alpha_r r)
                       (resp_l : respects_alpha_l r)
                       (congr : is_congr r)
                       (trans_rel : trans_rel r),
                  l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros.
  assert (SIM: approx_aux lib (r0 \2/ l) x0 x1).
  { apply OBG; eauto 3 with slow. }
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna c Hcl. repnd.
  unfold close_comput.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    repndors; tcsp.
    left.
    apply CIH; apply OBG; eauto 3 with slow.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd.
    exists a' e'; dands; auto; repndors; auto; tcsp;
    try (complete (left; apply CIH; apply OBG; tcsp; eauto 3 with slow)).
Qed.

Fixpoint mk_swap_cs2_N {o} n a b (t : @NTerm o) :=
  match n with
  | 0 => t
  | S n => mk_swap_cs2 a b (mk_swap_cs2 a b (mk_swap_cs2_N n a b t))
end.

Lemma implies_alpha_eq_mk_swap_cs2_N {o} :
  forall n a b (t u : @NTerm o),
    alpha_eq t u
    -> alpha_eq (mk_swap_cs2_N n a b t) (mk_swap_cs2_N n a b u).
Proof.
  induction n; introv aeq; simpl; eauto 3 with slow.
  repeat apply implies_alpha_eq_mk_swap_cs2; auto.
Qed.
Hint Resolve implies_alpha_eq_mk_swap_cs2_N : slow.

Lemma mk_swap_cs2_N_twice {o} :
  forall n m a b (t : @NTerm o),
    mk_swap_cs2_N n a b (mk_swap_cs2_N m a b t) = mk_swap_cs2_N (n + m) a b t.
Proof.
  induction n; introv; simpl; auto.
  rewrite IHn; auto.
Qed.
Hint Rewrite @mk_swap_cs2_N_twice : slow.

Lemma implies_prog_sub_sub_keep_first {o} :
  forall (u : @NTerm o) sub,
    isprogram (lsubst u sub)
    -> prog_sub (sub_keep_first sub (free_vars u)).
Proof.
  introv isp i.
  apply in_sub_keep_first in i; repnd.
  apply isprogram_lsubst_iff in isp; repnd.
  applydup isp in i; exrepnd.
  rewrite i1 in *; ginv.
  split; auto.
Qed.
Hint Resolve implies_prog_sub_sub_keep_first : slow.

Lemma subset_dom_sub_sub_keep_first {o} :
  forall l (sub : @Sub o),
    subset l (dom_sub sub)
    -> subset l (dom_sub (sub_keep_first sub l)).
Proof.
  introv ss i.
  pose proof (eqvars_dom_sub_sub_keep_first sub l) as q.
  autodimp q hyp.
  { apply subvars_eq; auto. }
  apply eqvars_is_eqset in q; apply q; auto.
Qed.
Hint Resolve subset_dom_sub_sub_keep_first : slow.

(*Lemma approx_mk_swap_cs2_twice {o} :
  forall lib a b (t : @NTerm o),
    isprog t
    -> approx lib (mk_swap_cs2 a b (mk_swap_cs2 a b t)) t.
Proof.
  introv; revert t.
  pose proof (approx_acc_resp_cg
                lib
                (fun t1 t2 => isprog t2 # {n : nat & alpha_eq t1 (mk_swap_cs2_N n a b t2)})
                (@bot2 o)) as h.
  simpl in h.
  introv isp.
  apply h; auto; clear h; eauto 2 with slow;
    try (complete (dands; auto; exists 1; simpl; auto)).
  { introv h q; exrepnd; subst; dands; auto; exists n; eauto 3 with slow. }
  { introv h q; exrepnd; subst; dands; eauto 2 with slow; exists n; eauto 3 with slow. }
  { introv h q ispa ispb; right; allrw @isprog_eq; dands; auto.

}
  { introv h q; repndors; exrepnd; subst; dands; tcsp.
    apply (implies_alpha_eq_mk_swap_cs2_N n0 a b) in q1.
    right; dands; auto; exists (n0 + n); autorewrite with slow in *; eauto 2 with slow. }

  introv h q respa respb trans w; exrepnd; subst.
  eapply respects_alpha_l_approx_aux; try apply alpha_eq_sym; try exact w1; auto.
  clear w1.
  clear dependent t.
  rename x1 into t; rename w0 into isp.
  assert (forall t n, isprog t -> r (mk_swap_cs2_N n a b t) t) as q' by (introv isp'; apply q; dands; eauto).
  clear q; rename q' into ind.
  constructor; unfold close_comput; dands; auto;
    repeat apply implies_isprogram_mk_swap_cs2;
    eauto 2 with slow; introv comp;[|].

  { (* VAL case *)

    apply swap_cs2_computes_to_value_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    apply swap_cs2_computes_to_value_implies in comp0;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    inversion comp0; subst; clear comp0.
    inversion comp1; subst; clear comp1.
    autorewrite with slow.
    exists bs0; dands; auto.
    unfold lblift; autorewrite with slow; dands; auto.
    introv i.
    unfold blift, push_swap_cs_bterms.
    repeat (rewrite selectbt_map; autorewrite with slow; auto).

    applydup @computes_to_value_implies_isprogram in comp2.
    dup i as wf.
    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (change_bvars_alpha_norep_bterm (bs0 {[n]}) []) as ha; destruct ha as [b1 ha]; repnd.
    destruct b1 as [l u]; simpl in *.
    allrw no_repeats_app; repnd.
    eapply alpha_eq_bterm_preserves_isprogram_bt in wf; eauto.
    eapply respect_eauto_albt in wf0; eauto.
    allrw @bt_wf_iff.

    exists l (mk_swap_cs2 a b (mk_swap_cs2 a b (push_swap_cs_sub_term a b l (push_swap_cs_sub_term a b l u)))) u.
    dands; auto;
      [|eapply alpha_eq_bterm_trans;
        [repeat apply implies_alpha_eq_bterm_push_swap_cs_bterm; eauto|];
        simpl; unfold push_swap_cs_sub_term; simpl; autorewrite with slow; auto];[].

    assert (subset (free_vars u) l) as ssa by eauto 2 with slow.

    apply approx_open_simpler_equiv_r; eauto 3 with slow.
    apply (simpl_olift_as_cl_olift _ _ _ l); simpl; autorewrite with slow; auto;[].
    unfold cl_olift; dands; repeat apply implies_nt_wf_mk_swap_cs2; eauto 3 with slow;[].
    introv len aps.
    repeat rewrite lsust_mk_swap_cs2_eq.

    unfold push_swap_cs_sub_term; simpl.
    repeat (rewrite lsubst_sw_sub_lsust_aux_combine_eq; autorewrite with slow; eauto 2 with slow).
    repeat (rewrite lsubst_sw_sub_lsust_aux_combine_eq2; autorewrite with slow; eauto 2 with slow).


    (* in addition to alpha-respecting, we would need a version of approx_acc_resp
       where r is also transitive and a congruence... *)

XXXXX

    eapply approx_trans;
      [apply ind; apply isprog_eq; apply isprogram_lsubst_if_isprog_sub;
       autorewrite with slow; eauto 3 with slow
      |];[].

    apply lsubst_approx_congr2; eauto 3 with slow.
    apply implies_approx_sub_combine; autorewrite with slow; auto.
    introv j; rewrite <- map_combine_left in j; apply in_map_iff in j; exrepnd; ginv.
    apply in_combine_same in j1; repnd; subst.
    applydup aps in j0.
    apply ind; eauto 2 with slow. }

  { (* EXC case *)

    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
    exists a0 e; dands; auto; left; apply approx_refl; auto. }
Qed.*)

Lemma approx_mk_swap_cs2_twice {o} :
  forall lib a b (t : @NTerm o),
    isprog t
    -> approx lib (mk_swap_cs2 a b (mk_swap_cs2 a b t)) t.
Proof.
  cofix ind; introv isp.
  constructor; unfold close_comput; dands; auto;
    repeat apply implies_isprogram_mk_swap_cs2;
    eauto 2 with slow; introv comp;[|].

  { (* VAL case *)

    apply swap_cs2_computes_to_value_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    apply swap_cs2_computes_to_value_implies in comp0;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    inversion comp0; subst; clear comp0.
    inversion comp1; subst; clear comp1.
    autorewrite with slow.
    exists bs0; dands; auto.
    unfold lblift; autorewrite with slow; dands; auto.
    introv i.
    unfold blift, push_swap_cs_bterms.
    repeat (rewrite selectbt_map; autorewrite with slow; auto).

    applydup @computes_to_value_implies_isprogram in comp2.
    dup i as wf.
    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (change_bvars_alpha_norep_bterm (bs0 {[n]}) []) as ha; destruct ha as [b1 ha]; repnd.
    destruct b1 as [l u]; simpl in *.
    allrw no_repeats_app; repnd.
    eapply alpha_eq_bterm_preserves_isprogram_bt in wf; eauto.
    eapply respect_eauto_albt in wf0; eauto.
    allrw @bt_wf_iff.

    exists l (mk_swap_cs2 a b (mk_swap_cs2 a b (push_swap_cs_sub_term a b l (push_swap_cs_sub_term a b l u)))) u.
    dands; auto;
      [|eapply alpha_eq_bterm_trans;
        [repeat apply implies_alpha_eq_bterm_push_swap_cs_bterm; eauto|];
        simpl; unfold push_swap_cs_sub_term; simpl; autorewrite with slow; auto];[].

    assert (subset (free_vars u) l) as ssa by eauto 2 with slow.

    assert (forall (ts : list NTerm),
               length l = length ts
               -> areprograms ts
               -> approx_sub lib (sw_sub_ts2 a b l ts) (combine l ts)) as aps1.
    { introv len aps.
      apply implies_approx_sub_combine; autorewrite with slow; auto.
      introv j; rewrite <- map_combine_left in j; apply in_map_iff in j; exrepnd; ginv.
      apply in_combine_same in j1; repnd; subst.
      applydup aps in j0.
      apply ind; eauto 2 with slow. }

    assert (approx_open lib (mk_swap_cs2 a b (mk_swap_cs2 a b u)) u) as aps2.
    { apply (approx_open_cl_equiv l); simpl; autorewrite with slow; auto.
      unfold cl_olift; dands; repeat apply implies_nt_wf_mk_swap_cs2; eauto 3 with slow;[].
      introv len' aps'.
      repeat rewrite lsust_mk_swap_cs2_eq.
      apply ind.
      apply isprog_eq; apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow. }

(* XXXXXXXX *)
    assert (cl_olift (approx lib)
                     (mk_swap_cs2 a b (mk_swap_cs2 a b (push_swap_cs_sub_term a b l (push_swap_cs_sub_term a b l u))))
                     u l) as cl.
    2:{ unfold olift, cl_olift in *; repnd; dands; auto;[].
        introv ps ispa ispb; left.
        pose proof (lsubst_as_combine (mk_swap_cs2 a b (mk_swap_cs2 a b (push_swap_cs_sub_term a b l (push_swap_cs_sub_term a b l u)))) (sub_keep_first sub (free_vars u)) l) as qa.
        repeat (autodimp qa hyp); simpl; autorewrite with slow; eauto 3 with slow; exrepnd;[].
        pose proof (lsubst_as_combine u (sub_keep_first sub (free_vars u)) l) as qb.
        repeat (autodimp qb hyp); eauto 3 with slow; exrepnd;[].
        rewrite <- qa0 in qb0; subst ts0; clear qa0.
        eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;apply lsubst_trim_alpha|].
        eapply approx_alpha_rw_r_aux;[apply alpha_eq_sym;apply lsubst_trim_alpha|].
        simpl; autorewrite with slow.
        rewrite qa2, qb2 in *.
        apply cl; auto. }
(* XXXXXXXXXX *)

(*    apply implies_clearbots_olift.
    apply (approx_open_cl_equiv l); simpl; autorewrite with slow; auto.*)
    unfold cl_olift; dands; repeat apply implies_nt_wf_mk_swap_cs2; eauto 3 with slow;[].
    introv len aps.
    repeat rewrite lsust_mk_swap_cs2_eq.

    unfold push_swap_cs_sub_term; simpl.
    rewrite lsubst_sw_sub_lsubst_aux_combine_eq; autorewrite with slow; eauto 2 with slow.
    rewrite lsubst_sw_sub_lsubst_aux_combine_eq2; autorewrite with slow; eauto 2 with slow.
    repeat rewrite <- lsust_mk_swap_cs2_eq.

    apply lsubst_approx_congr2; eauto 2 with slow.
    apply isprogram_lsubst_if_isprog_sub; simpl; autorewrite with slow; eauto 3 with slow. }

  { (* EXC case *)

    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
    exists a0 e; dands; auto; left; apply approx_refl; auto. }
Admitted.

Lemma approx_mk_swap_cs2_twice_rev {o} :
  forall lib a b (t : @NTerm o),
    isprog t
    -> approx lib t (mk_swap_cs2 a b (mk_swap_cs2 a b t)).
Proof.
  cofix ind; introv isp.
  constructor; unfold close_comput; dands; auto;
    repeat apply implies_isprogram_mk_swap_cs2;
    eauto 2 with slow; introv comp;[|].

  { (* VAL case *)

    apply (computes_to_value_can_implies_swap_cs2 a b) in comp.
    apply (computes_to_value_can_implies_swap_cs2 a b) in comp.
    unfold push_swap_cs_can in comp; simpl in comp; autorewrite with slow in comp.
    eexists; dands; eauto.

    unfold lblift; autorewrite with slow; dands; auto.
    introv i.
    unfold blift, push_swap_cs_bterms.
    repeat (rewrite selectbt_map; autorewrite with slow; auto).

    applydup @computes_to_value_implies_isprogram in comp.
    dup i as wf.

    apply isprogram_ot_iff in comp0; autorewrite with slow in comp0; repnd.

(*    remember (selectbt tl_subterms n) as bt; destruct bt; simpl.
    pose proof (comp0 (bterm l (mk_swap_cs2 a b (mk_swap_cs2 a b n0)))) as comp0; autodimp comp0 hyp.
    { apply in_map_iff; exists (bterm l (mk_swap_cs2 a b n0)); dands; auto.
      apply in_map_iff; exists (bterm l n0); dands; auto.
      allrw; eauto 3 with slow. }
    applydup @isprogram_bt_implies_bt_wf in comp0.
    allrw @bt_wf_iff.
    repeat apply nt_wf_mk_swap_cs2_implies in comp2.
    exists l n0 (mk_swap_cs2 a b (mk_swap_cs2 a b n0)); dands; auto.
    unfold olift.
    dands; eauto 3 with slow;[].
    introv wfs ispa ispb; left.
    repeat rewrite lsust_mk_swap_cs2_eq.
    apply ind; apply isprog_eq; auto.*)

admit.
 }

  { (* EXC case *)

    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc a b) in comp.
    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc a b) in comp.
    applydup @preserve_program_exc2 in comp; repnd;
      repeat apply implies_isprogram_mk_swap_cs2; eauto 3 with slow;[].
    exists a0 e; dands; auto; left; apply approx_refl; auto. }
Admitted.

Lemma approx_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @NTerm o),
    approx lib (mk_swap_cs2 a b t1) (mk_swap_cs2 a b t2)
    -> approx lib t1 t2.
Proof.
  cofix ind; introv ap.
  apply approx_relates_only_progs in ap as isp; repnd.
  allrw @isprogram_mk_swap_cs2_iff.

  constructor; unfold close_comput; dands; auto; introv comp.

  { (* CAN case*)

    rename tl_subterms into bterms.
    unfold computes_to_value in comp; repnd.

    assert (reduces_to lib (mk_swap_cs2 a b t1) (push_swap_cs_can a b c bterms)) as r.
    { eapply reduces_to_trans;[eapply reduces_to_prinarg; eauto|].
      apply reduces_to_if_step; csunf; simpl; auto. }
    applydup @reduces_to_preserves_program in comp0; auto;[].
    eapply approx_canonical_form in ap;
      [|unfold computes_to_value; dands; eauto;
        apply implies_isvalue_push_swap_cs_can; auto].
    exrepnd.

    applydup @swap_cs2_computes_to_value_implies in ap1; eauto 3 with slow; exrepnd.
    unfold push_swap_cs_can in ap2; inversion ap2 as [ec]; subst; clear ap2.
    apply swap_cs_can_inj in ec; subst.
    exists bs; dands; auto.

    unfold lblift in *; autorewrite with slow in *; repnd; dands; auto.
    introv i; applydup ap0 in i; clear ap0.

    unfold push_swap_cs_bterms in i0.
    repeat (rewrite selectbt_map in i0; autorewrite with slow in i0; auto; try omega).
    apply (blift_oliftd _ _ _ []) in i0; auto; exrepnd.

    pose proof (change_bvars_alpha_norep_bterm (bterms {[n]}) lvn) as ha; destruct ha as [b1 ha]; repnd.
    eapply alpha_eq_bterm_trans in i2;
      [|apply implies_alpha_eq_bterm_push_swap_cs_bterm; apply alpha_eq_bterm_sym; eauto].
    destruct b1 as [l u1].
    applydup @alphaeqbt_numbvars in ha1; simpl in *; autorewrite with slow in *.
    applydup @alphaeqbt_numbvars in i3; simpl in *; autorewrite with slow in *.
    applydup @alphaeqbt_numbvars in i2; simpl in *; autorewrite with slow in *.
    allrw no_repeats_app; repnd.
    allrw disjoint_app_r; repnd.
    applydup @computes_to_value_isvalue in ap3 as isv.

    pose proof (change_bvars_to (bs {[n]}) l lvn) as hb.
    repeat (autodimp hb hyp); try congruence; eauto 2 with slow;[].
    destruct hb as [u2 hb]; repnd.
    eapply alpha_eq_bterm_trans in i3;
      [|apply implies_alpha_eq_bterm_push_swap_cs_bterm; apply alpha_eq_bterm_sym; eauto].

    eexists; eexists; eexists; dands; try exact ha1; try exact hb0;[].
    apply alpha_eq_bterm_sym in i3; apply alpha_eq_bterm_ren_1side2 in i3;[].
    apply alpha_eq_bterm_sym in i2; apply alpha_eq_bterm_ren_1side2 in i2;[].
    rewrite lsust_mk_swap_cs2_eq in i3, i2.

    assert (subset (free_vars u1) l) as ssa.
    { pose proof (isprog_oterm_implies_null_free_vars_bterm (Can c0) bterms n) as q.
      autodimp q hyp; eauto 2 with slow.
      apply alpha_eq_bterm_preserves_free_vars in ha1; rewrite ha1 in q; simpl in q.
      apply null_remove_nvars_subvars in q; apply subvars_eq in q; auto. }

    assert (subset (free_vars u2) l) as ssb.
    { pose proof (isprog_oterm_implies_null_free_vars_bterm (Can c0) bs n) as q.
      autodimp q hyp; eauto 3 with slow.
      apply alpha_eq_bterm_preserves_free_vars in hb0; rewrite hb0 in q; simpl in q.
      apply null_remove_nvars_subvars in q; apply subvars_eq in q; auto. }

    assert (disjoint lvn (free_vars u1)) as da by eauto 3 with slow.
    assert (disjoint lvn (free_vars u2)) as db by eauto 3 with slow.

    unfold push_swap_cs_sub_term in *.
    eapply approx_open_alpha_rw_l_aux in i0;[|exact i2].
    eapply approx_open_alpha_rw_r_aux in i0;[|exact i3].
    repeat (rewrite lsubst_lsubst_aux in i0;
            [|autorewrite with slow; rewrite flat_map_free_var_vars_range; eauto 2 with slow];[]).
    repeat (rewrite lsubst_aux_sw_sub_var_ren in i0; auto;[]).
    apply clearbots_olift.
    unfold approx_open, olift in i0; repnd.
    apply nt_wf_mk_swap_cs2_implies in i7; apply lsubst_aux_nt_wf in i7.
    apply nt_wf_mk_swap_cs2_implies in i8; apply lsubst_aux_nt_wf in i8.
    apply (approx_open_cl_equiv l); auto;[].
    unfold cl_olift; dands; auto;[].
    introv len aps.
    pose proof (i0 (sw_sub_ts a b lvn ts)) as i0.
    repeat (autodimp i0 hyp); eauto 2 with slow;
      try (complete (apply isprogram_mk_swap_cs2_sw_sub2_sw_sub_ts; auto; try congruence)).
    repeat rewrite lsust_mk_swap_cs2_eq in i0.

    apply ind in i0.

(*
SearchAbout approx lsubst.

(* We now need to combine the substitutions and use something like [approx_mk_swap_cs2_twice] below *)

XXXXXX
    , b2 as [l2 u2]; simpl in *.

SearchAbout alpha_eq_bterm disjoint no_repeats alpha_eq.


    inversion i2 as [? ? ? ? ? disj1 lena1 lenb1 norep1 aeq1]; subst; clear i2.
    inversion i1 as [? ? ? ? ? disj2 lena2 lenb2 norep2 aeq2]; subst; clear i1.
    autorewrite with slow in disj1, disj2.
    apply disjoint_app_r in disj1; repnd.
    apply disjoint_app_r in disj2; repnd.

    rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in aeq1;
      [|rewrite computation_mark.sub_free_vars_var_ren; autorewrite with slow; auto];[].
    rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in aeq2;
      [|rewrite computation_mark.sub_free_vars_var_ren; autorewrite with slow; auto];[].

(*    rewrite lsubst_push_swap_cs_sub_term_var_ren_as in aeq1; auto;[].
    rewrite lsubst_push_swap_cs_sub_term_var_ren_as in aeq2; auto;[].*)

    apply swap_cs2_alpha_eq_implies in aeq1; exrepnd.
    apply swap_cs2_alpha_eq_implies in aeq2; exrepnd.
    apply lsubst_eq_swap2_implies in aeq1; auto; exrepnd; subst; try congruence;[].
    apply lsubst_eq_swap2_implies in aeq2; auto; exrepnd; subst; try congruence;[].
    autorewrite with slow in disj1, disj2.


rewrite lsubst_push_swap_cs_sub_term_var_ren_eq in aeq0; auto;[].
rewrite lsubst_push_swap_cs_sub_term_var_ren_eq in aeq3; auto;[].
rewrite lsubst_lsubst_aux in aeq0;
  [|rewrite flat_map_free_var_vars_range; try omega; allrw disjoint_app_r; repnd; eauto 2 with slow];[].
rewrite lsubst_lsubst_aux in aeq3;
  [|rewrite flat_map_free_var_vars_range; try omega; allrw disjoint_app_r; repnd; eauto 2 with slow];[].



Set Nested Proofs Allowed.


Lemma lsubst_aux_sw_sub2_alpha_eq_lsubst_aux_var_ren_implies {o} :
  forall a b (t u : @NTerm o) l k j,
    disjoint l (all_vars t)
    -> disjoint l (all_vars u)
    -> length j = length l
    -> length k = length l
    -> alpha_eq (lsubst_aux t (sw_sub2 a b k l)) (lsubst_aux u (var_ren j l))
    -> {z : NTerm
        & u = lsubst_aux z (sw_sub a b j)
        # alpha_eq (lsubst_aux t (var_ren k l)) (lsubst_aux z (var_ren j l))}.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv disja disjb lena lenb aeq; simpl in *.

  { rewrite sub_find_sw_sub2 in aeq.
    rewrite sub_find_var_ren_as_option_map in aeq.
    rewrite sub_find_var_ren_as_option_map.
    remember (renFind (mk_swapping k l) v) as w; symmetry in Heqw; destruct w; simpl in *.

    { apply swap_cs2_alpha_eq_implies in aeq; exrepnd.
      inversion aeq0; subst; clear aeq0.
      apply lsubst_aux_eq_swap2_implies in aeq1; auto; exrepnd; subst; simpl in *.
      applydup @lsubst_aux_is_vterm    in aeq0; exrepnd; subst; simpl in *.
      rewrite sub_find_var_ren_as_option_map in aeq0.
      remember (renFind (mk_swapping j l) u) as r; symmetry in Heqr; destruct r; simpl in *; ginv.

      { exists (@mk_var o u); simpl.
        autorewrite with slow.
        applydup renFind_implies_in in Heqr.
        rewrite sub_find_sw_sub; boolvar; tcsp;[]; GC.
        rewrite sub_find_var_ren_as_option_map; allrw; simpl.
        dands; tcsp. }

      unfold all_vars in *; simpl in *; allrw disjoint_singleton_r.
      symmetry in Heqw; apply renFind_some_in_codom in Heqw; tcsp. }

    inversion aeq as [? xx eqv|]; subst; clear aeq.
    applydup @lsubst_aux_is_vterm in eqv; exrepnd; subst; simpl in *.
    rewrite sub_find_var_ren_as_option_map in eqv.
    remember (renFind (mk_swapping j l) u0) as r; symmetry in Heqr; destruct r; simpl in *; ginv.

    { unfold all_vars in *; simpl in *; allrw disjoint_singleton_r.
      symmetry in Heqr; apply renFind_some_in_codom in Heqr; tcsp. }

    exists (@mk_var o u0); simpl.
    repeat rewrite sub_find_var_ren_as_option_map; allrw; simpl.
    rewrite sub_find_sw_sub; boolvar; tcsp.
    eapply implies_renFind_Some in l0; eauto; exrepnd; rewrite l1 in *; ginv. }

  destruct u as [v'|op' bs']; simpl in *.

  { rewrite sub_find_var_ren_as_option_map in aeq.
    remember (renFind (mk_swapping j l) v') as r; destruct r; inversion aeq. }

  apply alpha_eq_oterm_combine2 in aeq; repnd; autorewrite with slow in *; subst; simpl in *.

  assert {bs'' : list BTerm
          $ bs' = map (fun x => lsubst_bterm_aux x (sw_sub a b j)) bs''
          # alpha_eq_bterms
             (map (fun b => lsubst_bterm_aux b (var_ren k l)) bs)
             (map (fun b => lsubst_bterm_aux b (var_ren j l)) bs'')}.
  { revert dependent bs'.
    induction bs; introv disj len imp; simpl in *.
    { destruct bs'; simpl in *; ginv.
      exists ([] : list (@BTerm o)); simpl; dands; eauto 3 with slow. }
    destruct bs'; simpl in *; cpx;[].
    pose proof (imp (lsubst_bterm_aux a0 (sw_sub2 a b k l)) (lsubst_bterm_aux b0 (var_ren j l))) as imp'.
    autodimp imp' hyp;[].
    repeat (autodimp IHbs hyp).
    { introv i; eapply ind; eauto. }
    { unfold all_vars in *; simpl in *; allrw disjoint_app_r; repnd; dands; auto. }
    pose proof (IHbs bs') as IHbs.
    repeat (autodimp IHbs hyp).
    { unfold all_vars in *; simpl in *; allrw disjoint_app_r; repnd; dands; auto. }
    exrepnd; subst.
    autorewrite with slow in *.

    inversion imp' as [? ? ? ? ? disj' disj'' len' norep aeq' xa xb].
    destruct a0 as [l1 t1], b0 as [l2 t2]; simpl in *; ginv.

  }

Qed.
*)

(*    exists lv z1 z; dands; auto;
      try (complete (econstructor; try exact norep1; auto; apply disjoint_app_r; auto));
      try (complete (econstructor; try exact norep2; auto; apply disjoint_app_r; auto)).

    unfold approx_open, olift in *; repnd.
    apply nt_wf_mk_swap_cs2_implies in i1.
    apply nt_wf_mk_swap_cs2_implies in i2.
    dands; auto.
    introv wf cova covb.
    pose proof (i0 sub) as i0; repeat (autodimp i0 hyp);
      try (apply implies_isprogram_lsust_mk_swap_cs2); auto;[].
    repeat rewrite lsust_mk_swap_cs2_eq in i0.
    left; apply ind in i0; auto.*)

admit.

 }

  { (* EXC case *)

    eapply exception_approx in ap;
      [|eapply reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc; eauto].
    exrepnd.
    repndors; try (complete (inversion ap1)); try (complete (inversion ap2)).
    apply swap_cs2_computes_to_exc_implies in ap0; eauto 3 with slow.
    exists a' e'; dands; auto. }
Admitted.

(*
Lemma approx_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @NTerm o),
    approx lib (mk_swap_cs2 a b t1) (mk_swap_cs2 a b t2)
    -> approx lib t1 t2.
Proof.
  introv apx.
  pose proof (change_bvars_alpha_norep t1 []) as h; exrepnd.
  pose proof (change_bvars_alpha_norep t2 []) as q; exrepnd.
  eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;eauto|].
  eapply approx_alpha_rw_r_aux;[apply alpha_eq_sym;eauto|].
  eapply approx_alpha_rw_l_aux in apx;[|apply implies_alpha_eq_mk_swap_cs2;eauto].
  eapply approx_alpha_rw_r_aux in apx;[|apply implies_alpha_eq_mk_swap_cs2;eauto].

Qed.*)


Lemma cequiv_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @NTerm o),
    cequiv lib (mk_swap_cs2 a b t1) (mk_swap_cs2 a b t2)
    -> cequiv lib t1 t2.
Proof.
  introv ceq; destruct ceq as [ap1 ap2].
  apply approx_swap_cs2_implies in ap1.
  apply approx_swap_cs2_implies in ap2.
  split; auto.
Qed.

Lemma cequivc_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    cequivc lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> cequivc lib t1 t2.
Proof.
  introv; destruct_cterms; unfold cequivc; simpl; apply cequiv_swap_cs2_implies.
Qed.

Lemma approxc_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    approxc lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> approxc lib t1 t2.
Proof.
  introv; destruct_cterms; unfold approxc; simpl.
  apply approx_swap_cs2_implies.
Qed.

Lemma capproxc_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    capproxc lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> capproxc lib t1 t2.
Proof.
  introv h; spcast.
  apply approxc_swap_cs2_implies in h; auto.
Qed.

Lemma ccequivc_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    ccequivc lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> ccequivc lib t1 t2.
Proof.
  introv h; spcast.
  apply cequivc_swap_cs2_implies in h; auto.
Qed.

Lemma mkc_swap_per_base_eq {o} :
  forall sw lib (eq : per(o)),
    (eq <=2=> (per_base_eq lib))
    -> (mkc_swap_per sw eq) <=2=> (per_base_eq lib).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      spcast; eauto 3 with slow;[].
  apply cequivc_swap_cs2_implies in h; auto.
Qed.

Lemma substc_mkcv_swap_cs {o} :
  forall sw v a (t : @CTerm o),
    substc t v (mkcv_swap_cs [v] sw a) = mkc_swap_cs sw (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc_mkcv_swap_cs : slow.

Lemma mkc_swap_per_approx_eq_bar {o} :
  forall sw lib (eq : per(o)) a b,
    (eq <=2=> (per_approx_eq_bar lib a b))
    -> (mkc_swap_per sw eq) <=2=> (per_approx_eq_bar lib (mkc_swap_cs sw a) (mkc_swap_cs sw b)).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold per_approx_eq in *; repnd.
  { allapply @mkc_swap_ccomputes_to_valc_ext_axiom_implies; dands; auto; spcast; eauto 3 with slow. }
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h1.
  autorewrite with slow in *.
  dands; auto; spcast.
  apply approxc_swap_cs2_implies in h; auto.
Qed.

Lemma mkc_swap_per_cequiv_eq_bar {o} :
  forall sw lib (eq : per(o)) a b,
    (eq <=2=> (per_cequiv_eq_bar lib a b))
    -> (mkc_swap_per sw eq) <=2=> (per_cequiv_eq_bar lib (mkc_swap_cs sw a) (mkc_swap_cs sw b)).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold per_cequiv_eq in *; repnd.
  { allapply @mkc_swap_ccomputes_to_valc_ext_axiom_implies; dands; auto; spcast; eauto 3 with slow. }
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h1.
  autorewrite with slow in *.
  dands; auto; spcast.
  apply cequivc_swap_cs2_implies in h; auto.
Qed.

Lemma swap_cs_computes_to_valc_inl_implies {o} :
  forall lib sw (t : @CTerm o) u,
    computes_to_valc lib (mkc_swap_cs sw t) (mkc_inl u)
    -> {z : CTerm
       & computes_to_valc lib t (mkc_inl z)
       # u = mkc_swap_cs sw z }.
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in comp; auto; exrepnd.
  inversion comp1; subst.
  destruct c; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
  destruct b; simpl in *.
  destruct l; simpl in *; unfold nobnd in *; ginv; fold_terms.
  applydup @computes_to_value_implies_isprogram in comp0 as isp.
  apply isprogram_inl_iff in isp.
  apply isprogram_eq in isp.
  exists (mk_ct n isp); dands; simpl; auto.
  apply cterm_eq; simpl; auto; autorewrite with slow; auto.
Qed.

Lemma swap_cs_computes_to_valc_inr_implies {o} :
  forall lib sw (t : @CTerm o) u,
    computes_to_valc lib (mkc_swap_cs sw t) (mkc_inr u)
    -> {z : CTerm
       & computes_to_valc lib t (mkc_inr z)
       # u = mkc_swap_cs sw z }.
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in comp; auto; exrepnd.
  inversion comp1; subst.
  destruct c; simpl in *; ginv.
  repeat (destruct bs; simpl in *; ginv).
  destruct b; simpl in *.
  destruct l; simpl in *; unfold nobnd in *; ginv; fold_terms.
  applydup @computes_to_value_implies_isprogram in comp0 as isp.
  apply isprogram_inr_iff in isp.
  apply isprogram_eq in isp.
  exists (mk_ct n isp); dands; simpl; auto.
  apply cterm_eq; simpl; auto; autorewrite with slow; auto.
Qed.

Lemma ccequivc_ext_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    ccequivc_ext lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> ccequivc_ext lib t1 t2.
Proof.
  introv h ext; apply h in ext; spcast.
  apply cequivc_swap_cs2_implies in ext; auto.
Qed.

Lemma cequiv_mk_swap_cs2_twice {o} :
  forall lib a b (t : @NTerm o),
    isprog t
    -> cequiv lib (mk_swap_cs2 a b (mk_swap_cs2 a b t)) t.
Proof.
  introv isp; split;
    try apply approx_mk_swap_cs2_twice; auto;
    try apply approx_mk_swap_cs2_twice_rev; auto.
Qed.

Lemma cequivc_mkc_swap_cs2_twice {o} :
  forall lib a b (t : @CTerm o),
    cequivc lib (mkc_swap_cs2 a b (mkc_swap_cs2 a b t)) t.
Proof.
  introv; destruct_cterms; unfold cequivc; simpl.
  apply cequiv_mk_swap_cs2_twice; auto.
Qed.

Lemma cequivc_mkc_swap_cs_twice {o} :
  forall lib sw (t : @CTerm o),
    cequivc lib (mkc_swap_cs sw (mkc_swap_cs sw t)) t.
Proof.
  introv; destruct sw as [a b]; apply cequivc_mkc_swap_cs2_twice.
Qed.

Lemma ccequivc_ext_mkc_swap_cs_twice {o} :
  forall lib sw (t : @CTerm o),
    ccequivc_ext lib (mkc_swap_cs sw (mkc_swap_cs sw t)) t.
Proof.
  introv ext; spcast; apply cequivc_mkc_swap_cs_twice.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_inl_implies {o} :
  forall sw lib (t : @CTerm o) k,
  (mkc_swap_cs sw t) ===>(lib) (mkc_inl k)
  -> t ===>(lib) (mkc_inl (mkc_swap_cs sw k)).
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  apply cequivc_mkc_inl_implies in ext0; exrepnd.
  apply computes_to_valc_isvalue_eq in ext0; eauto 3 with slow; subst.
  apply swap_cs_computes_to_valc_inl_implies in ext1; exrepnd; subst.
  exists (mkc_inl z); dands; spcast; eauto 3 with slow.
  apply implies_cequivc_inl.
  apply (implies_cequivc_swap_cs sw) in ext3.
  eapply cequivc_trans;[eauto|].
  apply cequivc_mkc_swap_cs_twice.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_inr_implies {o} :
  forall sw lib (t : @CTerm o) k,
  (mkc_swap_cs sw t) ===>(lib) (mkc_inr k)
  -> t ===>(lib) (mkc_inr (mkc_swap_cs sw k)).
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  apply cequivc_mkc_inr_implies in ext0; exrepnd.
  apply computes_to_valc_isvalue_eq in ext0; eauto 3 with slow; subst.
  apply swap_cs_computes_to_valc_inr_implies in ext1; exrepnd; subst.
  exists (mkc_inr z); dands; spcast; eauto 3 with slow.
  apply implies_cequivc_inr.
  apply (implies_cequivc_swap_cs sw) in ext3.
  eapply cequivc_trans;[eauto|].
  apply cequivc_mkc_swap_cs_twice.
Qed.

Lemma push_swap_cs_otermc_mkc_inl {o} :
  forall sw (k : @CTerm o),
    push_swap_cs_otermc sw (mkc_inl k) = mkc_inl (mkc_swap_cs sw k).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    unfold push_swap_cs_can; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_inl : slow.

Lemma push_swap_cs_otermc_mkc_inr {o} :
  forall sw (k : @CTerm o),
    push_swap_cs_otermc sw (mkc_inr k) = mkc_inr (mkc_swap_cs sw k).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto;
    unfold push_swap_cs_can; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_inr : slow.

Lemma push_swap_cs_otermc_mkc_qnat {o} :
  forall sw c,
    @push_swap_cs_otermc o sw (mkc_qnat c) = mkc_qnat c.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_qnat : slow.

Lemma push_swap_cs_otermc_mkc_csname {o} :
  forall sw n,
    @push_swap_cs_otermc o sw (mkc_csname n) = mkc_csname n.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_csname : slow.

Lemma ccomputes_to_valc_ext_inl_implies_mkc_swap_cs {o} :
  forall sw lib (t k : @CTerm o),
    t ===>(lib) (mkc_inl k)
    -> (mkc_swap_cs sw t) ===>(lib) (mkc_inl (mkc_swap_cs sw k)).
Proof.
  introv comp.
  apply (mkc_swap_ccomputes_to_valc_ext sw) in comp; autorewrite with slow in *; auto.
Qed.

Lemma ccomputes_to_valc_ext_inr_implies_mkc_swap_cs {o} :
  forall sw lib (t k : @CTerm o),
    t ===>(lib) (mkc_inr k)
    -> (mkc_swap_cs sw t) ===>(lib) (mkc_inr (mkc_swap_cs sw k)).
Proof.
  introv comp.
  apply (mkc_swap_ccomputes_to_valc_ext sw) in comp; autorewrite with slow in *; auto.
Qed.

Lemma mkc_swap_per_union_eq_bar {o} :
  forall sw lib (eq : per(o)) (eqa eqb : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => term_equality_respecting lib (eqa lib x))
    -> in_ext_ext lib (fun lib x => term_equality_respecting lib (eqb lib x))
    -> in_ext_ext lib (fun lib x => term_equality_transitive (eqa lib x))
    -> in_ext_ext lib (fun lib x => term_equality_transitive (eqb lib x))
    -> in_ext_ext lib (fun lib x => term_equality_symmetric (eqa lib x))
    -> in_ext_ext lib (fun lib x => term_equality_symmetric (eqb lib x))
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> (mkc_swap_per sw eq) <=2=> (per_union_eq_bar lib (mkc_swap_lib_per sw eqa) (mkc_swap_lib_per sw eqb)).
Proof.
  introv respa respb transa transb syma symb h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h;
      unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd.

  { left.
    apply mkc_swap_ccomputes_to_valc_ext_inl_implies in h0.
    apply mkc_swap_ccomputes_to_valc_ext_inl_implies in h2.
    eexists; eexists; dands; eauto; simpl.
    unfold mkc_swap_per.
    pose proof (respa _ e) as respa; simpl in respa.
    eapply transa;[apply syma;apply respa;[|apply ccequivc_ext_sym;apply ccequivc_ext_mkc_swap_cs_twice]|];
      [eapply transa;eauto;apply syma;auto|].
    eapply transa;[|apply respa;[|apply ccequivc_ext_sym;apply ccequivc_ext_mkc_swap_cs_twice] ];auto.
    eapply transa;[|eauto]; apply syma; auto. }

  { right.
    apply mkc_swap_ccomputes_to_valc_ext_inr_implies in h0.
    apply mkc_swap_ccomputes_to_valc_ext_inr_implies in h2.
    eexists; eexists; dands; eauto; simpl.
    unfold mkc_swap_per.
    pose proof (respb _ e) as respb; simpl in respb.
    eapply transb;[apply symb;apply respb;[|apply ccequivc_ext_sym;apply ccequivc_ext_mkc_swap_cs_twice]|];
      [eapply transb;eauto;apply symb;auto|].
    eapply transb;[|apply respb;[|apply ccequivc_ext_sym;apply ccequivc_ext_mkc_swap_cs_twice] ];auto.
    eapply transb;[|eauto]; apply symb; auto. }

  { left.
    apply (ccomputes_to_valc_ext_inl_implies_mkc_swap_cs sw) in h0.
    apply (ccomputes_to_valc_ext_inl_implies_mkc_swap_cs sw) in h2.
    eexists; eexists; dands; eauto; simpl. }

  { right.
    apply (ccomputes_to_valc_ext_inr_implies_mkc_swap_cs sw) in h0.
    apply (ccomputes_to_valc_ext_inr_implies_mkc_swap_cs sw) in h2.
    eexists; eexists; dands; eauto; simpl. }
Qed.

Lemma in_ext_ext_tysys_implies_in_ext_ext_term_equality_respecting {o} :
  forall uk lib ts (eqa : lib-per(lib,o)) A B,
    type_system ts
    -> in_ext_ext lib (fun lib' x => ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv tysys h; introv.
  pose proof (h _ e) as h; simpl in h.
  unfold type_system in *; repnd; eauto.
Qed.
Hint Resolve in_ext_ext_tysys_implies_in_ext_ext_term_equality_respecting : slow.

Lemma in_ext_ext_tysys_implies_in_ext_ext_term_equality_transitive {o} :
  forall uk lib ts (eqa : lib-per(lib,o)) A B,
    type_system ts
    -> in_ext_ext lib (fun lib' x => ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv tysys h; introv.
  pose proof (h _ e) as h; simpl in h.
  unfold type_system in *; repnd; eauto.
Qed.
Hint Resolve in_ext_ext_tysys_implies_in_ext_ext_term_equality_transitive : slow.

Lemma in_ext_ext_tysys_implies_in_ext_ext_term_equality_symmetric {o} :
  forall uk lib ts (eqa : lib-per(lib,o)) A B,
    type_system ts
    -> in_ext_ext lib (fun lib' x => ts uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv tysys h; introv.
  pose proof (h _ e) as h; simpl in h.
  unfold type_system in *; repnd; eauto.
Qed.
Hint Resolve in_ext_ext_tysys_implies_in_ext_ext_term_equality_symmetric : slow.

Lemma cequiv_choice_seq {o} :
  forall lib (t t' : @NTerm o) n,
    computes_to_value lib t (mk_choice_seq n)
    -> cequiv lib t t'
    -> computes_to_value lib t' (mk_choice_seq n).
Proof.
  sp.
  apply @cequiv_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_choice_seq_implies {o} :
  forall sw lib (t : @CTerm o) name,
  (mkc_swap_cs sw t) ===>(lib) (mkc_choice_seq name)
  -> t ===>(lib) (mkc_choice_seq (swap_cs sw name)).
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  destruct_cterms; unfold computes_to_valc, cequivc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in ext1; auto; exrepnd; subst.
  eapply cequiv_choice_seq in ext0; eauto 3 with slow.
  apply computes_to_value_if_iscan in ext0; eauto 3 with slow; subst.
  inversion ext0; clear ext0; subst; simpl in *.
  destruct bs; simpl in *; ginv.
  destruct c; simpl in *; ginv.
  destruct sw as [a b]; simpl in *.
  boolvar; subst; tcsp; GC.
  { exists (@mkc_choice_seq o a); dands; spcast; tcsp; eauto 3 with slow. }
  { exists (@mkc_choice_seq o b); dands; spcast; tcsp; eauto 3 with slow. }
  { exists (@mkc_choice_seq o a); dands; spcast; tcsp; eauto 3 with slow. }
  { exists (@mkc_choice_seq o c); dands; spcast; tcsp; eauto 3 with slow. }
Qed.

Lemma push_swap_cs_otermc_mkc_choice_seq {o} :
  forall sw n,
    @push_swap_cs_otermc o sw (mkc_choice_seq n) = mkc_choice_seq (swap_cs sw n).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
  destruct sw as [a b]; simpl.
  unfold push_swap_cs_can; simpl; boolvar; tcsp.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_choice_seq : slow.

Lemma mkc_swap_equality_of_csname_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) n,
    (eq <=2=> (equality_of_csname_bar lib n))
    -> (mkc_swap_per sw eq) <=2=> (equality_of_csname_bar lib n).
Proof.
  introv sane h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_pres; eauto; clear h; introv ext h;
      unfold equality_of_csname in *; exrepnd.

  { apply mkc_swap_ccomputes_to_valc_ext_choice_seq_implies in h2.
    apply mkc_swap_ccomputes_to_valc_ext_choice_seq_implies in h0.
    exists (swap_cs sw name); dands; auto; eauto 3 with slow.
    apply sane_swapping_implies_compatible_choice_sequence_name; auto. }

  { apply (mkc_swap_ccomputes_to_valc_ext sw) in h2.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
    autorewrite with slow in *.
    eexists; dands; try exact h2; auto; eauto 3 with slow.
    apply sane_swapping_implies_compatible_choice_sequence_name; auto. }
Qed.

Lemma substc_ccequivc_ext_bar {o} :
  forall lib (a b : @CTerm o) x t,
    ccequivc_ext_bar lib a b
    -> ccequivc_ext_bar lib (substc a x t) (substc b x t).
Proof.
  introv h; eapply in_open_bar_pres; eauto; clear h; introv h q.
  apply substc_ccequivc_ext; auto.
Qed.
Hint Resolve substc_ccequivc_ext_bar : slow.

Lemma ccequivc_ext_bar_trans {o} lib (a b c : @CTerm o) :
  ccequivc_ext_bar lib a b
  -> ccequivc_ext_bar lib b c
  -> ccequivc_ext_bar lib a c.
Proof.
  introv ceq1 ceq2.
  eapply in_open_bar_comb; try exact ceq1; clear ceq1.
  eapply in_open_bar_pres; try exact ceq2; clear ceq2.
  introv ext ceq1 ceq2.
  eapply ccequivc_ext_trans; eauto.
Qed.
Hint Resolve ccequivc_ext_bar_trans : slow.

Lemma ccequivc_ext_bar_sym {o} lib (a b : @CTerm o) :
  ccequivc_ext_bar lib a b
  -> ccequivc_ext_bar lib b a.
Proof.
  introv ceq.
  eapply in_open_bar_pres; try exact ceq; clear ceq.
  introv ext ceq.
  apply ccequivc_ext_sym; auto.
Qed.
Hint Resolve ccequivc_ext_bar_sym : slow.

Lemma ccequivc_ext_bar_mkc_swap_cs_twice {o} :
  forall lib sw (t : @CTerm o),
    ccequivc_ext_bar lib (mkc_swap_cs sw (mkc_swap_cs sw t)) t.
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext.
  apply ccequivc_ext_mkc_swap_cs_twice.
Qed.
Hint Resolve ccequivc_ext_bar_mkc_swap_cs_twice : slow.

Lemma implies_ccequivc_ext_bar_mkc_swap {o} :
  forall sw lib (a b : @CTerm o),
    ccequivc_ext_bar lib a b
    -> ccequivc_ext_bar lib (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv ceq.
  eapply in_open_bar_pres; eauto; clear ceq; introv ext ceq xt.
  apply ceq in xt; spcast.
  destruct sw as [n m]; simpl in *.
  apply implies_cequivc_swap_cs2; auto.
Qed.
Hint Resolve implies_ccequivc_ext_bar_mkc_swap : slow.

Lemma mkc_swap_cs_list_snoc {o} :
  forall sws sw (t : @CTerm o),
    mkc_swap_cs_list (snoc sws sw) t
    = mkc_swap_cs_list sws (mkc_swap_cs sw t).
Proof.
  induction sws; introv; simpl; auto; try congruence.
Qed.
Hint Rewrite @mkc_swap_cs_list_snoc : slow.

Lemma implies_ccequivc_ext_bar_mkc_swap_list {o} :
  forall sws lib (a b : @CTerm o),
    ccequivc_ext_bar lib a b
    -> ccequivc_ext_bar lib (mkc_swap_cs_list sws a) (mkc_swap_cs_list sws b).
Proof.
  induction sws; introv ceq; simpl; auto.
  apply implies_ccequivc_ext_bar_mkc_swap; auto.
Qed.
Hint Resolve implies_ccequivc_ext_bar_mkc_swap_list : slow.

Lemma implies_is_swap_invariant_mkc_swap {o} :
  forall sw {lib} (eqa : lib-per(lib,o)) v B,
    is_swap_invariant eqa v B
    -> is_swap_invariant (mkc_swap_lib_per sw eqa) v (mkcv_swap_cs _ sw B).
Proof.
  introv isw h; simpl in *; autorewrite with slow.
  apply implies_ccequivc_ext_bar_mkc_swap.
  unfold mkc_swap_per in *.

  pose proof (isw _ [sw] _ e h) as iswa; simpl in *.
  eapply ccequivc_ext_bar_trans in iswa;
    [|apply substc_ccequivc_ext_bar;
      apply ccequivc_ext_bar_sym; auto;
      apply ccequivc_ext_bar_mkc_swap_cs_twice].

  pose proof (isw _ (snoc sws sw) _ e h) as iswb; simpl in *.
  autorewrite with slow in *.
  eapply ccequivc_ext_bar_trans;[|apply ccequivc_ext_bar_sym;exact iswa].
  eapply ccequivc_ext_bar_trans;[|exact iswb].
  apply substc_ccequivc_ext_bar.
  apply implies_ccequivc_ext_bar_mkc_swap_list.
  apply ccequivc_ext_bar_sym; apply ccequivc_ext_bar_mkc_swap_cs_twice.
Qed.
Hint Resolve implies_is_swap_invariant_mkc_swap : slow.


Lemma type_system_term_mem1 {p} :
 forall (ts : cts(p)) uk lib (T T' t1 t2 : CTerm) (eq : per),
   type_system ts
   -> ts uk lib T T' eq
   -> eq t1 t2
   -> eq t1 t1.
Proof.
  introv h q e.
  eapply type_system_term_mem; eauto; unfold type_system in *; tcsp.
Qed.

Lemma type_system_term_mem2 {p} :
 forall (ts : cts(p)) uk lib (T T' t1 t2 : CTerm) (eq : per),
   type_system ts
   -> ts uk lib T T' eq
   -> eq t1 t2
   -> eq t2 t2.
Proof.
  introv h q e.
  unfold type_system in *; repnd.
  assert (eq t2 t1) as z;[|eapply type_system_term_mem; eauto];[].
  match goal with
  | [ H : context[term_symmetric] |- _ ] => eapply H; eauto
  end.
Qed.

Lemma close_type_value_respecting_left_bar {o} :
  forall (ts : cts(o)) uk lib a b c eq,
    local_ts ts
    -> ts_implies_per_bar ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccequivc_ext_bar lib a c
    -> close ts uk lib a b eq
    -> close ts uk lib c b eq.
Proof.
  introv loc imp tysys dou mon ceq cl.
  apply close_implies_per_bar in cl; auto.
  apply CL_bar.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb;[|exact cl1]; clear cl1.
  eapply in_open_bar_ext_comb2;[|exact ceq]; clear ceq.
  apply in_ext_ext_implies_in_open_bar_ext; introv ceq h.
  eapply close_type_value_respecting_left; eauto.
Qed.


Lemma close_type_value_respecting_right_bar {o} :
  forall (ts : cts(o)) uk lib a b c eq,
    local_ts ts
    -> ts_implies_per_bar ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccequivc_ext_bar lib a c
    -> close ts uk lib b a eq
    -> close ts uk lib b c eq.
Proof.
  introv loc imp tysys dou mon ceq cl.
  apply close_implies_per_bar in cl; auto.
  apply CL_bar.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb;[|exact cl1]; clear cl1.
  eapply in_open_bar_ext_comb2;[|exact ceq]; clear ceq.
  apply in_ext_ext_implies_in_open_bar_ext; introv ceq h.
  eapply close_type_value_respecting_right; eauto.
Qed.

Lemma lsubst_aux_lsubst_aux_sw_sub_closed {o} :
  forall a b (t : @NTerm o) v u,
    closed u
    -> lsubst_aux (lsubst_aux t (sw_sub a b [v])) [(v, u)]
       = lsubst_aux t [(v, mk_swap_cs2 a b u)].
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cl; simpl.

  { repeat (boolvar; simpl; tcsp). }

  f_equal.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  boolvar; simpl; autorewrite with slow; auto.
  eapply ind; eauto.
Qed.

Lemma substc_push_swap_cs_sub_cvterm {o} :
  forall sw v (B : @CVTerm o [v]) a,
    substc a v (push_swap_cs_sub_cvterm [v] sw B)
    = substc (mkc_swap_cs sw a) v B.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  unfold push_swap_cs_sub_term.
  repeat unfsubst; eauto 4 with slow;[].
  rewrite lsubst_aux_lsubst_aux_sw_sub_closed; eauto 2 with slow.
Qed.
Hint Rewrite @substc_push_swap_cs_sub_cvterm : slow.

Lemma swap_cs_can_rev {o} :
  forall a b (c : @CanonicalOp o),
    swap_cs_can (a,b) c = swap_cs_can (b,a) c.
Proof.
  introv; destruct c; simpl; auto; boolvar; subst; auto.
Qed.

Lemma isprogram_push_swap_cs_can_implies {o} :
  forall (c1 c2 : choice_sequence_name) (can : @CanonicalOp o) (bs : list BTerm),
    isprogram (push_swap_cs_can c1 c2 can bs)
    -> isprogram (oterm (Can can) bs).
Proof.
  introv isp.
  unfold push_swap_cs_can in *.
  allrw @isprogram_ot_iff; simpl in *; repnd; autorewrite with slow in *.
  dands; auto.
  introv i.
  pose proof (isp (push_swap_cs_bterm c1 c2 bt)) as isp; autodimp isp hyp.
  { apply in_map_iff; eexists; dands; eauto. }
  destruct bt as [l t].
  unfold isprogram_bt, closed_bt in *; simpl in *; autorewrite with slow in *.
  repnd; dands; auto.
  allrw @bt_wf_iff.
  apply nt_wf_mk_swap_cs2_implies in isp.
  apply nt_wf_push_swap_cs_sub_term_implies in isp; auto.
Qed.


(* Experimenting with a version of [approx] that directly uses [cl_olift] *)
Definition NLrel {o} := @NTerm o -> @NTerm o -> list NVar -> Type.

Definition cl_blift {p} (R: NLrel) (bt1 bt2: BTerm): [univ] :=
  {lv : list NVar
  & {nt1,nt2 : @NTerm p
  $ R nt1 nt2 lv
  # alpha_eq_bterm bt1 (bterm lv nt1)
  # alpha_eq_bterm bt2 (bterm lv nt2) }}.

Definition cl_lblift {p} (R: NLrel) (tls trs: list (@BTerm p)): [univ] :=
  length tls = length trs
  # forall n : nat,  n < length tls -> cl_blift R (tls{[n]}) (trs{[n]}).

Definition cl_close_compute_val {p} lib (R: NTrel) (tl tr : NTerm) : [univ]:=
  forall (c : CanonicalOp) (tl_subterms : list BTerm),
    (tl =v>(lib) (oterm (Can c) tl_subterms))
    -> {tr_subterms : list (@BTerm p)
        & (tr =v>(lib) (oterm (Can c) tr_subterms))
        # cl_lblift (cl_olift R) tl_subterms tr_subterms }.

Definition cl_close_comput {p} lib (R: NTrel) (tl tr : @NTerm p) : [univ]:=
  isprogram tl
  # isprogram tr
  # cl_close_compute_val lib R tl tr
  # close_compute_exc lib R tl tr
  # True (*close_compute_mrk lib R tl tr*).

CoInductive cl_approx {o} (lib : @plibrary o) : @NTerm o -> @NTerm o -> Type :=
| cl_approx_C:
    forall tl tr,
      cl_close_comput lib (cl_approx lib) tl tr
      -> cl_approx lib tl tr.

Inductive cl_approx_sub {p} (lib : @plibrary p) : @Sub p -> @Sub p -> Type :=
  | cl_apr_sub_nil : cl_approx_sub lib [] []
  | cl_apr_sub_cons :
      forall v t1 t2 s1 s2,
        cl_approx lib t1 t2
        -> cl_approx_sub lib s1 s2
        -> cl_approx_sub lib ((v,t1) :: s1) ((v,t2) :: s2).
Hint Constructors cl_approx_sub.

Lemma implies_cl_approx_sub_combine {o} :
  forall lib l (ts1 ts2 : list (@NTerm o)),
    length l = length ts1
    -> length l = length ts2
    -> (forall t1 t2, LIn (t1,t2) (combine ts1 ts2) -> cl_approx lib t1 t2)
    -> cl_approx_sub lib (combine l ts1) (combine l ts2).
Proof.
  induction l; introv lena lenb imp; simpl in *; cpx.
  destruct ts1, ts2; simpl in *; cpx.
Qed.

Lemma cl_approx_trans {p} :
  forall lib (a b c : @NTerm p),
    cl_approx lib a b
    -> cl_approx lib b c
    -> cl_approx lib a c.
Proof.
Abort.

Lemma cl_approx_implies_approx {p} :
  forall lib (a b : @NTerm p),
    cl_approx lib a b -> approx lib a b.
Proof.
Abort.

Lemma approx_implies_cl_approx {p} :
  forall lib (a b : @NTerm p),
    approx lib a b -> cl_approx lib a b.
Proof.
Abort.

Lemma cl_approx_sub_as_approx_sub {o} :
  forall lib (s1 s2 : @Sub o),
    cl_approx_sub lib s1 s2 <=> approx_sub lib s1 s2.
Proof.
Abort.

Lemma implies_cl_approx_swap_cs2 {o} :
  forall n1 n2 lib (a b : @NTerm o),
    cl_approx lib a b
    -> cl_approx lib (mk_swap_cs2 n1 n2 a) (mk_swap_cs2 n1 n2 b).
Proof.
Abort.

Lemma lsubst_cl_approx_congr_sp {o} :
  forall lib (t : @NTerm o) (sub1 sub2 : Sub),
    cl_approx_sub lib sub1 sub2
    -> isprogram (lsubst t sub2)
    -> cl_approx lib (lsubst t sub1) (lsubst t sub2).
Proof.
Abort.

Definition force_cl_match {o} {lib} {t1 t2 : @NTerm o} (a : cl_approx lib t1 t2) : cl_approx lib t1 t2 :=
  match a with
  | cl_approx_C _ u v c => cl_approx_C _ u v c
  end.

Lemma swap_mk_swap_cs2 {o} :
  forall lib n1 n2 (t : @NTerm o),
    isprogram t
    -> cl_approx
         lib
         (mk_swap_cs2 n1 n2 t)
         (mk_swap_cs2 n2 n1 t).
Proof.
  cofix ind; introv isp.
  constructor.
  unfold cl_close_comput; dands; eauto 2 with slow;[|].

  { introv comp.
    apply swap_cs2_computes_to_value_implies in comp; eauto 2 with slow; exrepnd.
    apply (computes_to_value_can_implies_swap_cs2 n2 n1) in comp0.

    applydup @computes_to_value_implies_isprogram in comp0 as wf.
    apply isprogram_push_swap_cs_can_implies in wf.

    unfold push_swap_cs_can in *; ginv.
    rewrite swap_cs_can_rev in comp0.
    eexists; dands; eauto.
    unfold cl_lblift; autorewrite with slow; dands; auto.
    introv len; autorewrite with slow.
    unfold push_swap_cs_bterms.
    repeat (rewrite selectbt_map; autorewrite with slow; auto).

    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (change_bvars_alpha_norep_bterm (bs {[n]}) []) as ha; destruct ha as [b1 ha]; repnd.
    destruct b1 as [l u]; simpl in *.
    apply no_repeats_app in ha; repnd.
    eapply alpha_eq_bterm_preserves_isprogram_bt in wf; eauto.
    eapply respect_eauto_albt in wf0; eauto.
    apply bt_wf_iff in wf0.
    applydup (@implies_alpha_eq_bterm_push_swap_cs_bterm o n1 n2) in ha1; simpl in *.
    applydup (@implies_alpha_eq_bterm_push_swap_cs_bterm o n2 n1) in ha1; simpl in *.

    exists l
           (mk_swap_cs2 n1 n2 (push_swap_cs_sub_term n1 n2 l u))
           (mk_swap_cs2 n2 n1 (push_swap_cs_sub_term n2 n1 l u)).
    dands; auto.

    assert (subset (free_vars u) l) as ssa by eauto 2 with slow.

    unfold cl_olift; dands; eauto 4 with slow;[].

    introv ln ps.
    repeat rewrite lsust_mk_swap_cs2_eq.
    unfold push_swap_cs_sub_term.
    repeat (rewrite lsubst_sw_sub_lsust_aux_combine_eq; autorewrite with slow; eauto 2 with slow;[]).

    (* XXXXXXXXXXX *)
(*
    eapply cl_approx_trans.

    { apply ind.
      apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow. }

    apply implies_cl_approx_swap_cs2.
    apply lsubst_cl_approx_congr_sp.

    { apply implies_cl_approx_sub_combine; autorewrite with slow; auto.
      introv j; rewrite <- map_combine_left in j; apply in_map_iff in j; exrepnd; ginv.
      rewrite combine_map_l in j1; apply in_map_iff in j1; exrepnd; inversion j0; subst.
      apply ind; auto. }

    apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow.
*)
    (* XXXXXXXXXXX *)

    pose proof (ind lib n1 n2 (lsubst u (sw_sub_ts n1 n2 l ts))) as aps1.
    repeat (autodimp aps1 hyp); eauto 2 with slow;[|].
    { apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow. }

(*    inversion aps1; subst; clear aps1.
    assert (cl_approx lib (mk_swap_cs2 n1 n2 (lsubst u (sw_sub_ts n1 n2 l ts))) (mk_swap_cs2 n2 n1 (lsubst u (sw_sub_ts n1 n2 l ts)))) as aps1.
    { constructor; auto. }*)

    assert (forall (ts : list NTerm),
               length l = length ts
               -> areprograms ts
               -> cl_approx_sub lib (sw_sub_ts n1 n2 l ts) (sw_sub_ts n2 n1 l ts)) as aps2.
    { introv len' aps'.
      apply implies_cl_approx_sub_combine; autorewrite with slow; auto.
      introv j; rewrite <- map_combine_left in j; apply in_map_iff in j; exrepnd; ginv.
      rewrite combine_map_l in j1; apply in_map_iff in j1; exrepnd; inversion j0; subst.
      apply ind; auto. }

    clear ind.

(*
    apply approx_implies_cl_approx.
    apply cl_approx_implies_approx in aps1.

    eapply approx_trans;[exact aps1|].
    apply implies_approx_swap_cs2.
    apply lsubst_approx_congr2; eauto 2 with slow;
      try (apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow);[].

    apply cl_approx_sub_as_approx_sub.
    apply aps2; auto. }

  { (* EXC case *)

    clear ind.
    introv comp.
    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc n2 n1) in comp.
    eexists; eexists; dands; eauto; apply approx_implies_cl_approx; apply approx_refl; auto. }
*)
Abort.

Lemma isprog_vars_implies_isprogram_lsubst_sw_sub_ts {o} :
  forall n1 n2 (t : @NTerm o) vs ts,
    areprograms ts
    -> isprog_vars vs t
    -> length vs = length ts
    -> isprogram (lsubst t (sw_sub_ts n1 n2 vs ts)).
Proof.
  introv aps isp len.
  apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
  rewrite dom_sub_sw_sub_ts; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_implies_isprogram_lsubst_sw_sub_ts : slow.

Lemma isprog_vars_implies_isprog_lsubst_sw_sub_ts {o} :
  forall n1 n2 (t : @NTerm o) vs ts,
    areprograms ts
    -> isprog_vars vs t
    -> length vs = length ts
    -> isprog (lsubst t (sw_sub_ts n1 n2 vs ts)).
Proof.
  introv aps isp len; apply isprog_eq; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_implies_isprog_lsubst_sw_sub_ts : slow.

Lemma isprog_vars_implies_isprogram_mk_swap_cs2_lsubst_sw_sub_ts {o} :
  forall n1 n2 (t : @NTerm o) vs ts,
    areprograms ts
    -> isprog_vars vs t
    -> length vs = length ts
    -> isprogram (mk_swap_cs2 n1 n2 (lsubst t (sw_sub_ts n1 n2 vs ts))).
Proof.
  introv aps isp len.
  eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_implies_isprogram_mk_swap_cs2_lsubst_sw_sub_ts : slow.

Inductive diff_swaps {o} a b : @NTerm o -> @NTerm o -> Type :=
| dswap_v : forall v, diff_swaps a b (vterm v) (vterm v)
| dswap_same :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
      -> diff_swaps a b (oterm op bs1) (oterm op bs2)
| dswap_diff :
    forall t u,
      diff_swaps a b t u
      -> diff_swaps a b (mk_swap_cs2 a b t) (mk_swap_cs2 b a u)
with diff_swaps_bterm {o} a b : @BTerm o -> @BTerm o -> Type :=
| dswap_bterm :
    forall l t u,
      diff_swaps a b t u
      -> diff_swaps_bterm a b (bterm l t) (bterm l u).
Hint Constructors diff_swaps.
Hint Constructors diff_swaps_bterm.

Lemma diff_swaps_refl {o} :
  forall a b (t : @NTerm o),
    diff_swaps a b t t.
Proof.
  nterm_ind t as [v|op bs ind] Case; auto.
  apply dswap_same; auto.
  introv i.
  apply in_combine_same in i; repnd; subst.
  destruct b2; constructor; eapply ind; eauto.
Qed.
Hint Resolve diff_swaps_refl : slow.

Lemma or_diff_swaps_bterm_implies {o} :
  forall a b (x y : @BTerm o) F,
    (forall b1 b2, (x, y) = (b1, b2) [+] (F b1 b2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps_bterm a b x y # (forall b1 b2, F b1 b2 -> diff_swaps_bterm a b b1 b2).
Proof.
  introv h; dands.
  { apply h; auto. }
  { introv q; apply h; auto. }
Qed.

Ltac inv_diff_term h :=
  let len := fresh "len" in
  let imp := fresh "imp" in
  let dif := fresh "diff" in
  inversion h as [|? ? ? len imp|? ? dif]; subst; clear h.

Ltac inv_diff_bterm h :=
  let dif := fresh "diff" in
  inversion h as [? ? ? dif]; subst; clear h.

Ltac inv_diff_bterms :=
  match goal with
  | [ H : (forall b1 b2, (_ [+] _) -> diff_swaps_bterm _ _ _ _) |- _ ] => apply or_diff_swaps_bterm_implies in H; repnd
  | [ H : (forall b1 b2, False -> diff_swaps_bterm _ _ _ _) |- _ ] => clear H
  | [ H : diff_swaps_bterm _ _ _ _ |- _ ] => inv_diff_bterm H
  end.

Tactic Notation "inv_diff" ident(h) := inv_diff_term h; simpl in *; cpxpp; simpl in *; repeat inv_diff_bterms.

Tactic Notation "inv_diff" :=
  match goal with
  | [ H : diff_swaps _ _ (_ _) _ |- _ ] => inv_diff_term H; simpl in *; cpxpp; simpl in *; repeat inv_diff_bterms
  | [ H : diff_swaps _ _ _ (_ _) |- _ ] => inv_diff_term H; simpl in *; cpxpp; simpl in *; repeat inv_diff_bterms
  | [ H : diff_swaps _ _ (_ _) _ |- _ ] => inv_diff_term H; simpl in *
  | [ H : diff_swaps _ _ _ (_ _) |- _ ] => inv_diff_term H; simpl in *
  end.

Inductive diff_swaps_sub {o} a b : @Sub o -> @Sub o -> Type :=
| dswaps_sub_nil : diff_swaps_sub a b [] []
| dswaps_sub_cons :
    forall (v : NVar) (t1 t2 : NTerm) (s1 s2 : Sub),
      diff_swaps a b t1 t2
      -> diff_swaps_sub a b s1 s2
      -> diff_swaps_sub a b ((v, t1) :: s1) ((v, t2) :: s2).
Hint Constructors diff_swaps_sub.

Lemma sub_find_diff_swaps_if_some {o} :
  forall a b (s1 s2 : @Sub o) v t,
    diff_swaps_sub a b s1 s2
    -> sub_find s1 v = Some t
    -> {u : NTerm & sub_find s2 v = Some u # diff_swaps a b t u}.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
Qed.

Lemma sub_find_diff_swaps_if_none {o} :
  forall a b (s1 s2 : @Sub o) v,
    diff_swaps_sub a b s1 s2
    -> sub_find s1 v = None
    -> sub_find s2 v = None.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
Qed.

Lemma implies_diff_swaps_sub_filter {o} :
  forall a b (s1 s2 : @Sub o) l,
    diff_swaps_sub a b s1 s2
    -> diff_swaps_sub a b (sub_filter s1 l) (sub_filter s2 l).
Proof.
  introv d; induction d; simpl in *; boolvar; eauto.
Qed.
Hint Resolve implies_diff_swaps_sub_filter : slow.

Lemma diff_swaps_sub_refl {o} :
  forall a b (s : @Sub o),
    diff_swaps_sub a b s s.
Proof.
  induction s; introv; simpl; repnd; constructor; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_sub_refl : slow.

Lemma implies_diff_swaps_lsubst_aux {o} :
  forall a b (t u : @NTerm o) (s1 s2 : @Sub o),
    diff_swaps a b t u
    -> diff_swaps_sub a b s1 s2
    -> diff_swaps a b (lsubst_aux t s1) (lsubst_aux u s2).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv h q; simpl in *.

  { inv_diff.
    remember (sub_find s1 v) as sfa; symmetry in Heqsfa; destruct sfa.
    { eapply sub_find_diff_swaps_if_some in q; eauto; exrepnd; allrw; auto. }
    eapply sub_find_diff_swaps_if_none in q; eauto; allrw; auto. }

  inv_diff.

  { constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    destruct a1,a0; simpl in *.
    inv_diff_bterm i0; constructor.
    applydup in_combine in i1; repnd.
    eapply ind; eauto; eauto 3 with slow. }

  constructor; autorewrite with slow.
  eapply ind; eauto; left; try reflexivity.
Qed.
Hint Resolve implies_diff_swaps_lsubst_aux : slow.

Lemma implies_diff_swaps_push_swap_cs_can {o} :
  forall a b n m c (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps
         a b
         (push_swap_cs_can n m c bs1)
         (push_swap_cs_can n m c bs2).
Proof.
  introv len imp.
  unfold push_swap_cs_can; constructor; autorewrite with slow; auto.
  introv i.
  unfold push_swap_cs_bterms in i.
  rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply imp in i1.
  destruct a1, a0; inv_diff_bterm i1; simpl.
  constructor; simpl; auto.
  repeat (constructor; simpl; auto; introv xx; repndors; subst; ginv; tcsp; constructor; auto).
  unfold push_swap_cs_sub_term; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_push_swap_cs_can : slow.

Lemma diff_swaps_sub_sw_sub_rev {o} :
  forall a b l,
    @diff_swaps_sub o a b (sw_sub a b l) (sw_sub b a l).
Proof.
  unfold sw_sub; induction l; simpl; auto.
Qed.
Hint Resolve diff_swaps_sub_sw_sub_rev : slow.

Lemma implies_diff_swaps_push_swap_cs_can_rev {o} :
  forall a b c (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps
         a b
         (push_swap_cs_can a b c bs1)
         (push_swap_cs_can b a c bs2).
Proof.
  introv len imp.
  unfold push_swap_cs_can.
  rewrite swap_cs_can_rev.
  constructor; autorewrite with slow; auto.
  introv i.
  unfold push_swap_cs_bterms in i.
  rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply imp in i1.
  destruct a1, a0; inv_diff_bterm i1; simpl.
  constructor; simpl; auto.
  repeat (constructor; simpl; auto; introv xx; repndors; subst; ginv; tcsp; constructor; auto).
  unfold push_swap_cs_sub_term; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_push_swap_cs_can_rev : slow.

Lemma diff_swaps_preserves_iscan {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> iscan t
    -> iscan u.
Proof.
  introv h q.
  inv_diff h.
Qed.
Hint Resolve diff_swaps_preserves_iscan : slow.

Lemma diff_swaps_preserves_isexc {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isexc t
    -> isexc u.
Proof.
  introv h q.
  inv_diff h.
Qed.
Hint Resolve diff_swaps_preserves_isexc : slow.

Lemma diff_swaps_preserves_isnoncan {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isnoncan t
    -> isnoncan u.
Proof.
  introv h q.
  inv_diff h.
Qed.
Hint Resolve diff_swaps_preserves_isnoncan : slow.

Lemma diff_swaps_preserves_isabs {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isabs t
    -> isabs u.
Proof.
  introv h q.
  inv_diff h.
Qed.
Hint Resolve diff_swaps_preserves_isabs : slow.

Lemma diff_swaps_preserves_isvalue_like {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isvalue_like t
    -> isvalue_like u.
Proof.
  introv h q; unfold isvalue_like in *; repndors; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_preserves_isvalue_like : slow.

Lemma diff_swaps_preserves_isnoncan_like {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isnoncan_like t
    -> isnoncan_like u.
Proof.
  introv h q; unfold isnoncan_like in *; repndors; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_preserves_isnoncan_like : slow.

Lemma diff_swaps_implies_same_free_vars {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> free_vars t = free_vars u.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; inv_diff; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_diff_bterm i0; simpl.
  f_equal.
  apply in_combine in i; repnd.
  eapply ind; eauto.
Qed.
Hint Resolve diff_swaps_implies_same_free_vars : slow.

Lemma diff_swaps_implies_same_maybe_new_var {o} :
  forall a b (t u : @NTerm o) l k,
    diff_swaps a b t u
    -> maybe_new_var l k t = maybe_new_var l k u.
Proof.
  introv d; unfold maybe_new_var, newvar.
  erewrite diff_swaps_implies_same_free_vars; eauto.
Qed.

Lemma implies_diff_swaps_pushdown_fresh {o} :
  forall a b (t u : @NTerm o) l,
    diff_swaps a b t u
    -> diff_swaps a b (pushdown_fresh l t) (pushdown_fresh l u).
Proof.
  introv d.
  inv_diff d; simpl; eauto 3 with slow.

  { constructor; autorewrite with slow; auto.
    introv i.
    unfold mk_fresh_bterms in i.
    rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    inv_diff_bterm i0.
    unfold mk_fresh_bterm; simpl; constructor.
    constructor; simpl; auto; introv i; repndors; ginv; tcsp.
    erewrite diff_swaps_implies_same_maybe_new_var; eauto. }

  constructor.
  constructor; simpl; auto; introv i; repndors; ginv; tcsp.
Qed.
Hint Resolve implies_diff_swaps_pushdown_fresh : slow.

Lemma implies_diff_swaps_sub_cons {o} :
  forall a b v t u (s1 s2 : @Sub o),
    diff_swaps a b t u
    -> diff_swaps_sub a b s1 s2
    -> diff_swaps_sub a b ((v,t) :: s1) ((v,u) :: s2).
Proof.
  introv; auto.
Qed.
Hint Resolve implies_diff_swaps_sub_cons : slow.

Lemma diff_swaps_implies_same_get_utokens {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> get_utokens t = get_utokens u.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; inv_diff; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).
  f_equal.
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_diff_bterm i0; simpl.
  apply in_combine in i; repnd.
  eapply ind; eauto.
Qed.
Hint Resolve diff_swaps_implies_same_get_utokens : slow.

Lemma diff_swaps_implies_same_get_fresh_atom {o} :
  forall a b lib (t u : @NTerm o),
    diff_swaps a b t u
    -> get_fresh_atom lib t = get_fresh_atom lib u.
Proof.
  introv d.
  apply diff_swaps_implies_same_get_utokens in d.
  unfold get_fresh_atom, get_utokens_lib.
  allrw; auto.
Qed.
Hint Resolve diff_swaps_implies_same_get_fresh_atom : slow.

Lemma diff_swaps_implies_diff_swaps_mk_utoken_get_fresh_atom {o} :
  forall a b lib (t u : @NTerm o),
    diff_swaps a b t u
    -> diff_swaps a b (mk_utoken (get_fresh_atom lib t)) (mk_utoken (get_fresh_atom lib u)).
Proof.
  introv d; erewrite diff_swaps_implies_same_get_fresh_atom; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_implies_diff_swaps_mk_utoken_get_fresh_atom : slow.

Lemma implies_diff_swaps_mk_fresh {o} :
  forall a b v (t u : @NTerm o),
    diff_swaps a b t u
    -> diff_swaps a b (mk_fresh v t) (mk_fresh v u).
Proof.
  introv d.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp.
Qed.
Hint Resolve implies_diff_swaps_mk_fresh : slow.

Lemma implies_diff_swaps_mk_swap_cs2 {o} :
  forall a b n m (t u : @NTerm o),
    diff_swaps a b t u
    -> diff_swaps a b (mk_swap_cs2 n m t) (mk_swap_cs2 n m u).
Proof.
  introv d.
  repeat (constructor; simpl; tcsp; introv i; repndors; ginv; tcsp).
Qed.
Hint Resolve implies_diff_swaps_mk_swap_cs2 : slow.

Lemma implies_diff_swaps_mk_comp_seq2 {o} :
  forall a b i j k (t1 t2 u1 u2 : @NTerm o),
    diff_swaps a b t1 u1
    -> diff_swaps a b t2 u2
    -> diff_swaps a b (mk_comp_seq2 i j k t1 t2) (mk_comp_seq2 i j k u1 u2).
Proof.
  introv da db.
  repeat (constructor; simpl; tcsp; introv xx; repndors; ginv; tcsp).
Qed.
Hint Resolve implies_diff_swaps_mk_comp_seq2 : slow.

Lemma implies_diff_swaps_mk_eapply {o} :
  forall a b (t1 t2 u1 u2 : @NTerm o),
    diff_swaps a b t1 u1
    -> diff_swaps a b t2 u2
    -> diff_swaps a b (mk_eapply t1 t2) (mk_eapply u1 u2).
Proof.
  introv da db.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_diff_swaps_mk_eapply : slow.

Lemma implies_diff_swaps_mk_apply {o} :
  forall a b (t1 t2 u1 u2 : @NTerm o),
    diff_swaps a b t1 u1
    -> diff_swaps a b t2 u2
    -> diff_swaps a b (mk_apply t1 t2) (mk_apply u1 u2).
Proof.
  introv da db.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_diff_swaps_mk_apply : slow.

Lemma implies_diff_swaps_mk_atom_eq {o} :
  forall a b (t1 t2 t3 t4 u1 u2 u3 u4 : @NTerm o),
    diff_swaps a b t1 u1
    -> diff_swaps a b t2 u2
    -> diff_swaps a b t3 u3
    -> diff_swaps a b t4 u4
    -> diff_swaps a b (mk_atom_eq t1 t2 t3 t4) (mk_atom_eq u1 u2 u3 u4).
Proof.
  introv da db dc dd.
  constructor; simpl; tcsp; introv i; repndors; ginv; tcsp; constructor; auto.
Qed.
Hint Resolve implies_diff_swaps_mk_atom_eq : slow.

Lemma implies_diff_swaps_subst_utok {o} :
  forall a b g (bs1 bs2 : list (@BTerm o)) s,
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps a b (subst_utok g bs1 s) (subst_utok g bs2 s).
Proof.
  introv len imp.
  unfold subst_utok.
  remember (utok_sub_find s g) as x; symmetry in Heqx; destruct x; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_subst_utok : slow.

Lemma implies_diff_swaps_subst_utokens_aux {o} :
  forall a b (t u : @NTerm o) s,
    diff_swaps a b t u
    -> diff_swaps a b (subst_utokens_aux t s) (subst_utokens_aux u s).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; simpl; inv_diff d.

  { destruct op; simpl; auto.

    { destruct c; simpl; eauto 3 with slow;
        try (complete (constructor; autorewrite with slow; auto; introv i; rewrite <- map_combine in i;
                       apply in_map_iff in i; exrepnd; ginv; applydup in_combine in i1; repnd;
                       applydup imp in i1 as d; inv_diff_bterm d; simpl; constructor; eapply ind; eauto)).

      apply implies_diff_swaps_subst_utok; autorewrite with slow; auto.
      introv i; rewrite <- map_combine in i; exrepnd; apply in_map_iff in i; exrepnd; ginv.
      applydup in_combine in i1; repnd.
      apply imp in i1.
      inv_diff_bterm i1; simpl; constructor; eauto. }

    { destruct n; simpl; eauto 3 with slow;
        try (complete (constructor; autorewrite with slow; auto; introv i; rewrite <- map_combine in i;
                       apply in_map_iff in i; exrepnd; ginv; applydup in_combine in i1; repnd;
                       applydup imp in i1 as d; inv_diff_bterm d; simpl; constructor; eapply ind; eauto)). }

    { constructor; autorewrite with slow; auto; introv i; rewrite <- map_combine in i;
        apply in_map_iff in i; exrepnd; ginv; applydup in_combine in i1; repnd;
          applydup imp in i1 as d; inv_diff_bterm d; simpl; constructor; eapply ind; eauto. }

    { constructor; autorewrite with slow; auto; introv i; rewrite <- map_combine in i;
        apply in_map_iff in i; exrepnd; ginv; applydup in_combine in i1; repnd;
          applydup imp in i1 as d; inv_diff_bterm d; simpl; constructor; eapply ind; eauto. } }

  { constructor.
    eapply ind; try (left; reflexivity); auto. }
Qed.
Hint Resolve implies_diff_swaps_subst_utokens_aux : slow.

Lemma diff_swaps_implies_same_bound_vars {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> bound_vars t = bound_vars u.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; inv_diff; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_diff_bterm i0; simpl.
  f_equal.
  apply in_combine in i; repnd.
  eapply ind; eauto.
Qed.
Hint Resolve diff_swaps_implies_same_bound_vars : slow.

Lemma diff_swaps_implies_same_all_vars {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> all_vars t = all_vars u.
Proof.
  introv d.
  applydup @diff_swaps_implies_same_free_vars in d.
  applydup @diff_swaps_implies_same_bound_vars in d.
  unfold all_vars; allrw; auto.
Qed.
Hint Resolve diff_swaps_implies_same_all_vars : slow.

Lemma implies_diff_swaps_change_bvars_alpha {o} :
  forall a b (t u : @NTerm o) l,
    diff_swaps a b t u
    -> diff_swaps a b (change_bvars_alpha l t) (change_bvars_alpha l u).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; inv_diff d.

  { constructor; autorewrite with slow; auto.
    introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
    applydup imp in i1.
    applydup in_combine in i1; repnd.
    inv_diff_bterm i0; simpl.
    pose proof (ind _ _ i3 _ l diff) as ind.
    erewrite diff_swaps_implies_same_all_vars; eauto 3 with slow. }

  { constructor; autorewrite with slow.
    eapply ind; try (left; reflexivity); auto. }
Qed.
Hint Resolve implies_diff_swaps_change_bvars_alpha : slow.

Lemma implies_diff_swaps_subst_utokens {o} :
  forall a b (t u : @NTerm o) s,
    diff_swaps a b t u
    -> diff_swaps a b (subst_utokens t s) (subst_utokens u s).
Proof.
  introv d; unfold subst_utokens.
  erewrite diff_swaps_implies_same_bound_vars; eauto; boolvar; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_subst_utokens : slow.

Lemma diff_swaps_sub_implies_same_free_vars {o} :
  forall a b (s1 s2 : @Sub o),
    diff_swaps_sub a b s1 s2
    -> flat_map free_vars (range s1) = flat_map free_vars (range s2).
Proof.
  introv d; induction d; simpl; auto; f_equal; auto; eauto 3 with slow.
Qed.

Lemma implies_diff_swaps_lsubst {o} :
  forall a b (t u : @NTerm o) (s1 s2 : @Sub o),
    diff_swaps a b t u
    -> diff_swaps_sub a b s1 s2
    -> diff_swaps a b (lsubst t s1) (lsubst u s2).
Proof.
  introv dt ds.
  unfold lsubst.
  erewrite diff_swaps_implies_same_bound_vars; eauto.
  erewrite diff_swaps_sub_implies_same_free_vars; eauto.
  boolvar; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_lsubst : slow.

Lemma diff_swaps_preserves_eapply_wf_def {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> eapply_wf_def t
    -> eapply_wf_def u.
Proof.
  introv d e; unfold eapply_wf_def in *; repndors; exrepnd; subst; repeat inv_diff;
    [left;eexists|right; eexists; eexists]; reflexivity.
Qed.
Hint Resolve diff_swaps_preserves_eapply_wf_def : slow.

Lemma diff_swaps_find_last_entry_default {o} :
  forall a b lib name (t u : @NTerm o),
    diff_swaps a b t u
    -> diff_swaps a b (find_last_entry_default lib name t) (find_last_entry_default lib name u).
Proof.
  introv d.
  unfold find_last_entry_default.
  remember (find_cs lib name) as x; symmetry in Heqx; destruct x; auto.
  remember (last_cs_entry c) as y; symmetry in Heqy; destruct y; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_find_last_entry_default : slow.

Lemma diff_swaps_bterms_implies_eq_map_num_bvars {o} :
  forall a b (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; introv len imp; simpl in *; cpxpp.
  inv_diff_bterms.
  inv_diff_bterm imp0; simpl; f_equal; tcsp.
Qed.

Inductive diff_swaps_sosub_kind {o} a b : @sosub_kind o -> @sosub_kind o -> Type :=
| dawap_sosub_kind :
    forall vs t1 t2,
      diff_swaps a b t1 t2
      -> diff_swaps_sosub_kind a b (sosk vs t1) (sosk vs t2).
Hint Constructors diff_swaps_sosub_kind.

Inductive diff_swaps_sosub {o} a b : @SOSub o -> @SOSub o -> Type :=
| dswaps_sosub_nil : diff_swaps_sosub a b [] []
| dswaps_sosub_cons :
    forall (v : NVar) (t1 t2 : sosub_kind) (s1 s2 : SOSub),
      diff_swaps_sosub_kind a b t1 t2
      -> diff_swaps_sosub a b s1 s2
      -> diff_swaps_sosub a b ((v, t1) :: s1) ((v, t2) :: s2).
Hint Constructors diff_swaps_sosub.


Lemma sosub_find_diff_swaps_if_some {o} :
  forall a b (s1 s2 : @SOSub o) v t,
    diff_swaps_sosub a b s1 s2
    -> sosub_find s1 v = Some t
    -> {u : sosub_kind & sosub_find s2 v = Some u # diff_swaps_sosub_kind a b t u}.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
  inversion d; subst; boolvar; subst; ginv; eexists; dands; eauto.
Qed.

Lemma sosub_find_diff_swaps_if_none {o} :
  forall a b (s1 s2 : @SOSub o) v,
    diff_swaps_sosub a b s1 s2
    -> sosub_find s1 v = None
    -> sosub_find s2 v = None.
Proof.
  introv d; induction d; introv h; simpl in *; boolvar; ginv; eauto.
  inversion d; subst; boolvar; subst; ginv; eexists; dands; eauto.
Qed.

Lemma implies_diff_swaps_sub_combine {o} :
  forall a b vs (ts : list (@SOTerm o)) s1 s2,
    length vs = length ts
    -> diff_swaps_sosub a b s1 s2
    -> (forall t, LIn t ts -> diff_swaps_sosub a b s1 s2 -> diff_swaps a b (sosub_aux s1 t) (sosub_aux s2 t))
    -> diff_swaps_sub a b (combine vs (map (sosub_aux s1) ts)) (combine vs (map (sosub_aux s2) ts)).
Proof.
  induction vs; introv len d imp; simpl in *; eauto 3 with slow; cpxpp.
Qed.
Hint Resolve implies_diff_swaps_sub_combine : slow.

Lemma diff_swaps_apply_list {o} :
  forall a b (ts : list (@SOTerm o)) t u s1 s2,
    diff_swaps_sosub a b s1 s2
    -> diff_swaps a b t u
    -> (forall t, LIn t ts -> diff_swaps_sosub a b s1 s2 -> diff_swaps a b (sosub_aux s1 t) (sosub_aux s2 t))
    -> diff_swaps a b (apply_list t (map (sosub_aux s1) ts)) (apply_list u (map (sosub_aux s2) ts)).
Proof.
  induction ts; introv ds dt imp; simpl in *; auto.
  apply IHts; auto.
  apply implies_diff_swaps_mk_apply; eauto 3 with slow.
Qed.

Lemma diff_swaps_sosub_sosub_filter {o} :
  forall a b (s1 s2 : @SOSub o) l,
    diff_swaps_sosub a b s1 s2
    -> diff_swaps_sosub a b (sosub_filter s1 l) (sosub_filter s2 l).
Proof.
  introv d; induction d; simpl in *; auto.
  inversion d; subst; boolvar; tcsp.
Qed.
Hint Resolve diff_swaps_sosub_sosub_filter : slow.

Lemma implies_diff_swaps_sosub_aux {o} :
  forall a b t (s1 s2 : @SOSub o),
    diff_swaps_sosub a b s1 s2
    -> diff_swaps a b (sosub_aux s1 t) (sosub_aux s2 t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv d; simpl.

  { remember (sosub_find s1 (v, Datatypes.length ts)) as x; symmetry in Heqx; destruct x.
    { dup d as d'; eapply sosub_find_diff_swaps_if_some in d; eauto; exrepnd; allrw.
      inversion d0; subst; clear d0.
      apply implies_diff_swaps_lsubst_aux; auto.
      applydup @sosub_find_some in d1; repnd; eauto 3 with slow. }
    erewrite sosub_find_diff_swaps_if_none; eauto.
    apply diff_swaps_apply_list; auto. }

  constructor; autorewrite with slow; auto.
  introv i.
  rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply in_combine_same in i1; repnd; subst.
  destruct a0; simpl; constructor.
  eapply ind; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_sosub_aux : slow.

Lemma diff_swaps_sosub_same_free_vars_sosub {o} :
  forall a b (s1 s2 : @SOSub o),
    diff_swaps_sosub a b s1 s2
    -> free_vars_sosub s1 = free_vars_sosub s2.
Proof.
  introv d; induction d; simpl in *; auto.
  inversion d as [? ? ? d']; subst; clear d; simpl in *.
  erewrite diff_swaps_implies_same_free_vars; eauto; try congruence.
Qed.

Lemma diff_swaps_sosub_same_bound_vars_sosub {o} :
  forall a b (s1 s2 : @SOSub o),
    diff_swaps_sosub a b s1 s2
    -> bound_vars_sosub s1 = bound_vars_sosub s2.
Proof.
  introv d; induction d; simpl in *; auto.
  inversion d as [? ? ? d']; subst; clear d; simpl in *.
  erewrite diff_swaps_implies_same_bound_vars; eauto; try congruence.
Qed.

Lemma diff_swaps_implies_same_allvars {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> allvars t = allvars u.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d; inv_diff; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).
  apply eq_flat_maps_diff; auto.
  introv i.
  applydup imp in i.
  inv_diff_bterm i0; simpl.
  f_equal.
  apply in_combine in i; repnd.
  eapply ind; eauto.
Qed.
Hint Resolve diff_swaps_implies_same_allvars : slow.

Lemma diff_swaps_sosub_same_allvars_range_sosub {o} :
  forall a b (s1 s2 : @SOSub o),
    diff_swaps_sosub a b s1 s2
    -> allvars_range_sosub s1 = allvars_range_sosub s2.
Proof.
  introv d; induction d; simpl in *; auto.
  inversion d as [? ? ? d']; subst; clear d; simpl in *.
  erewrite diff_swaps_implies_same_allvars; eauto; try congruence.
Qed.

Lemma diff_swaps_sosub_sosub_change_bvars_alpha {o} :
  forall a b (s1 s2 : @SOSub o) l,
    diff_swaps_sosub a b s1 s2
    -> diff_swaps_sosub a b (sosub_change_bvars_alpha l s1) (sosub_change_bvars_alpha l s2).
Proof.
  introv d; induction d; simpl; auto.
  constructor; eauto 3 with slow.
  inversion d as [? ? ? d']; subst; clear d; simpl in *.
  unfold sk_change_bvars_alpha; simpl.
  applydup (implies_diff_swaps_change_bvars_alpha a b t0 t3 l) in d' as d''.
  erewrite diff_swaps_implies_same_all_vars; eauto.
  constructor; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_sosub_sosub_change_bvars_alpha : slow.

Lemma implies_diff_swaps_sosub {o} :
  forall a b (s1 s2 : @SOSub o) t,
    diff_swaps_sosub a b s1 s2
    -> diff_swaps a b (sosub s1 t) (sosub s2 t).
Proof.
  introv d; unfold sosub.
  rewrite <- (diff_swaps_sosub_same_free_vars_sosub a b s1 s2); auto.
  rewrite <- (diff_swaps_sosub_same_bound_vars_sosub a b s1 s2); auto.
  rewrite <- (diff_swaps_sosub_same_allvars_range_sosub a b s1 s2); auto.
  boolvar; eauto 3 with slow.
Qed.
Hint Resolve implies_diff_swaps_sosub : slow.

Lemma diff_swaps_sosub_mk_abs_subst {o} :
  forall a b vs (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1, b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps_sosub a b (mk_abs_subst vs bs1) (mk_abs_subst vs bs2).
Proof.
  induction vs; introv lena imp; simpl in *; auto; cpxpp.
  destruct a0; simpl in *; boolvar; subst; eauto 3 with slow.
  destruct bs1; simpl in *; cpxpp.
  inv_diff_bterms.
  inv_diff_bterm imp0.
  boolvar; subst; eauto 3 with slow.
  constructor; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_sosub_mk_abs_subst : slow.

Lemma diff_swaps_mk_instance {o} :
  forall a b vs (bs1 bs2 : list (@BTerm o)) t,
    length bs1 = length bs2
    -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> diff_swaps_bterm a b b1 b2)
    -> diff_swaps a b (mk_instance vs bs1 t) (mk_instance vs bs2 t).
Proof.
  introv lena imp; unfold mk_instance; eauto 3 with slow.
Qed.
Hint Resolve diff_swaps_mk_instance : slow.

Lemma compute_step_diff_swaps {o} :
  forall a b lib (t : @NTerm o) u z,
    diff_swaps a b t z
    -> compute_step lib t = csuccess u
    -> {w : NTerm
        & compute_step lib z = csuccess w
        # diff_swaps a b u w}.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv diff comp; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|exc|abs] SCase.

  { SCase "Can".
    csunf comp; simpl in *; ginv; eauto.
    inv_diff.
    csunf; simpl; eexists; dands; eauto. }

  { SCase "NCan".
    csunf comp; simpl in *.
    dterms w; try (complete (csunf; simpl; eauto));
      try (complete (apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
                     eapply ind in comp1; try (left; eauto); eauto 3 with slow; exrepnd;
                     csunf; simpl; allrw; simpl in *; allrw; simpl in *; auto)).

    { apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *.
      inv_diff.
      csunf; simpl; eexists; dands; eauto 2 with slow. }

    { dopid_noncan ncan SSCase; simpl in *;
      try apply_comp_success;
      try (complete (dcwf h));
      try (complete (ginv; csunf; simpl in *; eauto)).

      { SSCase "NFix".
        ginv.
        repeat inv_diff.
        csunf; simpl; eexists; dands; eauto.
        repeat (constructor; simpl; auto; introv xx; repndors; subst; ginv; tcsp; constructor; auto). }

      { SSCase "NSleep".
        ginv.
        repeat inv_diff.
        csunf; simpl.
        unfold compute_step_sleep; simpl; eexists; dands; eauto; eauto 3 with slow. }

      { SSCase "NTUni".
        ginv; csunf; simpl in *; eauto.
        repeat inv_diff.
        unfold compute_step_tuni; simpl; boolvar; try omega; autorewrite with slow; auto.
        eexists; dands; eauto; eauto 3 with slow. }

      { SSCase "NMinus".
        ginv; csunf; simpl in *; eauto.
        repeat inv_diff.
        unfold compute_step_minus; simpl; eexists; dands; eauto; eauto 3 with slow. }

      { SSCase "NParallel".
        ginv; csunf; simpl in *; eauto.
        repeat inv_diff.
        unfold compute_step_parallel; simpl; eexists; dands; eauto; eauto 3 with slow. }

      { SSCase "NSwapCs2".
        ginv; csunf; simpl in *; eauto.
        repeat inv_diff; eexists; dands; eauto; eauto 3 with slow. } }

    { apply on_success_csuccess in comp; exrepnd; subst.
      inv_diff.
      { eapply ind in comp1; eauto 2 with slow; exrepnd.
        inv_diff diff.
        { rewrite compute_step_ncan_ncan; allrw; eexists; dands; eauto.
          constructor; simpl; auto; introv i; repndors; ginv; tcsp. }
        unfold mk_swap_cs2 in *; rewrite compute_step_ncan_ncan; allrw; eexists; dands; eauto.
        constructor; simpl; auto; introv i; repndors; ginv; tcsp. }
      { eapply ind in comp1; eauto 2 with slow; exrepnd.
        inv_diff diff0.
        { unfold mk_swap_cs2, nobnd in *; rewrite compute_step_ncan_ncan; allrw; eexists; dands; eauto.
          constructor; simpl; auto; introv i; repndors; ginv; tcsp. }
        unfold mk_swap_cs2, nobnd in *; rewrite compute_step_ncan_ncan; allrw; eexists; dands; eauto.
        constructor; simpl; auto; introv i; repndors; ginv; tcsp. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; ginv; subst; simpl in *.
      csunf; simpl.
      repeat inv_diff; eauto.
      rewrite compute_step_catch_if_diff; tcsp; eauto 3 with slow; eexists; dands; eauto. }

    { apply on_success_csuccess in comp; exrepnd; subst.
      inv_diff.
      { eapply ind in comp1; eauto 2 with slow; exrepnd.
        inv_diff diff.
        csunf comp1; simpl in *.
        rewrite compute_step_ncan_abs; allrw; eexists; dands; eauto.
        constructor; simpl; auto; introv i; repndors; ginv; tcsp. }
      { eapply ind in comp1; eauto 2 with slow; exrepnd.
        inv_diff diff0.
        csunf comp1; simpl in *.
        unfold mk_swap_cs2, nobnd in *; rewrite compute_step_ncan_abs; allrw; eexists; dands; eauto.
        constructor; simpl; auto; introv i; repndors; ginv; tcsp. } }

    { apply compute_step_fresh_success in comp; repeat (repndors; exrepnd; GC; ginv; subst; simpl in * ).
      { repeat inv_diff; csunf; simpl; boolvar; eexists; dands; eauto.
        repeat (constructor; simpl; auto; introv i; repndors; tcsp; ginv). }
      { inv_diff.
        rewrite compute_step_fresh_if_isvalue_like2; eauto 3 with slow;[].
        eexists; dands; eauto; eauto 3 with slow. }
      { inv_diff.
        rewrite computation3.compute_step_fresh_if_isnoncan_like; eauto 3 with slow.
        pose proof (ind w2 (subst w2 w0 (mk_utoken (get_fresh_atom lib w2))) [w0]) as ind.
        rewrite simple_osize_subst in ind; eauto 3 with slow.
        repeat (autodimp ind hyp); eauto 3 with slow.
        pose proof (ind x (subst u w0 (mk_utoken (get_fresh_atom lib u)))) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow.
        { repeat unfsubst; eauto 3 with slow.
          apply implies_diff_swaps_lsubst_aux; eauto 3 with slow. }
        exrepnd.
        allrw; simpl; eexists; dands; eauto.
        erewrite diff_swaps_implies_same_get_fresh_atom; eauto; eauto 3 with slow. } }

    { dopid_noncan ncan SSCase; simpl in *;
        try apply_comp_success;
        try (complete (dcwf h));
        try (complete (dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
                       unfold apply_bterm; autorewrite with slow; simpl; eauto));
        try (complete (try dterms w; repndors; repnd; subst; simpl in *;
                       repeat inv_diff; csunf; simpl; eexists; dands; eauto;
                       unfold subst, apply_bterm; autorewrite with slow; simpl; tcsp; eauto 4 with slow)).

      { SSCase "NEApply".
        inversion comp0; subst; clear comp0.
        repndors; exrepnd; subst; simpl in *; tcsp.

        { apply compute_step_eapply2_success in comp1; repeat (repndors; exrepnd; subst; simpl in * ); ginv.
          { inversion comp3; subst; clear comp3; simpl in *.
            csunf; simpl.
            apply iscan_implies in comp0; exrepnd; subst; simpl in *.
            repeat inv_diff.
            unfold compute_step_eapply; simpl; unfold apply_bterm; autorewrite with slow; auto.
            simpl; eexists; dands; eauto; eauto 4 with slow. }
          { inversion comp1; subst; clear comp1; simpl in *.
            csunf; simpl.
            repeat inv_diff.
            unfold compute_step_eapply; simpl; boolvar; try omega; autorewrite with slow.
            allrw; eexists; dands; eauto; eauto 3 with slow. } }

        { repeat inv_diff.
          fold_terms; rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow. }

        { repeat inv_diff.
          fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
          dup diff as w; eapply ind in w; try (right; left; reflexivity); eauto 3 with slow; exrepnd.
          allrw; eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. } }

      { SSCase "NSwapCs1".
        dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
          repeat inv_diff; unfold apply_bterm; autorewrite with slow; simpl; eauto.
        { apply approx_star_swap.compute_step_swap_cs1_aux_success_implies in comp.
          exrepnd; subst; simpl in *; auto; cpx; simpl in *; repeat inv_diff_bterms.
          eexists; dands; eauto; eauto 3 with slow. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); eauto; eauto 3 with slow.
          exrepnd; allrw; simpl; eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); try apply dswap_diff; eauto; eauto 3 with slow.
          exrepnd; allrw; simpl; eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); try apply dswap_diff; eauto; eauto 3 with slow.
          exrepnd; allrw; simpl; eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. } }

      { SSCase "NLastCs".
        inversion comp3; subst; csunf; simpl; autorewrite with slow; tcsp.
        unfold nobnd in *; ginv; repeat inv_diff; eexists; dands; eauto; eauto 3 with slow. }

      { inversion comp4; subst; clear comp4; repndors; repnd; subst; simpl in *; csunf; simpl; fold_terms; tcsp;
          repeat inv_diff; boolvar; autorewrite with slow in *; subst; try omega; tcsp;
            eexists; dands; eauto; eauto 3 with slow. }

      { unfold nobnd in *; repeat inv_diff.
        repndors; repnd; subst; simpl in *; csunf; simpl; fold_terms; tcsp.
        { unfold sumbool_rec, sumbool_rect; simpl.
          boolvar; try omega; GC; tcsp.
          eexists; dands; eauto; autorewrite with slow; eauto 3 with slow. }
        { boolvar; subst; try omega.
          eexists; dands; eauto.
          autorewrite with slow; tcsp; eauto 3 with slow. } }

      { repeat inv_diff.
        dcwf h; dterms w; simpl in *.
        { apply compute_step_compop_success_can_can in comp; exrepnd; subst; simpl.
          repeat inv_diff.
          csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          repndors; exrepnd; subst; simpl in *; unfold compute_step_comp; simpl; autorewrite with slow.
          { repeat rewrite get_param_from_cop_swap_cs_can; allrw; boolvar; tcsp;
              eexists; dands; eauto. }
          { repeat rewrite get_param_from_cop_swap_cs_can; allrw; destruct pk1, pk2; subst; boolvar; ginv; tcsp;
              eexists; dands; eauto. } }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow; exrepnd.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          repeat inv_diff; allrw; simpl; eexists; dands; eauto; eauto 3 with slow;
            repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }
        { repeat inv_diff.
          csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
        eexists; dands; eauto. }
        { repeat inv_diff.
          apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto);
            try (complete (constructor;eauto)); eauto 3 with slow;[].
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          exrepnd; allrw; simpl; eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. } }

      { repeat inv_diff.
        dcwf h; dterms w; simpl in *.
        { apply compute_step_arithop_success_can_can in comp; exrepnd; subst; simpl.
          repeat inv_diff.
          csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          repndors; exrepnd; subst; simpl in *; unfold compute_step_arith; simpl; autorewrite with slow.
          repeat rewrite get_param_from_cop_swap_cs_can; allrw; boolvar; tcsp.
          eexists; dands; eauto; eauto 3 with slow. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          repeat inv_diff; exrepnd; allrw; simpl; eexists; dands; eauto;
            repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }
        { inv_diff; csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          eexists; dands; eauto. }
        { inv_diff; apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto);
            try (complete (constructor;eauto)); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          exrepnd; simpl in *; allrw; simpl; tcsp.
          eexists; dands; eauto.
          repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. } }

      { dterms w; csunf; simpl; autorewrite with slow; tcsp.
        repeat inv_diff; eexists; dands; eauto.
        destruct (canonical_form_test_for c w4); tcsp. } }

    { apply on_success_csuccess in comp; exrepnd; subst.
      inv_diff.
      eapply ind in comp1; eauto 2 with slow; exrepnd.
      inv_diff.
      { rewrite compute_step_ncan_ncan; allrw; eexists; dands; eauto.
        repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }
      { unfold mk_swap_cs2 in *; rewrite compute_step_ncan_ncan; allrw; simpl.
        eexists; dands; eauto.
        repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; subst; simpl in *.
      { inversion comp2; subst; simpl in *; clear comp2.
        repeat inv_diff.
        csunf; simpl; autorewrite with slow; auto.
        eexists; dands; eauto.
        repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv].
        unfold subst; eauto 3 with slow. }
      { repeat inv_diff.
        csunf; simpl.
        rewrite compute_step_catch_if_diff; tcsp; eauto 3 with slow.
        eexists; dands; eauto. } }

    { apply on_success_csuccess in comp; exrepnd; subst.
      inv_diff.
      eapply ind in comp1; eauto 2 with slow; exrepnd.
      inv_diff.
      csunf comp1; simpl in *.
      rewrite compute_step_ncan_abs; allrw; eexists; dands; eauto.
      repeat first [constructor; simpl; auto|introv i; repndors; tcsp; ginv]. }

    { apply compute_step_fresh_success in comp; exrepnd; subst; simpl in *; ginv. } }

  { csunf comp; simpl in *; ginv; csunf; simpl; tcsp.
    repeat inv_diff; eexists; dands; eauto. }

  { csunf comp; simpl in *.
    repeat inv_diff; csunf; simpl.
    apply compute_step_lib_success in comp; exrepnd; subst.
    eapply compute_step_lib_success_change_bs in comp0;
      [|eapply diff_swaps_bterms_implies_eq_map_num_bvars; eauto].
    eexists; dands; eauto; eauto 3 with slow. }
Qed.

Lemma reduces_in_atmost_k_steps_diff_swaps {o} :
  forall a b lib k (t : @NTerm o) u z,
    diff_swaps a b t z
    -> reduces_in_atmost_k_steps lib t u k
    -> {w : NTerm
        & reduces_in_atmost_k_steps lib z w k
        # diff_swaps a b u w}.
Proof.
  induction k; introv d r; simpl in *.

  { allrw @reduces_in_atmost_k_steps_0; subst.
    exists z; allrw @reduces_in_atmost_k_steps_0; dands; auto. }

  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  eapply compute_step_diff_swaps in r1; eauto; exrepnd.
  eapply IHk in r0; eauto; exrepnd.
  exists w0; allrw @reduces_in_atmost_k_steps_S; dands; auto.
  exists w; dands; auto.
Qed.

Lemma reduces_to_diff_swaps {o} :
  forall a b lib (t : @NTerm o) u z,
    diff_swaps a b t z
    -> reduces_to lib t u
    -> {w : NTerm
        & reduces_to lib z w
        # diff_swaps a b u w}.
Proof.
  introv d r; unfold reduces_to in *; exrepnd.
  eapply reduces_in_atmost_k_steps_diff_swaps in r0; eauto; exrepnd.
  exists w; dands; auto.
  exists k; auto.
Qed.

Lemma diff_swaps_preserves_closed {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> closed t
    -> closed u.
Proof.
  introv d isp.
  unfold closed in *.
  erewrite diff_swaps_implies_same_free_vars in isp; eauto.
Qed.
Hint Resolve diff_swaps_preserves_closed : slow.

Lemma diff_swaps_preserves_nt_wf {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> nt_wf t
    -> nt_wf u.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d wf; inv_diff; simpl; autorewrite with slow; auto;
    try (complete (eapply ind; try (left; reflexivity); auto)).

  { allrw @nt_wf_oterm_iff; repnd.
    rewrite <- wf0.
    erewrite (diff_swaps_bterms_implies_eq_map_num_bvars a b bs bs2); eauto; dands; auto.
    introv i.
    dup len as j; symmetry in j; eapply implies_in_combine in j; eauto; exrepnd.
    apply in_combine_swap in j0; auto.
    applydup imp in j0.
    inv_diff_bterm j1.
    apply in_combine in j0; repnd.
    applydup wf in j1.
    allrw @bt_wf_iff.
    eapply ind; eauto. }

  { apply implies_nt_wf_mk_swap_cs2.
    apply nt_wf_mk_swap_cs2_implies in wf.
    eapply ind; try (left; reflexivity); eauto. }
Qed.
Hint Resolve diff_swaps_preserves_nt_wf : slow.

Lemma diff_swaps_preserves_isprogram {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isprogram t
    -> isprogram u.
Proof.
  introv d isp.
  unfold isprogram in *; repnd; dands; eauto 2 with slow.
Qed.
Hint Resolve diff_swaps_preserves_isprogram : slow.

Lemma diff_swaps_preserves_isvalue {o} :
  forall a b (t u : @NTerm o),
    diff_swaps a b t u
    -> isvalue t
    -> isvalue u.
Proof.
  introv d isv.
  inversion isv as [? isp isc]; subst.
  split; eauto 2 with slow.
Qed.
Hint Resolve diff_swaps_preserves_isvalue : slow.

Lemma computes_to_value_diff_swaps {o} :
  forall a b lib (t : @NTerm o) u z,
    diff_swaps a b t z
    -> computes_to_value lib t u
    -> {w : NTerm
        & computes_to_value lib z w
        # diff_swaps a b u w}.
Proof.
  introv d r; unfold computes_to_value in *; exrepnd.
  eapply reduces_to_diff_swaps in r0; eauto; exrepnd.
  exists w; dands; eauto 2 with slow.
Qed.

Lemma diff_swaps_implies_cl_approx_mk_swap_cs2 {o} :
  forall lib a b (t u : @NTerm o),
    isprogram t
    -> diff_swaps a b t u
    -> cl_approx lib t u.
Proof.
  cofix ind; introv isp d.
  constructor.
  unfold cl_close_comput; dands; eauto 2 with slow;[|].

  { (* VAL case*)

    introv comp.
    applydup @computes_to_value_implies_isprogram in comp as wf.
    eapply computes_to_value_diff_swaps in comp; eauto; exrepnd.
    inv_diff.
    eexists; dands; eauto.

    unfold cl_lblift; autorewrite with slow; dands; auto.
    introv ln; autorewrite with slow.

    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (select2bts tl_subterms bs2 n) as q; repeat (autodimp q hyp); exrepnd.
    applydup imp in q1.
    rewrite q0, q2.
    rewrite q0 in wf, wf0.
    destruct b1 as [l1 u1], b2 as [l2 u2].
    apply bt_wf_iff in wf0.
    inv_diff_bterm q3.

    exists l2 u1 u2; dands; eauto 3 with slow.
    unfold cl_olift.
    dands; eauto 2 with slow;[].

    assert (subset (free_vars u1) l2) as ssa by eauto 2 with slow.
    introv ln' aps.
    eauto 4 with slow. }

  { (* EXC case *)

    introv comp.
    applydup @preserve_program_exc2 in comp; auto; repnd.
    eapply reduces_to_diff_swaps in comp; eauto; exrepnd.
    inv_diff.
    exists u1 u0; dands; eauto 3 with slow. }
Qed.

Lemma diff_swaps_implies_approx_mk_swap_cs2 {o} :
  forall lib a b (t u : @NTerm o),
    isprogram t
    -> diff_swaps a b t u
    -> approx lib t u.
Proof.
  cofix ind; introv isp d.
  constructor.
  unfold close_comput; dands; eauto 2 with slow;[|].

  { (* VAL case*)

    introv comp.
    applydup @computes_to_value_implies_isprogram in comp as wf.
    eapply computes_to_value_diff_swaps in comp; eauto; exrepnd.
    inv_diff.
    eexists; dands; eauto.

    unfold lblift; autorewrite with slow; dands; auto.
    introv ln; autorewrite with slow.

    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (select2bts tl_subterms bs2 n) as q; repeat (autodimp q hyp); exrepnd.
    applydup imp in q1.
    rewrite q0, q2.
    rewrite q0 in wf, wf0.
    destruct b1 as [l1 u1], b2 as [l2 u2].
    apply bt_wf_iff in wf0.
    inv_diff_bterm q3.

    exists l2 u1 u2; dands; eauto 3 with slow.
    unfold olift.
    dands; eauto 2 with slow;[].

    assert (subset (free_vars u1) l2) as ssa by eauto 2 with slow.
    introv wfs ispa ispb; left.
    eapply ind; eauto 3 with slow. }

  { (* EXC case *)

    introv comp.
    applydup @preserve_program_exc2 in comp; auto; repnd.
    eapply reduces_to_diff_swaps in comp; eauto; exrepnd.
    inv_diff.
    exists u1 u0; dands; auto; left; eapply ind; eauto 3 with slow. }
Qed.

Lemma approx_mk_swap_cs2 {o} :
  forall lib n1 n2 (t : @NTerm o),
    isprogram t
    -> approx
         lib
         (mk_swap_cs2 n1 n2 t)
         (mk_swap_cs2 n2 n1 t).
Proof.
  introv isp.
  apply (diff_swaps_implies_approx_mk_swap_cs2 lib n1 n2); eauto 3 with slow.
Qed.
Hint Resolve approx_mk_swap_cs2 : slow.

Lemma cequiv_mk_swap_cs2 {o} :
  forall lib n1 n2 (t : @NTerm o),
    isprogram t
    -> cequiv
         lib
         (mk_swap_cs2 n1 n2 t)
         (mk_swap_cs2 n2 n1 t).
Proof.
  introv isp.
  split; eauto 3 with slow.
Qed.
Hint Resolve cequiv_mk_swap_cs2 : slow.

(*Lemma swap_mk_swap_cs2 {o} :
  forall lib n1 n2 (t : @NTerm o),
    isprogram t
    -> approx
         lib
         (mk_swap_cs2 n1 n2 t)
         (mk_swap_cs2 n2 n1 t).
Proof.
  cofix ind; introv isp.
  constructor.
  unfold close_comput; dands; eauto 2 with slow;[|].

  { introv comp.
    apply swap_cs2_computes_to_value_implies in comp; eauto 2 with slow; exrepnd.
    apply (computes_to_value_can_implies_swap_cs2 n2 n1) in comp0.

    applydup @computes_to_value_implies_isprogram in comp0 as wf.
    apply isprogram_push_swap_cs_can_implies in wf.

    unfold push_swap_cs_can in *; ginv.
    rewrite swap_cs_can_rev in comp0.
    eexists; dands; eauto.
    unfold lblift; autorewrite with slow; dands; auto.
    introv len; autorewrite with slow.
    unfold push_swap_cs_bterms.
    repeat (rewrite selectbt_map; autorewrite with slow; auto).

    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (change_bvars_alpha_norep_bterm (bs {[n]}) []) as ha; destruct ha as [b1 ha]; repnd.
    destruct b1 as [l u]; simpl in *.
    allrw no_repeats_app; repnd.
    eapply alpha_eq_bterm_preserves_isprogram_bt in wf; eauto.
    eapply respect_eauto_albt in wf0; eauto.
    allrw @bt_wf_iff.
    applydup (@implies_alpha_eq_bterm_push_swap_cs_bterm o n1 n2) in ha1; simpl in *.
    applydup (@implies_alpha_eq_bterm_push_swap_cs_bterm o n2 n1) in ha1; simpl in *.

    exists l
           (mk_swap_cs2 n1 n2 (push_swap_cs_sub_term n1 n2 l u))
           (mk_swap_cs2 n2 n1 (push_swap_cs_sub_term n2 n1 l u)).
    dands; auto.

    assert (subset (free_vars u) l) as ssa by eauto 2 with slow.

    apply implies_clearbots_olift.
    apply (approx_open_cl_equiv l); simpl; autorewrite with slow; auto;[].

    unfold cl_olift; dands; eauto 4 with slow;[].

    introv ln ps.
    autorewrite with slow.
    repeat rewrite lsust_mk_swap_cs2_eq.
    unfold push_swap_cs_sub_term.
    repeat (rewrite lsubst_sw_sub_lsust_aux_combine_eq; autorewrite with slow; eauto 2 with slow;[]).

    pose proof (ind lib n1 n2 (lsubst u (sw_sub_ts n1 n2 l ts))) as ind'.
    repeat (autodimp ind' hyp); eauto 2 with slow;[|].
    { apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow. }

    eapply approx_trans;[exact ind'|].
    apply implies_approx_swap_cs2.
    apply lsubst_approx_congr2; eauto 2 with slow;
      try (apply isprogram_lsubst_if_isprog_sub; try rewrite dom_sub_sw_sub_ts; eauto 3 with slow);[].

    apply implies_approx_sub_combine; autorewrite with slow; auto.
    introv j; rewrite <- map_combine_left in j; apply in_map_iff in j; exrepnd; ginv.
    rewrite combine_map_l in j1; apply in_map_iff in j1; exrepnd; inversion j0; subst.
    apply ind; auto. }

  { (* EXC case *)

    introv comp.
    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc n2 n1) in comp.
    eexists; eexists; dands; eauto; left; apply approx_refl; auto. }
Qed.*)


(*
  This does not quite work because if [t=\x.x(0)] then [swap_cs_term (n1,n2) t] is [\x.x(0)]
  and [mk_swap_cs2 n1 n2 t] computes to [\x.mk_swap_cs2 n1 n2 ((mk_swap_cs2 n1 n2 x)0)]
  but applying [\x.x(0)] to [n1] gives [n1(0)],
  while applying [\x.mk_swap_cs2 n1 n2 ((mk_swap_cs2 n1 n2 x)0)] to [n1] computes to [mk_swap_cs2 n1 n2 (n2(0))],
  which would not return the same value if [n1(0)] is not the same choice as [n2(0)]
 *)
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
    applydup (computes_to_value_swap_implies_cs2 cond) in comp; auto.
    eexists; dands; eauto.
    unfold lblift; autorewrite with slow; dands; auto.
    introv len; autorewrite with slow.
    unfold push_swap_cs_bterms.
    rewrite selectbt_map; autorewrite with slow; auto.
    unfold swap_cs_bterms.
    rewrite selectbt_map; autorewrite with slow; auto.

    applydup @computes_to_value_implies_isprogram in comp.
    dup len as wf.
    eapply isprogram_ot_implies_eauto2 in wf; eauto.
    applydup @isprogram_bt_implies_bt_wf in wf.

    pose proof (change_bvars_alpha_norep_bterm (tl_subterms {[n]}) []) as ha; destruct ha as [b1 ha]; repnd.
    destruct b1 as [l u]; simpl in *.
    allrw no_repeats_app; repnd.
    eapply alpha_eq_bterm_preserves_isprogram_bt in wf; eauto.
    eapply respect_eauto_albt in wf0; eauto.
    allrw @bt_wf_iff.

    exists l u (mk_swap_cs2 n1 n2 (push_swap_cs_sub_term n1 n2 l (swap_cs_term (n1, n2) u))).
    dands; eauto 3 with slow;
      [|eapply alpha_eq_bterm_trans;
        [apply implies_alpha_eq_bterm_push_swap_cs_bterm;
         apply implies_alpha_eq_bterm_swap_cs_bterm; eauto|];
        simpl; auto].

    assert (subset (free_vars u) l) as ssa by eauto 2 with slow.

    apply implies_clearbots_olift.
    apply (approx_open_cl_equiv l); simpl; autorewrite with slow; auto;[].

    unfold cl_olift; dands; eauto 4 with slow;[].

    introv ln ps.
    autorewrite with slow.

    pose proof (ind cond lib n1 n2 (lsubst u (combine l ts))) as ind'.
    repeat (autodimp ind' hyp); eauto 2 with slow;[].

    apply (swap_approx (n1,n2)) in ind'.
    rewrite swap_cs_term_idem in ind'.
    erewrite swap_cs_plib_trivial_if_no_cs in ind'; eauto 3 with slow;[].
    autorewrite with slow in *.
    simpl in ind'; boolvar; tcsp; GC; fold_terms;[].
    eapply approx_trans;[eauto|].
    rewrite lsust_mk_swap_cs2_eq.
    rewrite <- lsubst_swap_cs_term.
    rewrite swap_cs_sub_combine.
    unfold push_swap_cs_sub_term.
    rewrite lsubst_sw_sub_lsubst_aux_combine_eq; autorewrite with slow; eauto 2 with slow.
    unfold sw_sub_ts.

(*

We need to
(1) reverse n2/n1
(2) use the [ind] on the substitution as well...

 *)


Locate extensional_op.
SearchAbout approx_star approx_open.
Locate approx_star_open_trans.
SearchAbout swap_cs_sub combine.
SearchAbout swap_cs_term lsubst.
SearchAbout compute_step lsubst_aux.
Locate compute_step_lsubst_aux.
Check compute_step_lsubst_aux.
SearchAbout approx computes_to_value.
SearchAbout approx swap_cs_term.
SearchAbout lsubst swap_cs_term.
SearchAbout csubst mk_apply.
SearchAbout respects_alpha.
SearchAbout olift.

Qed.

Lemma implies_close_mk_swap {o} :
  forall sw (lib : library) (u : cts(o)) (t1 t2 : @CTerm o) e,
    sane_swapping sw
    -> lib_nodup lib
    -> strong_sat_lib_cond lib
    -> type_extensionality u
    -> local_ts u
    -> ts_implies_per_bar u
    -> type_system u
    -> defines_only_universes u
    -> type_monotone u
    -> (forall lib t1 t2 e,
           u uk0 lib t1 t2 e
           -> u uk0 lib
                (mkc_swap_cs sw t1)
                (mkc_swap_cs sw t2)
                (mkc_swap_per sw e))
    -> close u uk0 lib t1 t2 e
    -> close
         u
         uk0 lib
         (mkc_swap_cs sw t1)
         (mkc_swap_cs sw t2)
         (mkc_swap_per sw e).
Proof.
  introv sane nodup sat; introv tyext locts tsimp tysys dou mon imp cl.
  remember uk0 as uk; revert Hequk.
  close_cases (induction cl using @close_ind') Case; introv h; subst.

  { Case "CL_init".
    apply CL_init.
    apply imp; auto.
  }

  { Case "CL_bar".
    apply CL_bar; clear per.
    exists (mkc_swap_lib_per sw eqa); simpl; dands.

    { eapply in_open_bar_ext_pres; try exact reca; clear reca; simpl.
      introv reca; repeat (autodimp reca hyp); eauto 3 with slow. }

    apply mkc_swap_per_bar_eq; auto. }

  { Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per0.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per1.
    autorewrite with slow in *; dands; auto.
    apply mkc_swap_equality_of_int_bar; auto. }

  { Case "CL_nat".
    apply CL_nat.
    unfold per_nat in *; repnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per0; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per1; auto.
    autorewrite with slow in *; dands; auto.
    apply mkc_swap_equality_of_nat_bar; auto. }

  { Case "CL_qnat".
    apply CL_qnat.
    unfold per_qnat in *; exrepnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    eexists; dands; eauto 3 with slow.
    apply mkc_swap_equality_of_qnat_bar; auto. }

  { Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; exrepnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    exists n; dands; eauto 3 with slow.
    apply mkc_swap_equality_of_csname_bar; auto. }

  { Case "CL_atom".
admit.
(*    apply CL_atom.
    unfold per_atom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in per0; auto.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_atom_bar; auto.*) }

  { Case "CL_uatom".
    apply CL_uatom.
admit.
(*    unfold per_uatom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in per0; auto.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_uatom_bar; auto.*) }

  { Case "CL_base".
    apply CL_base.
    unfold per_base in *; exrepnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per0.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per1.
    autorewrite with slow in *; dands; auto.
    apply mkc_swap_per_base_eq; auto. }

  { Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per0; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; dands; eauto.
    { introv xt.
      pose proof (per3 _ xt) as per3; simpl in *; split; intro h.
      { apply capproxc_swap_cs2_implies in h; apply per3 in h; spcast; eauto 3 with slow. }
      { apply capproxc_swap_cs2_implies in h; apply per3 in h; spcast; eauto 3 with slow. } }
    apply mkc_swap_per_approx_eq_bar; auto. }

  { Case "CL_cequiv".
    apply CL_cequiv.
    unfold per_cequiv in *; exrepnd.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per0; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; dands; eauto.
    { introv xt.
      pose proof (per3 _ xt) as per3; simpl in *; split; intro h.
      { apply ccequivc_swap_cs2_implies in h; apply per3 in h; spcast; eauto 3 with slow. }
      { apply ccequivc_swap_cs2_implies in h; apply per3 in h; spcast; eauto 3 with slow. } }
    apply mkc_swap_per_cequiv_eq_bar; auto. }

  { Case "CL_eq".
    apply CL_eq.
    clear per.
admit.
(*    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (swap_cs_lib_per sw sane eqa).
    dands; eauto;
      try (complete (apply (swap_eqorceq_ext sw sane); auto)).

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_eq_per_eq_bar; auto.*) }

  { Case "CL_qtime".
    apply CL_qtime; clear per.
admit.
(*    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_qtime.
    exists (swap_cs_lib_per sw sane eqa).
    eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_per_qtime_eq_bar; auto.*) }

  { Case "CL_qlt".
    apply CL_qlt; clear per.
admit.
(*    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    apply (swap_equality_of_qnat sw) in ceqa; auto.
    apply (swap_equality_of_qnat sw) in ceqb; auto.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; dands; eauto.
    apply swap_per_qlt_eq_bar; auto.*) }

  { Case "CL_func".
    apply CL_func; clear per.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_func_ext.

    exists (mkc_swap_lib_per sw eqa) (mkc_swap_lib_per_fam sw eqb).
    dands; eauto.

    { unfold type_family_ext; simpl in *; repnd.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto; eauto 2 with slow.

      { introv; simpl in *.
        pose proof (reca _ e) as reca; simpl in reca.
        repeat (autodimp reca hyp); eauto 3 with slow. }

      introv; simpl.
      unfold mkc_swap_per in e0.
      autorewrite with slow.
      pose proof (recb _ e _ _ e0) as recb; simpl in recb.
      repeat (autodimp recb hyp); eauto 3 with slow. }

Set Nested Proofs Allowed.

Lemma subst_mk_swap_cs2 {o} :
  forall a b (t : @NTerm o) v u,
    subst (mk_swap_cs2 a b t) v u = mk_swap_cs2 a b (subst t v u).
Proof.
  introv; unfold subst; rewrite lsust_mk_swap_cs2_eq; auto.
Qed.
Hint Rewrite @subst_mk_swap_cs2 : slow.

Lemma reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue {o} :
  forall lib name v k (a : @NTerm o),
    reduces_in_atmost_k_steps lib (mk_eapply (mk_choice_seq name) a) v k
    -> isvalue v
    -> {val : ChoiceSeqVal
        & {n : nat
        & {i : nat
        & {j : nat
        & i + j < k
        # reduces_in_atmost_k_steps lib a (mk_nat n) i
        # reduces_in_atmost_k_steps lib (CSVal2term val) v j
        # find_cs_value_at lib name n = Some val }}}}.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion isv as [? isp isc]; subst; inversion isc.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; ginv.
      exists v0 n 0 k; dands; eauto 3 with slow.
      apply reduces_in_atmost_k_steps_0; auto.

    + apply isexc_implies2 in comp2; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
    inversion isv as [? isp isc]; subst; inversion isc.

    + apply IHk in comp0; auto.
      repndors; exrepnd.
      exists val n (S i) j; dands; auto; try omega.
      rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma computes_to_value_eapply_choice_seq {o} :
  forall lib name v (a : @NTerm o),
    computes_to_value lib (mk_eapply (mk_choice_seq name) a) v
    -> {val : ChoiceSeqVal
        & {n : nat
        & computes_to_value lib a (mk_nat n)
        # reduces_to lib (CSVal2term val) v
        # find_cs_value_at lib name n = Some val }}.
Proof.
  introv comp; unfold computes_to_value in *; repnd.
  unfold reduces_to in *; exrepnd.
  eapply reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue in comp1; auto.
  exrepnd.
  exists val n; dands; eauto.
Qed.

Lemma mkc_swap_per_func_ext_eq {o} :
  forall sw lib (eq : per(o)) eqa eqb,
    (eq <=2=> (per_func_ext_eq lib eqa eqb))
    -> (mkc_swap_per sw eq) <=2=> (per_func_ext_eq lib (mkc_swap_lib_per sw eqa) (mkc_swap_lib_per_fam sw eqb)).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h;
      introv; simpl in *; unfold mkc_swap_per in *.

  { pose proof (h _ _ e0) as h.

SearchAbout mkc_swap_cs mkc_apply.

Lemma xxx {o} :
  forall a b lib (f t : @NTerm o),
    isprog f
    -> isprog t
    -> approx
         lib
         (mk_apply (mk_swap_cs2 a b f) (mk_swap_cs2 a b t))
         (mk_swap_cs2 a b (mk_apply f t)).
Proof.
  cofix ind; introv ispf ispt.
  constructor; unfold close_comput; dands; auto;
    repeat first [apply isprogram_apply| apply implies_isprogram_mk_swap_cs2];
    eauto 2 with slow; introv comp;[|].

  { (* VAL case *)

    apply if_computes_to_value_apply in comp; eauto 4 with slow;[].
    repndors; exrepnd.

    { apply swap_cs2_computes_to_value_implies in comp0; eauto 3 with slow;[].
      exrepnd.
      destruct c0; simpl in *; ginv.
      repeat (destruct bs; simpl in *; ginv).
      destruct b1; simpl in *.
      repeat (destruct l; simpl in *; ginv).
      inversion comp0; subst; clear comp0; fold_terms.
      autorewrite with slow in *.

      assert (cequiv
                lib
                (mk_swap_cs2 a b (subst (push_swap_cs_sub_term a b [n0] n) n0 (mk_swap_cs2 a b t)))
                (mk_swap_cs2 a b (subst n n0 t))) as ceq by admit.

      eapply cequiv_canonical_form in ceq; eauto; exrepnd.
      exists bterms'.
      dands.

      { unfold computes_to_value in *; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;
           eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|];
           apply reduces_to_if_step; csunf; simpl; eauto
          |]; auto. }

      apply clearbot_relbt2.
      apply lblift_cequiv_approx in ceq0; repnd; auto. }

    { apply swap_cs2_computes_to_value_implies in comp1; eauto 3 with slow;[].
      exrepnd.
      destruct c0; simpl in *; ginv.
      repeat (destruct bs; simpl in *; ginv).
      inversion comp1; subst; clear comp1; fold_terms.
      apply computes_to_value_eapply_choice_seq in comp0; exrepnd.

(*

  If the domain were free from choice sequences, we would get that [t] also computes to [n].
  But now we get the n'th choice in c0 and not in swap(a,b,c0)...

*)


Qed.


Qed.

    (*apply swap_per_func_ext_eq; auto.*) }

  { Case "CL_union".
    apply CL_union; clear per.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (mkc_swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_union.
    exists (mkc_swap_lib_per sw eqa) (mkc_swap_lib_per sw eqb).
    eexists; eexists; eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ e) as reca; simpl in reca.
      repeat (autodimp reca hyp); eauto 3 with slow. }

    { introv; simpl.
      pose proof (recb _ e) as recb; simpl in recb.
      repeat (autodimp recb hyp); eauto 3 with slow. }

    apply mkc_swap_per_union_eq_bar; auto;
      try (eapply in_ext_ext_tysys_implies_in_ext_ext_term_equality_respecting;[|eauto]);
      try (eapply in_ext_ext_tysys_implies_in_ext_ext_term_equality_transitive;[|eauto]);
      try (eapply in_ext_ext_tysys_implies_in_ext_ext_term_equality_symmetric;[|eauto]);
      try apply close_type_system; auto. }

  { Case "CL_image".
    apply CL_image; clear per.
admit.
    (*apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    apply (swap_ccequivc_ext sw) in ceq; auto.
    autorewrite with slow in *.
    unfold per_image.
    exists (swap_cs_lib_per sw sane eqa); eexists; eexists; eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_per_image_eq_bar; auto.*) }

  { Case "CL_ffdefs".
    apply CL_ffdefs; clear per.
admit.
    (*apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_ffdefs.
    eexists; eexists; eexists; eexists; exists (swap_cs_lib_per sw sane eqa).
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    { introv; simpl.
      unfold swap_cs_per; simpl.
      autorewrite with slow; eauto. }

    apply swap_per_ffdefs_eq_bar; auto.*) }

  { Case "CL_set".
    apply CL_set; clear per.
admit.
    (*apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_set.

    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb).
    dands; eauto.

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
        repeat (autodimp reca hyp).
        autorewrite with slow in *.
        eapply close_extensionality; try exact reca; auto.
        introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

      introv; simpl.
      assert (eqa (swap_cs_lib sw lib') (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ex.
      { unfold swap_cs_per in *; simpl in *.
        eapply lib_per_cond; eauto. }
      pose proof (recb _ (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a') ex) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond. }

    apply swap_per_set_ext_eq; auto.*) }

  { Case "CL_product".
    apply CL_product; clear per.
admit.
    (*apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in c2; auto.
    autorewrite with slow in *.
    unfold per_set.

    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb).
    dands; eauto.

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
        repeat (autodimp reca hyp).
        autorewrite with slow in *.
        eapply close_extensionality; try exact reca; auto.
        introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

      introv; simpl.
      assert (eqa (swap_cs_lib sw lib') (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ex.
      { unfold swap_cs_per in *; simpl in *.
        eapply lib_per_cond; eauto. }
      pose proof (recb _ (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a') ex) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond. }

    apply swap_per_product_ext_eq; auto.*) }
Qed.
