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

Lemma push_swap_cs_otermc_function {o} :
  forall sw (a : @CTerm o) v b,
    push_swap_cs_otermc sw (mkc_function a v b)
    = mkc_function (mkc_swap_cs sw a) v (mkcv_swap_cs _ sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_function : slow.

Lemma push_swap_cs_otermc_union {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_union a b)
    = mkc_union (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_union : slow.

Lemma push_swap_cs_otermc_approx {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_approx a b)
    = mkc_approx (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_approx : slow.

Lemma push_swap_cs_otermc_cequiv {o} :
  forall sw (a b : @CTerm o),
    push_swap_cs_otermc sw (mkc_cequiv a b)
    = mkc_cequiv (mkc_swap_cs sw a) (mkc_swap_cs sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
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
  forall a b (can : @CanonicalOp o) bs k,
    push_swap_cs_can a b can bs = mk_integer k
    -> can = Nint k # bs = [].
Proof.
  introv h.
  destruct can; simpl in *; ginv.
  destruct bs; simpl in *; ginv; tcsp.
  inversion h; auto.
Qed.

Lemma implies_approx_swap_cs2 {o} :
  forall n1 n2 lib (a b : @NTerm o),
    approx lib a b
    -> approx lib (mk_swap_cs2 n1 n2 a) (mk_swap_cs2 n1 n2 b).
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
  forall n1 n2 lib (a b : @NTerm o),
    cequiv lib a b
    -> cequiv lib (mk_swap_cs2 n1 n2 a) (mk_swap_cs2 n1 n2 b).
Proof.
  introv ceq; destruct ceq as [c1 c2]; split; apply implies_approx_swap_cs2; auto.
Qed.

Lemma implies_cequivc_swap_cs2 {o} :
  forall n1 n2 lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_swap_cs2 n1 n2 a) (mkc_swap_cs2 n1 n2 b).
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
  forall n1 n2 (t : @NTerm o),
    isprogram (mk_swap_cs2 n1 n2 t) <=> isprogram t.
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
  inversion ext0; subst; simpl in *.
  destruct bs; simpl in *; ginv.
  destruct c; simpl in *; ginv.
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
  inversion comp1 as [xx]; subst; clear comp1.
  destruct bs; simpl in *; ginv.
  destruct c; simpl in *; ginv.
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
  forall a b (t : @NTerm o) u,
    alpha_eq (mk_swap_cs2 a b t) u
    -> {z : NTerm & u = mk_swap_cs2 a b z # alpha_eq t z}.
Proof.
  introv aeq; apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst.
  unfold alpha_eq_bterms in *; simpl in *; repnd.
  repeat (destruct bs'; simpl in *; tcsp; ginv).
  pose proof (aeq0 (nobnd t) b0) as aeq0; autodimp aeq0 hyp.
  apply alpha_eq_bterm_nobnd in aeq0; exrepnd; subst.
  exists u; dands; auto.
Qed.

Lemma lsubst_eq_swap2_implies {o} :
  forall t l k a b (u : @NTerm o),
    disjoint k (all_vars t)
    -> length l = length k
    -> lsubst t (var_ren l k) = mk_swap_cs2 a b u
    -> {z : NTerm & t = mk_swap_cs2 a b z # u = lsubst z (var_ren l k)}.
Proof.
  introv disj len h.
  rewrite lsubst_lsubst_aux2 in h; auto;
    [|apply disjoint_sym; apply disjoint_app_r in disj; tcsp].
  destruct t as [v|op bs]; simpl in *.
  { rewrite sub_find_var_ren_as_option_map in h.
    remember (renFind (mk_swapping l k) v) as x; destruct x; simpl in *; ginv. }
  inversion h as [xx]; subst; clear h.
  repeat (destruct bs; simpl in *; tcsp; ginv).
  destruct b0; simpl in *.
  destruct l0; simpl in *; unfold nobnd in *; ginv; fold_terms.
  exists n; dands; autorewrite with slow; auto.
  rewrite lsubst_lsubst_aux2; auto.
  apply disjoint_app_r in disj; simpl in *; autorewrite with slow in disj; repnd; eauto 3 with slow.
Qed.

Lemma implies_cover_vars_mk_swap_cs2 {o} :
  forall a b (t : @NTerm o) sub,
    cover_vars t sub
    -> cover_vars (mk_swap_cs2 a b t) sub.
Proof.
  introv cov.
  allrw @cover_vars_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Resolve implies_cover_vars_mk_swap_cs2 : slow.

Lemma reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc {o} :
  forall a b lib (t : @NTerm o) x e,
    reduces_to lib t (mk_exception x e)
    -> mk_swap_cs2 a b t =e>(x,lib) e.
Proof.
  introv comp.
  unfold computes_to_exception.
  eapply reduces_to_trans;[eapply reduces_to_prinarg; eauto|].
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma swap_cs2_computes_to_exc_implies {o} :
  forall lib a b (t : @NTerm o) x e,
    wf_term t
    -> (mk_swap_cs2 a b t) =e>(x,lib) e
    -> t =e>(x,lib) e.
Proof.
  introv wf comp.
  unfold computes_to_exception, reduces_to in *; exrepnd.

  pose proof (approx_star_swap.computes_to_val_like_in_max_k_steps_swap_cs2_implies
                lib k (MkSwapCsNfo a b) t (mk_exception x e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
  repndors; exrepnd; subst; simpl in *; ginv.

  { apply computes_to_val_like_in_max_k_steps_if_isvalue_like in q0; eauto 3 with slow; ginv. }

  exists k1; auto.
Qed.

Lemma implies_isprogram_lsust_mk_swap_cs2 {o} :
  forall a b (t : @NTerm o) sub,
    isprogram (lsubst t sub)
    -> isprogram (lsubst (mk_swap_cs2 a b t) sub).
Proof.
  introv isp.
  unfold lsubst in *; simpl in *; autorewrite with slow in *.
  boolvar; apply implies_isprogram_mk_swap_cs2; auto.
Qed.
Hint Resolve implies_isprogram_lsust_mk_swap_cs2 : sow.

Lemma lsust_mk_swap_cs2_eq {o} :
  forall a b (t : @NTerm o) sub,
    lsubst (mk_swap_cs2 a b t) sub = mk_swap_cs2 a b (lsubst t sub).
Proof.
  introv.
  unfold lsubst in *; simpl in *; autorewrite with slow in *.
  boolvar; auto.
Qed.

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
    unfold blift in *; exrepnd.

    remember (bterms {[n]}) as b1.
    remember (bs {[n]}) as b2.
    destruct b1 as [l1 u1], b2 as [l2 u2]; simpl in *.
    inversion i2 as [? ? ? ? ? disj1 lena1 lenb1 norep1 aeq1]; subst; clear i2.
    inversion i1 as [? ? ? ? ? disj2 lena2 lenb2 norep2 aeq2]; subst; clear i1.
    autorewrite with slow in disj1, disj2.
    apply disjoint_app_r in disj1; repnd.
    apply disjoint_app_r in disj2; repnd.
    rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in aeq1;
      [|rewrite computation_mark.sub_free_vars_var_ren; auto].
    rewrite lsubst_mk_swap_cs2_choice_seq_var_ren in aeq2;
      [|rewrite computation_mark.sub_free_vars_var_ren; auto].

    apply swap_cs2_alpha_eq_implies in aeq1; exrepnd.
    apply swap_cs2_alpha_eq_implies in aeq2; exrepnd.
    apply lsubst_eq_swap2_implies in aeq1; auto; exrepnd; subst; try congruence;[].
    apply lsubst_eq_swap2_implies in aeq2; auto; exrepnd; subst; try congruence;[].
    autorewrite with slow in disj1, disj2.
    exists lv z1 z; dands; auto;
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
    left; apply ind in i0; auto. }

  { (* EXC case *)

    eapply exception_approx in ap;
      [|eapply reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc; eauto].
    exrepnd.
    repndors; try (complete (inversion ap1)); try (complete (inversion ap2)).
    apply swap_cs2_computes_to_exc_implies in ap0; eauto 3 with slow.
    exists a' e'; dands; auto. }
Qed.

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
  apply cterm_eq; simpl; auto.
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
  apply cterm_eq; simpl; auto.
Qed.

Lemma ccequivc_ext_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    ccequivc_ext lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> ccequivc_ext lib t1 t2.
Proof.
  introv h ext; apply h in ext; spcast.
  apply cequivc_swap_cs2_implies in ext; auto.
Qed.

Lemma computes_to_value_can_implies_swap_cs2 {o} :
  forall a b lib (t : @NTerm o) c bs,
    t =v>(lib) (oterm (Can c) bs)
    -> mk_swap_cs2 a b t =v>(lib) (push_swap_cs_can a b c bs).
Proof.
  introv comp.
  unfold computes_to_value in *; repnd.
  dands; eauto 3 with slow.
  eapply reduces_to_trans;[eapply reduces_to_prinarg; eauto|].
  apply reduces_to_if_step; auto.
Qed.

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

    remember (selectbt bs0 n) as bt; destruct bt; simpl.
    allrw @bt_wf_iff.
    exists l (mk_swap_cs2 a b (mk_swap_cs2 a b n0)) n0; dands; auto.
    unfold olift.
    dands; eauto 3 with slow;[].
    introv wfs ispa ispb; left.
    repeat rewrite lsust_mk_swap_cs2_eq.
    apply ind; apply isprog_eq; auto. }

  { (* EXC case *)

    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    apply swap_cs2_computes_to_exc_implies in comp;
      repeat apply isprog_swap_cs2_implies; exrepnd; eauto 3 with slow;[].
    applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
    exists a0 e; dands; auto; left; apply approx_refl; auto. }
Qed.

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

    remember (selectbt tl_subterms n) as bt; destruct bt; simpl.
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
    apply ind; apply isprog_eq; auto. }

  { (* EXC case *)

    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc a b) in comp.
    apply (reduces_in_atmost_k_steps_implies_swap_cs2_computes_to_exc a b) in comp.
    applydup @preserve_program_exc2 in comp; repnd;
      repeat apply implies_isprogram_mk_swap_cs2; eauto 3 with slow;[].
    exists a0 e; dands; auto; left; apply approx_refl; auto. }
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
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @push_swap_cs_otermc_mkc_inl : slow.

Lemma push_swap_cs_otermc_mkc_inr {o} :
  forall sw (k : @CTerm o),
    push_swap_cs_otermc sw (mkc_inr k) = mkc_inr (mkc_swap_cs sw k).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
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
           u uk1 lib t1 t2 e
           -> u uk1 lib
                (mkc_swap_cs sw t1)
                (mkc_swap_cs sw t2)
                (mkc_swap_per sw e))
    -> close u uk1 lib t1 t2 e
    -> close
         u
         uk1 lib
         (mkc_swap_cs sw t1)
         (mkc_swap_cs sw t2)
         (mkc_swap_per sw e).
Proof.
  introv sane nodup sat; introv tyext locts tsimp tysys dou mon imp cl.
  remember uk1 as uk; revert Hequk.
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

      { introv; simpl.
        pose proof (reca _ e) as reca; simpl in reca.
        repeat (autodimp reca hyp); eauto 3 with slow. }

      introv; simpl.
      unfold mkc_swap_per in e0.
      autorewrite with slow.
      pose proof (recb _ e _ _ e0) as recb; simpl in recb.
      repeat (autodimp recb hyp); eauto 3 with slow.

      assert (eqa lib' e (mkc_swap_cs sw a) (mkc_swap_cs sw a)) as eqa1.
      { pose proof (cla _ e) as cla; simpl in *.
        eapply type_system_term_mem1; try exact cla; eauto; eauto 3 with slow.
        apply close_type_system; auto. }
      assert (eqa lib' e (mkc_swap_cs sw a') (mkc_swap_cs sw a')) as eqa2.
      { pose proof (cla _ e) as cla; simpl in *.
        eapply type_system_term_mem2; try exact cla; eauto; eauto 3 with slow.
        apply close_type_system; auto. }

      pose proof (inv0 (mkc_swap_cs sw a) [sw] _ e eqa1) as inva; simpl in *.
      pose proof (inv (mkc_swap_cs sw a') [sw] _ e eqa2) as invb; simpl in *.
      eapply ccequivc_ext_bar_trans in inva;
        [|apply substc_ccequivc_ext_bar;
          apply ccequivc_ext_bar_sym; auto;
          apply ccequivc_ext_bar_mkc_swap_cs_twice].
      eapply ccequivc_ext_bar_trans in invb;
        [|apply substc_ccequivc_ext_bar;
          apply ccequivc_ext_bar_sym; auto;
          apply ccequivc_ext_bar_mkc_swap_cs_twice].

      eapply close_type_value_respecting_left_bar;
        try (apply implies_ccequivc_ext_bar_mkc_swap;
             apply ccequivc_ext_bar_sym; exact inva); auto.
      eapply close_type_value_respecting_right_bar;
        try (apply implies_ccequivc_ext_bar_mkc_swap;
             apply ccequivc_ext_bar_sym; exact invb); auto. }




(* ====> Will this only work if the domain [A] is such that [mkc_swap_cs] doesn't affect
   its members such as nat? Can I find a counterexample otherwise?
 *)

(*
XXXXXX
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond.*)
 admit. }

admit.
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
