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

Lemma wf_swap_cs2 {o} :
  forall n1 n2 (a : @NTerm o),
    wf_term (mk_swap_cs2 n1 n2 a) <=> wf_term a.
Proof.
  introv; rw @wf_oterm_iff; simpl.
  split; intro h; repnd; dands; tcsp.
  { dLin_hyp; allrw @wf_bterm_iff; auto. }
  { introv i; repndors; subst; tcsp. }
Qed.

Lemma isprog_swap_cs2 {o} :
  forall n1 n2 (a : @NTerm o),
    isprog (mk_swap_cs2 n1 n2 a) <=> isprog a.
Proof.
  introv.
  unfold isprog; simpl; autorewrite with slow.
  rw @wf_swap_cs2; tcsp.
Qed.

Lemma isprog_swap_cs2_implies {o} :
  forall n1 n2 (a : @NTerm o),
    isprog a
    -> isprog (mk_swap_cs2 n1 n2 a).
Proof.
  introv ispa; apply isprog_swap_cs2; sp.
Qed.

Lemma isprog_vars_swap_cs2_implies {o} :
  forall vs n1 n2 (a : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs (mk_swap_cs2 n1 n2 a).
Proof.
  introv ispa.
  apply approx_star_swap.implies_isprog_vars_mk_swap_cs2; auto.
Qed.

Definition mkc_swap_cs2 {o} n1 n2 (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (mk_swap_cs2 n1 n2 a) (isprog_swap_cs2_implies n1 n2 a x).

Definition mkcv_swap_cs2 {o} vs n1 n2 (t : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_swap_cs2 n1 n2 a) (isprog_vars_swap_cs2_implies vs n1 n2 a x).

Definition mkc_swap_cs {o} (sw : cs_swap) (t : @CTerm o) :=
  mkc_swap_cs2 (fst sw) (snd sw) t.

Definition mkcv_swap_cs {o} vs (sw : cs_swap) (t : @CVTerm o vs) :=
  mkcv_swap_cs2 _ (fst sw) (snd sw) t.

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

Definition push_swap_cs_oterm {o} sw (t : @NTerm o) : NTerm :=
  match t with
  | oterm (Can can) bs => push_swap_cs_can (fst sw) (snd sw) can bs
  | _ => t
  end.

Lemma implies_isprog_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isprog t
    -> isprog (push_swap_cs_oterm sw t).
Proof.
  introv isp.
  destruct t as [v|op bs]; simpl; auto.
  destruct op; simpl; auto; simpl in *.
  unfold push_swap_cs_can; simpl.
  allrw @isprog_ot_iff; repnd; unfold OpBindings; simpl; autorewrite with slow.
  dands; auto.
  introv i; apply in_map_iff in i; exrepnd; subst.
  destruct a; simpl in *.
  apply isp in i1.
  allrw <- @isprogram_bt_eq.
  unfold isprogram_bt in *; repnd; simpl in *.
  unfold closed_bt in *; simpl in *; autorewrite with slow; dands; auto.
  allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_push_swap_cs_oterm : slow.

Definition push_swap_cs_otermc {o} sw (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (push_swap_cs_oterm sw a) (implies_isprog_push_swap_cs_oterm sw a x).

Lemma implies_isprogram_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isprogram t
    -> isprogram (push_swap_cs_oterm sw t).
Proof.
  introv isp.
  allrw @isprogram_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_push_swap_cs_oterm : slow.

Lemma implies_iscan_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    iscan t
    -> iscan (push_swap_cs_oterm sw t).
Proof.
  introv isc.
  destruct t as [|op bs]; simpl in *; tcsp.
  destruct op; simpl in *; auto.
Qed.
Hint Resolve implies_iscan_push_swap_cs_oterm : slow.

Lemma implies_isvalue_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isvalue t
    -> isvalue (push_swap_cs_oterm sw t).
Proof.
  introv isv.
  destruct isv as [? isp isc].
  split; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_push_swap_cs_oterm : slow.

Lemma mkc_swap_preserves_computes_to_valc {o} :
  forall sw lib (a b : @CTerm o),
    computes_to_valc lib a b
    -> computes_to_valc lib (mkc_swap_cs sw a) (push_swap_cs_otermc sw b).
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in *; repnd; dands; eauto 3 with slow.
  eapply reduces_to_trans;[eapply reduces_to_prinarg; eauto|].
  applydup @isvalue_implies_iscan in comp.
  apply iscan_implies in comp1; exrepnd; subst.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.
Hint Resolve mkc_swap_preserves_computes_to_valc : slow.

Lemma implies_iscvalue_push_swap_cs_otermc {o} :
  forall sw (t : @CTerm o),
    iscvalue t
    -> iscvalue (push_swap_cs_otermc sw t).
Proof.
  introv isv; destruct_cterms; simpl in *.
  unfold iscvalue in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_iscvalue_push_swap_cs_otermc : slow.

Lemma approx_canonical_form2_2 {o} :
  forall lib (op1 op2 : @CanonicalOp o) bterms1 bterms2,
    approx lib (oterm (Can op1) bterms1) (oterm (Can op2) bterms2)
    -> (op1 = op2 # lblift (approx_open lib) bterms1 bterms2).
Proof.
  introv Hap; applydup @approx_relates_only_progs in Hap; repnd.
  eapply approx_canonical_form in Hap; exrepnd; eauto with slow.
  apply computes_to_value_isvalue_eq in Hap3;
  inverts Hap3; eauto with slow.
Qed.

Lemma approx_implies_approx_starbts {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)),
    lblift (approx_open lib) bs1 bs2
    -> approx_starbts lib op bs1 bs2.
Proof.
  introv h.
  unfold approx_starbts, lblift_sub, lblift in *; repnd; dands; auto.
  introv i.
  applydup h in i; clear h.
  unfold blift, blift_sub in *; exrepnd.
  exists lv nt1 nt2; dands; auto.
  apply approx_open_implies_approx_star in i0.
  destruct (dec_op_eq_fresh op) as [d|d]; subst; tcsp.
  right.
  pose proof (exists_nrut_sub lv (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)) as q; exrepnd; subst.
  exists sub; dands; auto.
  apply lsubst_approx_star_congr3; eauto 3 with slow.
Qed.
Hint Resolve approx_implies_approx_starbts : slow.

Lemma implies_approx_push_swap_cs_oterm {o} :
  forall sw lib (a b : @NTerm o),
    isvalue a
    -> isvalue b
    -> approx lib a b
    -> approx lib (push_swap_cs_oterm sw a) (push_swap_cs_oterm sw b).
Proof.
  introv isva isvb apx.
  applydup @isvalue_implies_iscan in isva.
  applydup @isvalue_implies_iscan in isvb.
  apply iscan_implies in isva0; exrepnd; subst.
  apply iscan_implies in isvb0; exrepnd; subst.
  apply approx_canonical_form2_2 in apx; repnd; subst; simpl.
  applydup @isvalue_program in isva.
  applydup @isvalue_program in isvb.

  apply howetheorem1;
    try apply approx_star_swap.implies_isprogram_push_swap_cs_can; auto.
  destruct sw; simpl in *.
  apply approx_star_swap.approx_star_push_swap_cs_can; eauto 2 with slow;[].
  apply implies_nt_wf_push_swap_cs_oterm;
    apply wf_term_implies; apply isprogram_implies_wf;
      eauto 2 with slow.
Qed.

Lemma implies_cequiv_push_swap_cs_oterm {o} :
  forall sw lib (a b : @NTerm o),
    isvalue a
    -> isvalue b
    -> cequiv lib a b
    -> cequiv lib (push_swap_cs_oterm sw a) (push_swap_cs_oterm sw b).
Proof.
  introv isva isvb ceq.
  destruct ceq as [apx1 apx2]; split;
    apply implies_approx_push_swap_cs_oterm; auto.
Qed.

Lemma implies_cequivc_push_swap_cs_otermc {o} :
  forall sw lib (a b : @CTerm o),
    iscvalue a
    -> iscvalue b
    -> cequivc lib a b
    -> cequivc lib (push_swap_cs_otermc sw a) (push_swap_cs_otermc sw b).
Proof.
  introv isva iscb ceq.
  destruct_cterms; unfold cequivc, iscvalue in *; simpl in *.
  apply implies_cequiv_push_swap_cs_oterm; auto.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext {o} :
  forall sw lib (a b : @CTerm o),
    a ===>(lib) b
    -> (mkc_swap_cs sw a) ===>(lib) (push_swap_cs_otermc sw b).
Proof.
  introv comp ext; apply comp in ext; exrepnd; spcast.
  exists (push_swap_cs_otermc sw c); dands; spcast; eauto 3 with slow.
  apply implies_cequivc_push_swap_cs_otermc; auto; eauto 2 with slow.
Qed.

Lemma push_swap_cs_otermc_int {o} :
  forall sw, @push_swap_cs_otermc o sw mkc_int = mkc_int.
Proof.
  introv; apply cterm_eq; simpl; tcsp.
Qed.
Hint Rewrite @push_swap_cs_otermc_int : slow.

Lemma push_swap_cs_otermc_integer {o} :
  forall sw k, @push_swap_cs_otermc o sw (mkc_integer k) = mkc_integer k.
Proof.
  introv; apply cterm_eq; simpl; tcsp.
Qed.
Hint Rewrite @push_swap_cs_otermc_integer : slow.

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
  introv; split; intro h; try apply approx_star_swap.implies_isprogram_mk_swap_cs2; auto.
  destruct h as [cl wf]; split; unfold closed in *; simpl in *; autorewrite with slow in *; auto.
  apply nt_wf_oterm_iff in wf; repnd; simpl in *.
  dLin_hyp; allrw @bt_wf_iff; auto.
Qed.

Lemma implies_isvalue_push_swap_cs_can {o} :
  forall c1 c2 (can : @CanonicalOp o) bs,
    isvalue (oterm (Can can) bs)
    -> isvalue (push_swap_cs_can c1 c2 can bs).
Proof.
  introv isv; inversion isv; subst; split; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_push_swap_cs_can : slow.

Lemma iscan_push_swap_cs_can {o} :
  forall a b c (bs : list (@BTerm o)),
    iscan (push_swap_cs_can a b c bs).
Proof.
  tcsp.
Qed.
Hint Resolve iscan_push_swap_cs_can : slow.

Lemma compute_on_can {o} :
  forall lib (t : @NTerm o) k,
    iscan t
    -> compute_at_most_k_steps lib k t = csuccess t.
Proof.
  induction k; introv isc; simpl in *; auto.
  rewrite IHk; auto.
  apply iscan_compute_step; auto.
Qed.

Lemma reduces_to_if_can {o} :
  forall lib (t u : @NTerm o),
    reduces_to lib t u
    -> iscan t
    -> t = u.
Proof.
 unfold reduces_to, reduces_in_atmost_k_steps; introv Hc Hisv; exrepnd.
 rewrite compute_on_can in Hc0; ginv; auto.
Qed.

Lemma swap_cs2_computes_to_value_implies {o} :
  forall lib a b (t : @NTerm o) u,
    isprog t
    -> (mk_swap_cs2 a b t) =v>(lib) u
    -> {c : CanonicalOp & {bs : list BTerm
       & (t =v>(lib) (oterm (Can c) bs))
       # u = (push_swap_cs_can a b c bs) }}.
Proof.
  introv wf comp.
  unfold computes_to_value, reduces_to in comp; exrepnd.

  pose proof (approx_star_swap.computes_to_val_like_in_max_k_steps_swap_cs2_implies
                lib k (MkSwapCsNfo a b) t u) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
  repndors; exrepnd; subst; simpl in *;
    allapply @isvalue_mk_exception; tcsp;[].

  exists can bs; dands; auto.
  { unfold computes_to_value; dands; eauto 3 with slow.
    unfold computes_to_can_in_max_k_steps in *; repnd.
    apply reduces_atmost_preserves_program in q4; eauto 3 with slow. }

  unfold computes_to_val_like_in_max_k_steps in *; repnd; eauto 3 with slow.
  apply reduces_in_atmost_k_steps_implies_reduces_to in q4.
  apply reduces_to_if_can in q4; eauto 3 with slow.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_integer_implies {o} :
  forall sw lib (t : @CTerm o) k,
  (mkc_swap_cs sw t) ===>(lib) (mkc_integer k)
  -> t ===>(lib) (mkc_integer k).
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  destruct_cterms; unfold computes_to_valc, cequivc in *; simpl in *.
  apply swap_cs2_computes_to_value_implies in ext1; auto; exrepnd; subst.
  eapply cequiv_integer in ext0; eauto 3 with slow.
  apply computes_to_value_if_iscan in ext0; eauto 3 with slow; subst.
  inversion ext0; subst; simpl in *.
  destruct bs; simpl in *; ginv.
  destruct c; simpl in *; ginv.
  exists (@mkc_integer o k); dands; spcast; tcsp.
Qed.

Lemma mkc_swap_ccomputes_to_valc_ext_nat_implies {o} :
  forall sw lib (t : @CTerm o) k,
  (mkc_swap_cs sw t) ===>(lib) (mkc_nat k)
  -> t ===>(lib) (mkc_nat k).
Proof.
  introv comp.
  apply mkc_swap_ccomputes_to_valc_ext_integer_implies in comp; auto.
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
  boolvar; apply approx_star_swap.implies_isprogram_mk_swap_cs2; auto.
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
    apply approx_star_swap.nt_wf_mk_swap_cs2_implies in i1.
    apply approx_star_swap.nt_wf_mk_swap_cs2_implies in i2.
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

Lemma ccequivc_ext_swap_cs2_implies {o} :
  forall a b lib (t1 t2 : @CTerm o),
    ccequivc_ext lib (mkc_swap_cs2 a b t1) (mkc_swap_cs2 a b t2)
    -> ccequivc_ext lib t1 t2.
Proof.
  introv h ext; apply h in ext; spcast.
  apply cequivc_swap_cs2_implies in ext; auto.
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
           u lib t1 t2 e
           -> u lib
                (mkc_swap_cs sw t1)
                (mkc_swap_cs sw t2)
                (mkc_swap_per sw e))
    -> close u lib t1 t2 e
    -> close
         u
         lib
         (mkc_swap_cs sw t1)
         (mkc_swap_cs sw t2)
         (mkc_swap_per sw e).
Proof.
  introv sane nodup sat; introv tyext locts tsimp tysys dou mon imp cl.
  close_cases (induction cl using @close_ind') Case; introv; subst.

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
admit.
(*  apply CL_qnat.
    unfold per_qnat in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    eexists; dands; eauto 3 with slow.
    apply swap_equality_of_qnat_bar; auto.*) }

  { Case "CL_csname".
admit.
(*    apply CL_csname.
    unfold per_csname in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1; auto.
    apply (swap_ccomputes_to_valc_ext sw) in per2; auto.
    autorewrite with slow in *.
    exists n; dands; eauto 3 with slow.
    apply swap_equality_of_csname_bar; auto.*) }

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

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ e) as reca; simpl in reca.
        repeat (autodimp reca hyp); eauto 3 with slow. }

      introv; simpl.
      autorewrite with slow.
      unfold mkc_swap_per in e0.
      pose proof (recb _ e _ _ e0) as recb; simpl in recb.
      repeat (autodimp recb hyp); eauto 3 with slow.

(* Will this only works if the domain [A] is such that [mkc_swap_cs] doesn't affect its members
   such as nat? Can I find a counterexample otherwise?
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

Set Nested Proofs Allowed.

Lemma mkc_swap_per_union_eq_bar {o} :
  forall sw lib (eq : per(o)) eqa eqb,
    (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> (mkc_swap_per sw eq) <=2=> (per_union_eq_bar lib (mkc_swap_lib_per sw eqa) (mkc_swap_lib_per sw eqb)).
Proof.
  introv h; introv.
  unfold mkc_swap_per; rw h; clear h; split; intro h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h;
      unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd.
  { left.


    apply ccomputes_to_valc_ext_implies_ccequivc_ext in h0.

Check ccequivc_ext_swap_cs2_implies.

Lemma mkc_swap_ccomputes_to_valc_ext_inl_implies {o} :
  forall sw lib (t : @CTerm o) k,
  (mkc_swap_cs sw t) ===>(lib) (mkc_inl k)
  -> {u : @CTerm o , t ===>(lib) (mkc_inl u) # k = mkc_swap_cs sw u}.
Proof.
  introv comp.

  pose proof (comp _ (lib_extends_refl _)) as q; simpl in q; exrepnd; spcast.
  apply cequivc_mkc_inl_implies in q0; exrepnd.
  apply computes_to_valc_isvalue_eq in q0; eauto 3 with slow; subst.
  apply swap_cs_computes_to_valc_inl_implies in q1; exrepnd; subst.

  exists z.
  dands.
  { introv ext; pose proof (comp _ ext) as comp; simpl in *; exrepnd.

XXXXx
  destruct_cterms; simpl in *.
  unfold computes_to_valc in q1; simpl in *.

Qed.



  { allapply @mkc_swap_ccomputes_to_valc_ext_axiom_implies; dands; auto; spcast; eauto 3 with slow. }
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h0.
  apply (mkc_swap_ccomputes_to_valc_ext sw) in h1.
  autorewrite with slow in *.
  dands; auto; spcast.
  apply cequivc_swap_cs2_implies in h; auto.
Qed.

    apply mkc_swap_per_union_eq_bar; auto. }

  { Case "CL_image".
    apply CL_image; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
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

    apply swap_per_image_eq_bar; auto. }

  { Case "CL_ffdefs".
    apply CL_ffdefs; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
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

    apply swap_per_ffdefs_eq_bar; auto. }

  { Case "CL_set".
    apply CL_set; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
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

    apply swap_per_set_ext_eq; auto. }

  { Case "CL_product".
    apply CL_product; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1; auto.
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

    apply swap_per_product_ext_eq; auto. }
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
