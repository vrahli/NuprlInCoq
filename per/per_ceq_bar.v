(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.


(* !!MOVE *)
Lemma computes_to_value_implies_isprogram {o} :
  forall lib (t1 t2 : @NTerm o), (t1 =v>( lib) t2) -> isprogram t2.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  apply isvalue_implies in comp; tcsp.
Qed.
Hint Resolve computes_to_value_implies_isprogram : slow.

(* !!MOVE *)
Lemma approx_sterm {o} :
  forall lib (t t' : @NTerm o) f,
    computes_to_value lib t (sterm f)
    -> approx lib t t'
    -> {f' : nat -> NTerm
        & computes_to_value lib t' (sterm f')
        # forall n, approx lib (f n) (f' n) }.
Proof.
  introv comp apr.
  invertsn apr.
  repnud apr.
  destruct comp as [comp isv].
  apply apr4 in comp; exrepnd.
  applydup @reduces_to_preserves_program in comp1; auto.

  exists f'; dands; auto.

  { split; auto. }

  { introv.
    pose proof (comp0 n) as q.
    repndors; tcsp; inversion q. }
Qed.

(* !!MOVE *)
Lemma cequiv_seq {o} :
  forall lib (t t' : @NTerm o) f,
    computes_to_value lib t (sterm f)
    -> cequiv lib t t'
    -> {f' : nat -> NTerm
        & computes_to_value lib t' (sterm f')
        # forall n, cequiv lib (f n) (f' n)}.
Proof.
  introv comp ceq.
  allunfold @cequiv; repnd.
  eapply approx_sterm in ceq0;[|eauto].
  exrepnd.
  exists f'; dands; auto.
  introv; dands; auto.
  eapply approx_sterm in ceq;[|eauto].
  exrepnd.
  eapply computes_to_value_eq in comp;[|eauto]; ginv; tcsp.
Qed.

(* !!MOVE *)
Lemma approx_open_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, approx_open lib (f1 n) (f2 n))
    -> nt_wf (sterm f1)
    -> nt_wf (sterm f2)
    -> approx_open lib (sterm f1) (sterm f2).
Proof.
  introv apr wf1 wf2.
  apply approx_star_implies_approx_open.
  econstructor;[| |introv;apply approx_star_iff_approx_open;apply apr|]; eauto 2 with slow.
Qed.

(* !!MOVE *)
Lemma approx_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, approx lib (f1 n) (f2 n))
    -> isprogram (sterm f1)
    -> isprogram (sterm f2)
    -> approx lib (sterm f1) (sterm f2).
Proof.
   introv apr isp1 isp2.
   apply approx_open_approx; auto.
   apply approx_open_sterm_congruence; eauto 2 with slow.
   introv; apply approx_implies_approx_open; auto.
Qed.

(* !!MOVE *)
Lemma cequiv_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, cequiv lib (f1 n) (f2 n))
    -> isprogram (sterm f1)
    -> isprogram (sterm f2)
    -> cequiv lib (sterm f1) (sterm f2).
Proof.
  introv ceq isp1 isp2.
  split; apply approx_sterm_congruence; auto; introv;
    pose proof (ceq n) as q; destruct q; auto.
Qed.

(* !!MOVE *)
Lemma cequiv_value {o} :
  forall lib (t t' v : @NTerm o),
    t =v>(lib) v
    -> cequiv lib t t'
    -> {v' : NTerm & (t' =v>(lib) v') # cequiv lib v v'}.
Proof.
  introv comp ceq.
  unfold computes_to_value in comp; repnd.
  inversion comp as [? isp isv]; subst; clear comp.
  apply iscan_implies in isv; repndors; exrepnd; subst.

  - eapply cequiv_canonical_form in ceq;[|];
      [|split;[eauto|]; eauto 2 with slow].
    exrepnd.
    eexists; dands; eauto.
    apply cequiv_congruence; eauto 2 with slow.

  - eapply cequiv_seq in ceq;[|split;[eauto|];eauto 2 with slow].
    exrepnd.
    eexists; dands; eauto.
    apply cequiv_sterm_congruence; eauto 2 with slow.
Qed.

(* !!MOVE *)
Lemma cequivc_preserves_computes_to_valc {o} :
  forall lib (T T' U : @CTerm o),
    computes_to_valc lib T U
    -> cequivc lib T T'
    -> {U' : CTerm
        & computes_to_valc lib T' U'
        # cequivc lib U U'}.
Proof.
  introv comp ceq.
  unfold computes_to_valc in *.
  unfold cequivc in *.
  destruct_cterms; simpl in *.
  eapply cequiv_value in ceq;[|eauto].
  exrepnd.
  applydup @computes_to_value_implies_isprogram in ceq1.
  apply isprogram_eq in ceq2.
  exists (mk_ct v' ceq2); simpl; dands; auto.
Qed.

(* !!MOVE *)
Lemma cequivc_ext_preserves_computes_to_valc_ceq_bar {o} :
  forall {lib} (bar : BarLib lib) (T T' : @CTerm o) v,
    T ==b==>(bar) v
    -> ccequivc_ext lib T T'
    -> T' ==b==>(bar) v.
Proof.
  introv comp ceq w ext.
  pose proof (comp lib' w lib'0 ext) as h; simpl in h.
  pose proof (ceq lib'0) as q; simpl in q; autodimp q hyp; eauto 3 with slow.
  exrepnd; spcast.

  eapply cequivc_preserves_computes_to_valc in q;[|eauto].
  exrepnd.
  apply cequivc_sym in q0.
  exists U'; dands; spcast; auto.
  eapply cequivc_trans;[eauto|]; auto.
Qed.

(*Lemma eq_per_approx_eq_bar {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq1 ceq2; introv.
  unfold per_approx_eq_bar, per_approx_eq_bar1.
  split; introv h; exrepnd; exists bar; introv w z;
    pose proof (h0 lib' w lib'0 z) as q; clear h0; simpl in q;
      repnd; dands; auto;
        pose proof (ceq1 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow;
          pose proof (ceq2 lib'0) as c2; simpl in c2; autodimp c2 hyp; eauto 3 with slow;
            spcast.

  - eapply approxc_cequivc_trans;[|eauto].
    eapply cequivc_approxc_trans;[apply cequivc_sym;eauto|].
    auto.

  - eapply approxc_cequivc_trans;[|apply cequivc_sym;eauto].
    eapply cequivc_approxc_trans;[eauto|].
    auto.
Qed.*)

Lemma two_computes_to_valc_ceq_bar_implies {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) v1 v2,
    T ==b==>(bar1) v1
    -> T ==b==>(bar2) v2
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib v1 v2).
Proof.
  introv comp1 comp2 b ext.
  simpl in *; exrepnd.
  pose proof (comp1 lib1 b0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (comp2 lib2 b2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  exrepnd.
  spcast.
  computes_to_eqval.
  apply cequivc_sym in q0.
  eapply cequivc_trans in h0;[|eauto]; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_same_bar_implies {o} :
  forall {lib} (bar : BarLib lib) (T : @CTerm o) v1 v2,
    T ==b==>(bar) v1
    -> T ==b==>(bar) v2
    -> all_in_bar bar (fun lib => ccequivc lib v1 v2).
Proof.
  introv comp1 comp2 b ext.
  simpl in *; exrepnd.
  pose proof (comp1 lib' b lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (comp2 lib' b lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  exrepnd.
  spcast.
  computes_to_eqval.
  apply cequivc_sym in q0.
  eapply cequivc_trans in h0;[|eauto]; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_approx {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_approx a1 b1)
    -> T ==b==>(bar2) (mkc_approx a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_approx in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_approx_same_bar {o} :
  forall {lib} (bar : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar) (mkc_approx a1 b1)
    -> T ==b==>(bar) (mkc_approx a2 b2)
    -> all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_same_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_approx in q; repnd; dands; spcast; auto.
Qed.

Lemma eq_per_approx_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) (a1 a2 b1 b2 : @CTerm o),
    all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2)
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_approx_eq_bar, per_approx_eq_bar1.
  split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.

    spcast.
    eapply approxc_cequivc_trans;[|eauto].
    eapply cequivc_approxc_trans;[apply cequivc_sym;eauto|].
    auto.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.

    spcast.
    eapply approxc_cequivc_trans;[|apply cequivc_sym;eauto].
    eapply cequivc_approxc_trans;[eauto|].
    auto.
Qed.

Lemma approx_iff_implies_eq_per_approx_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) (a1 a2 b1 b2 : @CTerm o),
    all_in_bar bar (fun lib => (a1 ~<~(lib) b1) <=> (a2 ~<~(lib) b2))
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_approx_eq_bar, per_approx_eq_bar1.
  split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.
    apply c1; tcsp.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.
    apply c1; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_cequiv {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_cequiv a1 b1)
    -> T ==b==>(bar2) (mkc_cequiv a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_cequiv in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_cequiv_same_bar {o} :
  forall {lib} (bar : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar) (mkc_cequiv a1 b1)
    -> T ==b==>(bar) (mkc_cequiv a2 b2)
    -> all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_same_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_cequiv in q; repnd; dands; spcast; auto.
Qed.

Lemma eq_per_cequiv_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) (a1 a2 b1 b2 : @CTerm o),
    all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2)
    -> ((per_cequiv_eq_bar lib a1 b1) <=2=> (per_cequiv_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_cequiv_eq_bar, per_cequiv_eq_bar1.
  split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.

    spcast.
    eapply cequivc_trans;[|eauto].
    eapply cequivc_trans;[apply cequivc_sym;eauto|].
    auto.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.

    spcast.
    eapply cequivc_trans;[|apply cequivc_sym;eauto].
    eapply cequivc_trans;[eauto|].
    auto.
Qed.

Lemma cequiv_iff_implies_eq_per_cequiv_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) (a1 a2 b1 b2 : @CTerm o),
    all_in_bar bar (fun lib => (a1 ~=~(lib) b1) <=> (a2 ~=~(lib) b2))
    -> ((per_cequiv_eq_bar lib a1 b1) <=2=> (per_cequiv_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_cequiv_eq_bar, per_cequiv_eq_bar1.
  split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.
    apply c1; tcsp.

  - exists (intersect_bars bar bar0).
    introv w z.
    simpl in *; exrepnd.
    pose proof (h0 lib2 w2 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd; dands; auto.
    pose proof (ceq lib1 w0 lib'0) as c1; simpl in c1; autodimp c1 hyp; eauto 3 with slow.
    repnd.
    apply c1; tcsp.
Qed.

Lemma approx_decomp_equality {o} :
  forall lib (a b c d A B : @NTerm o),
    approx lib (mk_equality a b A) (mk_equality c d B)
    <=> approx lib a c # approx lib b d # approx lib A B.
Proof.
  split; unfold mk_equality; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_equality_iff in Hyp1.
    applydup @isprogram_equality_iff in Hyp0.
    repnd.
    eapply blift_approx_open_nobnd in Hyp2bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd.
    applydup @approx_relates_only_progs in Hyp; repnd.
    applydup @approx_relates_only_progs in Hyp0; repnd.
    applydup @approx_relates_only_progs in Hyp1; repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_equality {o} :
  forall lib (a b c d A B : @NTerm o),
    cequiv lib (mk_equality a b A) (mk_equality c d B)
    <=> cequiv lib a c # cequiv lib b d # cequiv lib A B.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_equality lib a b c d A B); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_equality lib c d a b B A); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_equality {o} :
  forall lib (a b c d A B : @CTerm o),
    cequivc lib (mkc_equality a b A) (mkc_equality c d B)
    <=> cequivc lib a c # cequivc lib b d # cequivc lib A B.
Proof.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_equality.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality_same_bar {o} :
  forall {lib} (bar : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar) (mkc_equality a1 b1 A)
    -> T ==b==>(bar) (mkc_equality a2 b2 B)
    -> all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2 # ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_same_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_equality in q; repnd; dands; spcast; auto.
Qed.

Lemma approx_preserves_computes_to_value {o} :
  forall lib (t t' v : @NTerm o),
    computes_to_value lib t v
    -> approx lib t t'
    -> {v' : NTerm $
                   computes_to_value lib t' v'
                   # approx lib v v'}.
Proof.
  introv comp ceq.
  inversion ceq as [cl].
  unfold close_comput in *; repnd.
  applydup @computes_to_value_isvalue in comp.
  apply isvalue_implies_iscan in comp0.
  apply iscan_implies in comp0; repndors; exrepnd; subst.

  - applydup cl2 in comp; exrepnd.
    eexists; dands; eauto.
    apply approx_congruence; auto; eauto 3 with slow;[].
    apply clearbot_relbt; auto.

  - unfold computes_to_value in comp; repnd.
    applydup cl4 in comp0; exrepnd.
    exists (sterm f'); dands; auto.

    { unfold computes_to_value; dands; eauto 3 with slow. }

    constructor.
    split; dands; auto; eauto 2 with slow.

    { introv comp'.
      apply computes_to_value_isvalue_eq in comp'; eauto 3 with slow; ginv. }

    { introv comp'.
      apply reduces_to_if_value in comp'; eauto 3 with slow; ginv. }

    introv comp'.
    apply reduces_to_if_value in comp'; eauto 3 with slow; unfold mk_ntseq in *; ginv.
    exists f'; dands; auto.
    apply reduces_to_symm.
Qed.

Lemma cequiv_preserves_computes_to_value {o} :
  forall lib (t t' v : @NTerm o),
    computes_to_value lib t v
    -> cequiv lib t t'
    -> {v' : NTerm $
                   computes_to_value lib t' v'
                   # cequiv lib v v'}.
Proof.
  introv comp ceq.
  unfold cequiv in ceq; repnd.
  dup comp as comp'.
  eapply approx_preserves_computes_to_value in comp;[|eauto].
  exrepnd.
  applydup @approx_relates_only_progs in ceq; repnd.
  eexists; dands; eauto.

  eapply cequiv_trans;
    [apply cequiv_sym; apply computes_to_value_implies_cequiv;[|eauto];auto|].
  eapply cequiv_trans;[|apply computes_to_value_implies_cequiv;[|eauto];auto].
  split; auto.
Qed.

(*Lemma cequivc_preserves_computes_to_valc {o} :
  forall lib (t t' v : @CTerm o),
    computes_to_valc lib t v
    -> cequivc lib t t'
    -> {v' : CTerm $
                   computes_to_valc lib t' v'
                   # cequivc lib v v'}.
Proof.
  unfold computes_to_valc, cequivc; introv comp ceq; destruct_cterms; allsimpl.
  eapply cequiv_preserves_computes_to_value in ceq;[|eauto].
  exrepnd.
  applydup @cequiv_isprogram in ceq0; repnd.
  exists (mk_cterm v' ceq2); simpl; dands; auto.
Qed.*)

Lemma ccequivc_ext_preserves_all_in_bar {o} :
  forall lib (bar : BarLib lib) (T T' : @CTerm o) v,
    ccequivc_ext lib T T'
    -> all_in_bar bar (fun lib => T ===>(lib) v)
    -> T' ==b==>(bar) v.
Proof.
  introv ceq inbar b ext.
  pose proof (inbar lib' b lib'0 ext) as inbar; simpl in inbar.
  pose proof (ceq lib'0) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *.
  spcast.

  eapply cequivc_preserves_computes_to_valc in ceq;[|eauto].
  exrepnd.
  eexists; dands; spcast; eauto.
  apply cequivc_sym; auto.
Qed.
