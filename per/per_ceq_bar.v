(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export type_sys_useful.
Require Import dest_close_tacs.
Require Export bar_fam.


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

Lemma type_extensionality_per_approx_bar {o} :
  forall (ts : cts(o)),
    type_extensionality (per_approx_bar ts).
Proof.
  introv h e.
  unfold per_approx_bar in *; exrepnd.
  exists a b c d; dands; eauto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_approx_bar : slow.

Lemma eq_per_approx_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) (a1 a2 b1 b2 : @CTerm o),
    all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2)
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_approx_eq_bar, per_approx_eq.
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
  unfold per_approx_eq_bar, per_approx_eq.
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

Lemma uniquely_valued_per_approx_bar {o} :
  forall (ts : cts(o)), uniquely_valued (per_approx_bar ts).
Proof.
  introv h q.
  unfold per_approx_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  eapply eq_per_approx_eq_bar; eapply two_computes_to_valc_ceq_bar_mkc_approx; eauto.
Qed.
Hint Resolve uniquely_valued_per_approx_bar : slow.

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
  unfold per_cequiv_eq_bar, per_cequiv_eq.
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
  unfold per_cequiv_eq_bar, per_cequiv_eq.
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
      repeat(destruct n; try (lia;fail); allsimpl);
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

Lemma two_computes_to_valc_ceq_bar_mkc_equality {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2 # ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_equality in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality1 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality2 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality3 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma cequivc_type_sys_props_implies_equal_types {o} :
  forall ts lib (A B C : @CTerm o) eqa,
    type_sys_props ts lib A B eqa
    -> ccequivc_ext lib A C
    -> ts lib A C eqa.
Proof.
  introv tsp ceq.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  pose proof (tyvr A C) as q; repeat (autodimp q hyp).
Qed.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
  apply uv in w; auto.
Qed.

Lemma all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext {o} :
  forall lib (bar : BarLib lib) (a b : @CTerm o),
    all_in_bar bar (fun lib => ccequivc lib a b)
    -> all_in_bar bar (fun lib => ccequivc_ext lib a b).
Proof.
  introv h br ext ext'.
  apply (h lib' br lib'1); eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext : slow.

Lemma all_in_bar_type_sys_props4_implies_term_equality_respecting {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa).
Proof.
  introv h b ext.
  pose proof (h lib' b lib'0 ext) as h; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_respecting : slow.

Lemma all_in_bar_type_sys_props4_implies_term_equality_symmetric {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> term_equality_symmetric eqa.
Proof.
  introv h.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (h lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_symmetric : slow.

Lemma all_in_bar_type_sys_props4_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> term_equality_transitive eqa.
Proof.
  introv h.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (h lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_transitive : slow.

Lemma implies_computes_to_valc_ceq_bar_intersect_bars_left {o} :
  forall lib (bar1 bar2 : @BarLib o lib) T v,
    T ==b==>(bar1) v
    -> T ==b==>(intersect_bars bar1 bar2) v.
Proof.
  introv comp br ext; simpl in *; exrepnd.
  apply (comp lib1 br0 lib'0); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect_bars_left : slow.

Lemma implies_computes_to_valc_ceq_bar_intersect_bars_right {o} :
  forall lib (bar1 bar2 : @BarLib o lib) T v,
    T ==b==>(bar2) v
    -> T ==b==>(intersect_bars bar1 bar2) v.
Proof.
  introv comp br ext; simpl in *; exrepnd.
  apply (comp lib2 br2 lib'0); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect_bars_right : slow.

Definition term_equality_change_lib_extends {o} {lib} (eqa : lib-per(lib,o)) :=
  forall lib' (x1 x2 : lib_extends lib' lib) a1 a2,
    eqa lib' x1 a1 a2
    -> eqa lib' x2 a1 a2.

Lemma in_ext_ext_type_sys_props4_implies_change_lib_extends {o} :
  forall ts lib (A A' : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> term_equality_change_lib_extends eqa.
Proof.
  introv i ea.
  pose proof (i lib' x1) as j; simpl in *.
  pose proof (i lib' x2) as k; simpl in *.

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  apply uv1 in tygt2.
  apply tygt2; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_change_lib_extends : slow.

Definition term_equality_change_lib_extends_fam {o} {lib} {eqa : lib-per(lib,o)} (eqb : lib-per-fam(lib,eqa)) :=
  forall lib' (x1 x2 : lib_extends lib' lib) (a1 a2 : @CTerm o) e1 e2 (t1 t2 : @CTerm o),
    eqb lib' x1 a1 a2 e1 t1 t2
    -> eqb lib' x2 a1 a2 e2 t1 t2.

Lemma in_ext_ext_type_sys_props4_fam_implies_change_lib_extends_fam {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)),
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> term_equality_change_lib_extends_fam eqb.
Proof.
  introv i eb.
  pose proof (i lib' x1 a1 a2 e1) as j; simpl in *.
  pose proof (i lib' x2 a1 a2 e2) as k; simpl in *.

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  apply uv1 in tygt2.
  apply tygt2; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_fam_implies_change_lib_extends_fam : slow.

Definition term_equality_change_lib_extends_bar {o} {lib}
           (bar : BarLib lib)
           (eqa : lib-per(lib,o)) :=
  forall lib' l (b : bar_lib_bar bar l)
         (ext : lib_extends lib' l)
         (x1 x2 : lib_extends lib' lib) a1 a2,
    eqa lib' x1 a1 a2
    -> eqa lib' x2 a1 a2.

Lemma all_in_bar_ext_type_sys_props4_implies_change_lib_extends_bar {o} :
  forall ts lib (bar : BarLib lib) (A A' : @CTerm o) (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> term_equality_change_lib_extends_bar bar eqa.
Proof.
  introv i b ext ea.
  pose proof (i l b lib' ext x1) as j; simpl in *.
  pose proof (i l b lib' ext x2) as k; simpl in *.

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  apply uv1 in tygt2.
  apply tygt2; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_change_lib_extends_bar : slow.

Lemma implies_iff_per_eq_eq {o} :
  forall lib (bar : @BarLib o lib) a1 a2 b1 b2 (eqa eqb : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar bar (fun lib => a1 ~=~(lib) b1)
    -> all_in_bar bar (fun lib => a2 ~=~(lib) b2)
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> (eq_per_eq_bar lib a1 a2 eqa) <=2=> (eq_per_eq_bar lib b1 b2 eqb).
Proof.
  introv eqeq alla allb tes tet ter; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv b e; repeat introv.
    simpl in *; exrepnd.

    simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0 (lib_extends_trans e b3) x) as q; simpl in q; repnd.
    dands; auto.

    pose proof (eqeq lib1 b0 lib'0 (lib_extends_trans e b5) x) as eqeq; simpl in *.
    apply eqeq.

    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0 (lib_extends_trans e b5) x) as z; simpl in z.
    eapply eqorceq_commutes;eauto;
      try (right; auto); try (eapply tes); try (eapply tet); eauto 3 with slow.

  - exists (intersect_bars bar bar0).
    introv b e; repeat introv.

    simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0 (lib_extends_trans e b3) x) as q; simpl in q; repnd.
    dands; auto.

    pose proof (eqeq lib1 b0 lib'0 (lib_extends_trans e b5) x) as eqeq; simpl in *.
    apply eqeq in q.

    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0 (lib_extends_trans e b5) x) as z; simpl in z.
    eapply eqorceq_commutes;eauto;
      try (right; apply ccequivc_ext_sym; eauto);
      try (eapply tes); try (eapply tet); eauto 3 with slow.
Qed.
Hint Resolve implies_iff_per_eq_eq : slow.

Lemma implies_all_in_bar_eqorceq_trans_ccequivc {o} :
  forall lib (bar : @BarLib o lib) a b c eqa,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa)
    -> all_in_bar bar (fun lib => a ~=~(lib) b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b c)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a c).
Proof.
  introv tes tet ter alla allb br ext.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  pose proof (ter lib' br lib'0 ext) as ter; simpl in *.
  eapply eqorceq_trans; eauto.
  right; eauto.
Qed.

Lemma all_in_bar_eqorceq_eq_term_equals {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    (eq1 <=2=> eq2)
    -> all_in_bar bar (fun lib => eqorceq lib eq1 a b)
    -> all_in_bar bar (fun lib => eqorceq lib eq2 a b).
Proof.
  introv eqiff alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve all_in_bar_eqorceq_eq_term_equals : slow.

Lemma all_in_bar_eqorceq_eq_term_equals2 {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    (eq2 <=2=> eq1)
    -> all_in_bar bar (fun lib => eqorceq lib eq1 a b)
    -> all_in_bar bar (fun lib => eqorceq lib eq2 a b).
Proof.
  introv eqiff alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto]; auto.
Qed.
Hint Resolve all_in_bar_eqorceq_eq_term_equals2 : slow.

Lemma ccequivc_ext_refl {o} :
  forall lib (a : @CTerm o), ccequivc_ext lib a a.
Proof.
  introv ext; spcast; auto.
Qed.
Hint Resolve ccequivc_ext_refl : slow.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
  applydup uv in w.

  pose proof (dum A1 A1 B2 eqa1 eqa2) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.

Lemma type_sys_props_ts_refl_left {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A A eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve type_sys_props_ts_refl_left : slow.

Lemma type_sys_props_ts_refl_right {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B B eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve type_sys_props_ts_refl_right : slow.

Lemma eqorceq_refl {o} :
  forall lib eqa (a : @CTerm o),
    eqorceq lib eqa a a.
Proof.
  introv; right; eauto 3 with slow.
Qed.
Hint Resolve eqorceq_refl : slow.

Lemma all_in_bar_eqorceq_refl {o} :
  forall lib (bar : @BarLib o lib) eqa a,
    all_in_bar bar (fun lib => eqorceq lib eqa a a).
Proof.
  introv br ext; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_eqorceq_refl : slow.

Lemma eqorceq_implies_iff_per_eq_eq {o} :
  forall lib (bar : @BarLib o lib) a1 a2 b1 b2 (eqa eqb : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a1 b1)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a2 b2)
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> (eq_per_eq_bar lib a1 a2 eqa) <=2=> (eq_per_eq_bar lib b1 b2 eqb).
Proof.
  introv eqeq alla allb tes tet ter; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv b e; repeat introv.

    simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0 (lib_extends_trans e b3) x) as q; simpl in q; repnd.
    dands; auto.

    pose proof (eqeq lib1 b0 lib'0 (lib_extends_trans e b5) x) as eqeq; simpl in *.
    apply eqeq.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0 (lib_extends_trans e b5)) as h ; simpl in h.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0 (lib_extends_trans e b5)) as w; simpl in w.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0 (lib_extends_trans e b5)) as z; simpl in z.
    eapply eqorceq_commutes;eauto;
      try (right; auto); try (eapply tes); try (eapply tet); eauto 3 with slow.

  - exists (intersect_bars bar bar0).
    introv b e; repeat introv.

    simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0 (lib_extends_trans e b3) x) as q; simpl in q; repnd.
    dands; auto.

    pose proof (eqeq lib1 b0 lib'0 (lib_extends_trans e b5) x) as eqeq; simpl in *.
    apply eqeq in q.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0 (lib_extends_trans e b5)) as h; simpl in h.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0 (lib_extends_trans e b5)) as w; simpl in w.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0 (lib_extends_trans e b5) x) as z; simpl in z.
    eapply eqorceq_commutes;eauto; try (apply eqorceq_sym; auto);
      try eapply tes; try eapply tet; eauto 3 with slow.
Qed.
Hint Resolve eqorceq_implies_iff_per_eq_eq : slow.

(*Lemma type_equality_respecting_trans_per_eq_bar_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' a b A a' b' A',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_equality a b A)
    -> T' ==b==>(bar) (mkc_equality a' b' A')
    -> type_equality_respecting_trans (per_eq_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  repndors; subst; dclose_lr; auto.

  - eapply dest_close_per_equality_ceq_bar_l in cl; eauto.

XXXXXXXXX

  apply CL_eq.
  eapply trans; eauto.
  repndors; subst.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.
    unfold per_eq_bar_or in *; auto; repndors; tcsp.


  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.
Qed.*)

Lemma sub_type_system_implies_type_equality_respecting_trans {o} :
  forall (ts : cts(o)) lib (T1 T2 : @CTerm o),
    type_symmetric ts
    -> type_transitive ts
    -> type_value_respecting ts
    -> type_equality_respecting_trans ts lib T1 T2.
Proof.
  introv tys tyt tyvr.
  introv h ceq q; repndors; subst.

  - pose proof (tyvr lib T3 T1 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.

  - pose proof (tyvr lib T3 T2 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.

  - pose proof (tyvr lib T3 T1 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.

  - pose proof (tyvr lib T3 T2 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.
Qed.

Lemma type_system_implies_all_in_bar_sym {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B A eqa).
Proof.
  introv tsts alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_sym : slow.

Lemma type_system_implies_all_in_bar_trans {o} :
  forall lib (bar : @BarLib o lib) ts A B C eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B C eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa).
Proof.
  introv tsts alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_trans : slow.

Lemma type_system_implies_all_in_bar_eqorceq_sym {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b A B,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b a).
Proof.
  introv tsts alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
  apply eqorceq_sym; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_eqorceq_sym : slow.

Lemma type_system_all_in_bar_ts_implies_term_equality_symmetric {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> term_equality_symmetric eqa.
Proof.
  introv tsts alla.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (alla lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_symmetric : slow.

Lemma type_system_all_in_bar_ts_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> term_equality_transitive eqa.
Proof.
  introv tsts alla.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (alla lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_transitive : slow.

Lemma type_system_all_in_bar_ts_implies_term_equality_respecting {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa).
Proof.
  introv tsts alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_respecting : slow.

Lemma type_system_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    type_system ts
    -> all_in_bar bar1 (fun lib => ts lib A1 A2 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 B1 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A2 B2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B1 eqa1).
Proof.
  introv tsp ts1 ts2 ceq br ext; simpl in *; exrepnd.

  pose proof (ts1 lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (ts2 lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  onedts uv tye tys tyt tyvr tes tet tevr.

  eapply uniquely_valued_trans2;auto;[exact q|].
  eapply uniquely_valued_trans2;auto;[|exact h].
  eapply type_reduces_to_symm2;auto;eauto.
Qed.
Hint Resolve type_system_implies_type_equality_respecting_trans3 : slow.

Lemma type_system_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    type_system ts
    -> all_in_bar bar1 (fun lib => ts lib A1 A2 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 B1 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A2 B2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp ts1 ts2 ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; simpl in b; exrepnd.

  pose proof (ts1 lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (ts2 lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  onedts uv tye tys tyt tyvr tes tet tevr.
  eapply uniquely_valued_eq2; try (exact q); auto.
  eapply uniquely_valued_trans2;auto;[|exact h].
  apply type_system_type_symm;auto.
  eapply type_reduces_to_symm2;auto;eauto.
  apply ccequivc_ext_sym;auto.
Qed.
Hint Resolve type_system_implies_type_equality_respecting_trans4 : slow.

Lemma implies_all_in_bar_eqorceq {o} :
  forall lib (bar1 bar2 : @BarLib o lib) a1 b1 a2 b2 eqa1 eqa2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> all_in_bar bar1 (fun lib => term_equality_respecting lib eqa1)
    -> all_in_bar bar1 (fun lib => eqorceq lib eqa1 a1 b1)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => b1 ~=~(lib) a2)
    -> all_in_bar bar2 (fun lib => eqorceq lib eqa2 a2 b2)
    -> (eqa1 <=2=> eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => eqorceq lib eqa1 a1 b2).
Proof.
  introv tes1 tet1 ter1 alla allb allc eqiff br ext; simpl in *; exrepnd.
  pose proof (alla lib1 br0 lib'0) as alla; simpl in alla; autodimp alla hyp; eauto 3 with slow.
  pose proof (allc lib2 br2 lib'0) as allc; simpl in allc; autodimp allc hyp; eauto 3 with slow.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.
  pose proof (allb lib') as allb; simpl in allb; autodimp allb hyp;[exists lib1 lib2; dands; auto|].
  pose proof (allb lib'0 ext) as allb; simpl in allb.

  pose proof (ter1 lib1 br0 lib'0) as ter1; autodimp ter1 hyp; eauto 3 with slow; simpl in *.

  eapply eqorceq_trans;auto;[exact alla|].
  eapply eqorceq_trans;auto;[right;exact allb|].
  eapply eqorceq_eq_term_equals;[exact eqiff|];auto.
Qed.
Hint Resolve implies_all_in_bar_eqorceq : slow.

Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  unfold type_equality_respecting_trans in tyvrt.
  apply (tyvrt A1 A2 B2 eqa2) in w; auto;[].
  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.
Qed.

Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  apply (tyvrt A1 A2 B2 eqa2) in w; auto;[].
  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.

  pose proof (dum A1 A1 B2 eqa1 eqa2) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma all_in_bar_type_sys_props4_implies_ts_sym {o} :
  forall ts lib (bar : BarLib lib) (A B C : @CTerm o) eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa)
    -> all_in_bar bar (fun lib => ts lib C A eqa).
Proof.
  introv alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in alla.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in allb.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_ts_sym : slow.

Lemma implies_all_in_bar_eqorceq_sym {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b A B,
    term_equality_symmetric eqa
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b a).
Proof.
  introv tes alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  apply eqorceq_sym; eauto.
Qed.
Hint Resolve implies_all_in_bar_eqorceq_sym : slow.

Lemma eq_term_equals_preserves_term_equality_symmetric {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_symmetric eqa1
    -> term_equality_symmetric eqa2.
Proof.
  introv eqiff tes ee.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_symmetric : slow.

Lemma eq_term_equals_preserves_term_equality_transitive {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_transitive eqa1
    -> term_equality_transitive eqa2.
Proof.
  introv eqiff tet ee1 ee2.
  apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
  eapply tet; eauto.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_transitive : slow.

Lemma eq_term_equals_preserves_all_in_bar_term_equality_respecting {o} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa1)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa2).
Proof.
  introv eqiff alla br ext ee ceq.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in alla.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_all_in_bar_term_equality_respecting : slow.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 A2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
  apply uv in w; auto.
Qed.

Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 A2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.
Qed.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 A2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
  applydup uv in w.

  pose proof (dum A1 A1 B2 eqa1 eqa2) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 A2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.

  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  pose proof (dum B1 A1 B2 eqa1 eqa1) as z; repeat (autodimp z hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_type_sys_props4_change_eq_term_equals1 {o} :
  forall ts lib (bar : @BarLib o lib) A B C eqa1 eqa2,
    (eqa1 <=2=> eqa2)
    -> all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa1)
    -> all_in_bar bar (fun lib : library => ts lib A C eqa1)
    -> all_in_bar bar (fun lib : library => ts lib A C eqa2).
Proof.
  introv eqpers allts alla br ext.
  pose proof (allts lib' br lib'0 ext) as allts; simpl in *.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tys; auto.
Qed.

Lemma all_in_bar_type_sys_props4_trans1 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa')
    -> all_in_bar bar (fun lib => ts lib A D eqa')
    -> all_in_bar bar (fun lib => ts lib C D eqa).
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa') as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa') as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa eqa) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_type_sys_props4_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa')
    -> all_in_bar bar (fun lib => ts lib A D eqa')
    -> all_in_bar bar (fun lib => ts lib C D eqa').
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa') as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa') as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa eqa') as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Definition intersect3bars {o} {lib} (bar1 bar2 bar3 : @BarLib o lib) : BarLib lib :=
  intersect_bars bar1 (intersect_bars bar2 bar3).

Lemma implies_intersect3bars1 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar bar1 F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  apply (alla lib1); eauto 3 with slow.
Qed.
Hint Resolve implies_intersect3bars1 : slow.

Lemma implies_intersect3bars2 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar bar2 F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  apply (alla lib0); eauto 3 with slow.
Qed.
Hint Resolve implies_intersect3bars2 : slow.

Lemma implies_intersect3bars3 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar bar3 F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  apply (alla lib3); eauto 3 with slow.
Qed.
Hint Resolve implies_intersect3bars3 : slow.

Lemma intersect_bars_1_2_implies_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar (intersect_bars bar1 bar2) F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_1_2_implies_intersect3bars : slow.

Lemma intersect_bars_1_3_implies_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar (intersect_bars bar1 bar3) F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_1_3_implies_intersect3bars : slow.

Lemma intersect_bars_2_3_implies_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar (intersect_bars bar2 bar3) F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_2_3_implies_intersect3bars : slow.

Lemma implies_computes_to_valc_ceq_bar_intersect3bars1 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) (T v : CTerm),
    (T ==b==>(bar1) v)
    -> (T ==b==>(intersect3bars bar1 bar2 bar3) v).
Proof.
  introv comp br ext; simpl in *; exrepnd.
  eapply comp; eauto; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect3bars1 : slow.

Lemma implies_computes_to_valc_ceq_bar_intersect3bars2 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) (T v : CTerm),
    (T ==b==>(bar2) v)
    -> (T ==b==>(intersect3bars bar1 bar2 bar3) v).
Proof.
  introv comp br ext; simpl in *; exrepnd.
  eapply comp; eauto; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect3bars2 : slow.

Lemma implies_computes_to_valc_ceq_bar_intersect3bars3 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) (T v : CTerm),
    (T ==b==>(bar3) v)
    -> (T ==b==>(intersect3bars bar1 bar2 bar3) v).
Proof.
  introv comp br ext; simpl in *; exrepnd.
  eapply comp; eauto; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect3bars3 : slow.

Lemma implies_all_in_bar_eqorceq_trans {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b c A B,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa)
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b c)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a c).
Proof.
  introv tes tet ter alla allb allc br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  pose proof (allc lib' br lib'0 ext) as allc; simpl in *.
  pose proof (ter lib' br lib'0 ext) as ter; simpl in *.
  eapply eqorceq_trans; eauto.
Qed.
Hint Resolve implies_all_in_bar_eqorceq_trans : slow.

Lemma all_in_bar_ccequivc_sym {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => a ~=~(lib) b)
    -> all_in_bar bar (fun lib => b ~=~(lib) a).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *; spcast; eauto 3 with slow.
  apply cequivc_sym; auto.
Qed.
Hint Resolve all_in_bar_ccequivc_sym : slow.

Lemma all_in_bar_ccequivc_trans {o} :
  forall {lib} (bar : @BarLib o lib) a b c,
    all_in_bar bar (fun lib => a ~=~(lib) b)
    -> all_in_bar bar (fun lib => b ~=~(lib) c)
    -> all_in_bar bar (fun lib => a ~=~(lib) c).
Proof.
  introv alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  spcast.
  eapply cequivc_trans; eauto.
Qed.
Hint Resolve all_in_bar_ccequivc_trans : slow.

Lemma all_in_bar_type_sys_props4_sym_change_eq_term_equals1 {o} :
  forall ts lib (bar : @BarLib o lib) A B C eqa1 eqa2,
    (eqa1 <=2=> eqa2)
    -> all_in_bar bar (fun lib => type_sys_props4 ts lib B A eqa1)
    -> all_in_bar bar (fun lib : library => ts lib A C eqa1)
    -> all_in_bar bar (fun lib : library => ts lib A C eqa2).
Proof.
  introv eqpers allts alla br ext.
  pose proof (allts lib' br lib'0 ext) as allts; simpl in *.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum B A C eqa1 eqa2) as q; repeat (autodimp q hyp); tcsp.

  { apply tygs; auto. }

  apply tys; auto.

  pose proof (dum A B C eqa1 eqa1) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma all_in_bar_type_sys_props4_sym_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar bar (fun lib => type_sys_props4 ts lib B A eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa')
    -> all_in_bar bar (fun lib => ts lib A D eqa')
    -> all_in_bar bar (fun lib => ts lib C D eqa').
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa') as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa') as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa eqa') as h; repeat (autodimp h hyp); tcsp.

  pose proof (dum B C A eqa eqa) as h; repeat (autodimp h hyp); tcsp.
  apply tygs.

  pose proof (dum A B C eqa eqa) as h; repeat (autodimp h hyp); tcsp.
Qed.

Hint Resolve eq_term_equals_sym : slow.

Hint Resolve all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext : slow.

Lemma eq_term_equals_per_func_ext_eq {o} :
  forall lib (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => forall a1 a2 (e1 : eqa1 lib' x a1 a2) (e2 : eqa2 lib' x a1 a2), (eqb1 lib' x a1 a2 e1) <=2=> (eqb2 lib' x a1 a2 e2))
    -> (per_func_ext_eq lib eqa1 eqb1) <=2=> (per_func_ext_eq lib eqa2 eqb2).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_ext_eq.
  split; introv h; exrepnd; exists bar; introv br ext; repeat introv.

  - pose proof (h0 lib' br lib'0 ext x) as h; simpl in h.
    pose proof (eqas lib'0 x) as eqas.
    pose proof (eqbs lib'0 x) as eqbs.
    simpl in *.
    dup e as e'.
    apply eqas in e'.
    apply (eqbs _ _ e'); tcsp.

  - pose proof (h0 lib' br lib'0 ext x) as h; simpl in h.
    pose proof (eqas lib'0 x) as eqas.
    pose proof (eqbs lib'0 x) as eqbs.
    simpl in *.
    dup e as e'.
    apply eqas in e'.
    apply (eqbs _ _ _ e'); tcsp.
Qed.

Lemma eq_term_equals_per_product_eq_bar {o} :
  forall lib (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => forall a1 a2 (e1 : eqa1 lib' x a1 a2) (e2 : eqa2 lib' x a1 a2), (eqb1 lib' x a1 a2 e1) <=2=> (eqb2 lib' x a1 a2 e2))
    -> (per_product_eq_bar lib eqa1 eqb1) <=2=> (per_product_eq_bar lib eqa2 eqb2).
Proof.
  introv eqas eqbs; introv.
  unfold per_product_eq_bar.
  split; introv h; exrepnd; exists bar; introv b e ; repeat introv.

  - pose proof (h0 lib' b lib'0 e x) as h0; simpl in *.
    unfold per_product_eq in *; exrepnd.
    dup h3 as xx.
    apply eqas in xx; eauto 3 with slow.
    eexists; eexists; eexists; eexists; exists xx; dands; eauto.
    eapply eqbs; eauto 3 with slow.

  - pose proof (h0 lib' b lib'0 e x) as h0; simpl in *.
    unfold per_product_eq in *; exrepnd.
    dup h3 as xx.
    apply eqas in xx; eauto 3 with slow.
    eexists; eexists; eexists; eexists; exists xx; dands; eauto.
    eapply eqbs; eauto 3 with slow.
Qed.

Lemma per_product_bar_change_per {o} :
  forall ts lib (T1 T2 : @CTerm o) eqa eqb,
    (eqa <=2=> eqb)
    -> per_product_bar ts lib T1 T2 eqa
    -> per_product_bar ts lib T1 T2 eqb.
Proof.
  introv eqiff per.
  unfold per_product_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve per_product_bar_change_per : slow.

Lemma ccequivc_ext_product {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_product A v B)
    -> {A' : CTerm , {v' : NVar , { B' : CVTerm [v'] ,
        ccomputes_to_valc lib T' (mkc_product A' v' B')
        # ccequivc_ext lib A A'
        # bcequivc_ext lib [v] B [v'] B' }}}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_product in ceq';[|eauto]; exrepnd.
  exists A' v' B'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_product A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_product A' v' B') ceq'1) as z.
    eapply cequivc_mkc_product in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_product A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_product A' v' B') ceq'1) as z.
    eapply cequivc_mkc_product in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Record constructor_inj {o} (C : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o) :=
  {
    cons_inj1 : forall x y z a b c, C x y z = C a b c -> x = a # y = b;
    cons_inj2 : forall x y z c, C x y z = C x y c -> z = c
  }.

Lemma type_family_ext_implies_in_ext_eqas {o} :
  forall ts lib C (T T' : @CTerm o) A A' v B eqa1 eqa2 eqb2,
    constructor_inj C
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa1 lib' x))
    -> type_family_ext C ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (C A v B)
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv cond tsp tf comp; repeat introv.
  pose proof (tsp lib' e) as tsp; simpl in tsp.
  unfold type_family_ext in tf; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.
  pose proof (tf3 lib' e) as tf3; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in tf3; auto.
Qed.
Hint Resolve type_family_ext_implies_in_ext_eqas : slow.

Lemma type_family_ext_implies_in_ext_eqbs {o} :
  forall ts lib C (T T' : @CTerm o) A1 A2 v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    constructor_inj C
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A1 A2 (eqa1 lib' x))
    -> type_family_ext C ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (C A1 v1 B1)
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa1 lib' x a a'),
              type_sys_props4 ts lib' (B1)[[v1\\a]] (B2)[[v2\\a']] (eqb1 lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a1 a2 (e1 : eqa1 lib' x a1 a2) (e2 : eqa2 lib' x a1 a2),
              (eqb1 lib' x a1 a2 e1) <=2=> (eqb2 lib' x a1 a2 e2)).
Proof.
  introv cond tspa tf comp tspb; repeat introv.
  pose proof (type_family_ext_implies_in_ext_eqas ts lib C T T' A1 A2 v1 B1 eqa1 eqa2 eqb2) as eqas.
  repeat (autodimp eqas hyp);[].
  pose proof (tspa lib' e) as tspa; simpl in *.
  pose proof (tspb lib' e) as tspb; simpl in *.
  pose proof (eqas lib' e) as eqas; simpl in *.
  unfold type_family_ext in tf; exrepnd; spcast.

  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  pose proof (tf3 lib' e) as tf3; simpl in *.
  pose proof (tf1 lib' e) as tf1; simpl in *.

  clear tspa.
  pose proof (tspb a1 a2 e1) as tsp; clear tspb.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (tf1 a1 a2 e2) as q.
  apply uv in q; auto.
Qed.
Hint Resolve type_family_ext_implies_in_ext_eqbs : slow.

Lemma constructor_inj_function {o} :
  @constructor_inj o mkc_function.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
Qed.
Hint Resolve constructor_inj_function : slow.

Lemma constructor_inj_product {o} :
  @constructor_inj o mkc_product.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
Qed.
Hint Resolve constructor_inj_product : slow.

(*Lemma type_family_ext_function_implies_in_ext_eqas {o} :
  forall ts lib (T T' : @CTerm o) A A' v B eqa1 eqa2 eqb2,
    in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa1 lib))
    -> type_family_ext mkc_function ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (mkc_function A v B)
    -> in_ext lib (fun lib => (eqa1 lib) <=2=> (eqa2 lib)).
Proof.
  introv tsp tf comp ext.
  pose proof (tsp lib' ext) as tsp; simpl in tsp.
  unfold type_family_ext in tf; exrepnd; spcast.
  computes_to_eqval.
  pose proof (tf3 lib' ext) as tf3; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in tf3; auto.
Qed.
Hint Resolve type_family_ext_function_implies_in_ext_eqas : slow.*)

(*Lemma type_family_ext_function_implies_in_ext_eqbs {o} :
  forall ts lib (T T' : @CTerm o) A1 A2 v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    in_ext lib (fun lib => type_sys_props4 ts lib A1 A2 (eqa1 lib))
    -> type_family_ext mkc_function ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (mkc_function A1 v1 B1)
    -> in_ext lib
              (fun lib =>
                 forall a a' (e : eqa1 lib a a'),
                   type_sys_props4 ts lib (B1)[[v1\\a]] (B2)[[v2\\a']] (eqb1 lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a1 a2 (e1 : eqa1 lib a1 a2) (e2 : eqa2 lib a1 a2),
                   (eqb1 lib a1 a2 e1) <=2=> (eqb2 lib a1 a2 e2)).
Proof.
  introv tspa tf comp tspb ext; repeat introv.
  pose proof (type_family_ext_function_implies_in_ext_eqas ts lib T T' A1 A2 v1 B1 eqa1 eqa2 eqb2) as eqas.
  repeat (autodimp eqas hyp);[].
  pose proof (tspa lib' ext) as tspa; simpl in *.
  pose proof (tspb lib' ext) as tspb; simpl in *.
  pose proof (eqas lib' ext) as eqas; simpl in *.
  unfold type_family_ext in tf; exrepnd; spcast.
  computes_to_eqval.
  pose proof (tf3 lib' ext) as tf3; simpl in *.
  pose proof (tf1 lib' ext) as tf1; simpl in *.

  clear tspa.
  pose proof (tspb a1 a2 e1) as tsp; clear tspb.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (tf1 a1 a2 e2) as q.
  apply uv in q; auto.
Qed.
Hint Resolve type_family_ext_function_implies_in_ext_eqbs : slow.*)

Lemma ccequivc_ext_function {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_function A v B)
    -> {A' : CTerm , {v' : NVar , { B' : CVTerm [v'] ,
        ccomputes_to_valc lib T' (mkc_function A' v' B')
        # ccequivc_ext lib A A'
        # bcequivc_ext lib [v] B [v'] B' }}}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_function in ceq';[|eauto]; exrepnd.
  exists A' v' B'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_function A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_function A' v' B') ceq'1) as z.
    eapply cequivc_mkc_function in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_function A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_function A' v' B') ceq'1) as z.
    eapply cequivc_mkc_function in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma lib_extends_preserves_ccequivc_ext {o} :
  forall lib lib' (A B : @CTerm o),
    lib_extends lib' lib
    -> ccequivc_ext lib A B
    -> ccequivc_ext lib' A B.
Proof.
  introv ext ceq e.
  apply ceq; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_ccequivc_ext : slow.

Lemma bcequivc_ext_implies_ccequivc_ext {o} :
  forall lib v v' (B : @CVTerm o [v]) (B' : @CVTerm o [v']) a,
    bcequivc_ext lib [v] B [v'] B'
    -> ccequivc_ext lib (B)[[v\\a]] (B')[[v'\\a]].
Proof.
  introv beq ext.
  pose proof (beq lib' ext) as beq; simpl in *.
  spcast.
  apply bcequivc1; auto.
Qed.

Lemma type_sys_props4_implies_type_sys_props {p} :
  forall (ts : cts(p)) lib T1 T2 e,
    type_sys_props4 ts lib T1 T2 e
    -> type_sys_props ts lib T1 T2 e.
Proof.
  introv tsp.
  apply type_sys_prop4_implies_type_sys_props3 in tsp.
  apply type_sys_props_iff_type_sys_props3; auto.
Qed.
Hint Resolve type_sys_props4_implies_type_sys_props : slow.

Lemma type_family_ext_cequivc {o} :
  forall C ts lib (T1 T2 : @CTerm o) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A1 v1 B1 A2 v2 B2 A v B,
    computes_to_valc lib T1 (C A1 v1 B1)
    -> computes_to_valc lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A1 A (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a1 a2 (e : eqa lib' x a1 a2),
              type_sys_props4 ts lib'
                              (substc a1 v1 B1)
                              (substc a2 v B)
                              (eqb lib' x a1 a2 e))
    -> type_family_ext C ts lib T1 T2 eqa eqb.
Proof.
  introv co1 co2 ca cb tspa tspb.

  exists A1 A2 v1 v2 B1 B2; dands; spcast; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvr; eauto 3 with slow.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    assert (eqa lib' e a' a') as e' by (apply tet with (t2 := a); sp).

    pose proof (tspb a' a' e') as i.

    onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

    pose proof (tyvr2 (substc a' v1 B1) (substc a' v2 B2)) as k.
    repeat (autodimp k hyp).

    {
      apply (lib_extends_preserves_ccequivc_ext lib lib'); eauto 3 with slow.
      apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a'); auto.
    }

    pose proof (tspb a a' e0) as i.
    pose proof (tspb a' a' e') as j.

    pose proof (type_sys_props_eq ts lib' (substc a v1 B1) (substc a' v1 B1) (substc a' v B) (eqb lib' e a a' e0) (eqb lib' e a' a' e')) as l; repeat (autodimp l hyp); eauto 3 with slow;[].
    pose proof (type_sys_props_ts_trans3 ts lib' (substc a v1 B1) (substc a' v1 B1) (substc a' v2 B2) (substc a' v B) (eqb lib' e a a' e0) (eqb lib' e a' a' e') (eqb lib' e a' a' e')) as w; repeat (autodimp w hyp); eauto 3 with slow.
Qed.

Lemma type_sys_props4_sym {p} :
  forall (ts : cts(p)) lib A B eq,
    type_sys_props4 ts lib A B eq
    -> type_sys_props4 ts lib B A eq.
Proof.
  introv tsp.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  prove_type_sys_props4 Case; tcsp.

  - Case "uniquely_valued".
    introv tsts.
    pose proof (dum B A T3 eq eq') as q; repeat (autodimp q hyp); repnd.
    eapply uv; eauto.

  - Case "type_symmetric".
    introv tsts eqiff.
    pose proof (dum B A T3 eq eq) as q; repeat (autodimp q hyp); repnd.
    eapply tys in q;[|eauto].
    pose proof (dum A B T3 eq eq') as w; repeat (autodimp w hyp); repnd; auto.
    apply tygs; auto.

  - Case "type_value_respecting_trans".
    introv ee ceq tsts.
    repndors; subst; try (complete (eapply tyvrt; eauto)).

  - Case "type_gsymmetric".
    introv; split; intro tsts.

    { pose proof (dum B A T3 eq eq') as q; repeat (autodimp q hyp); repnd.
      pose proof (dum A T3 B eq' eq) as w; repeat (autodimp w hyp); repnd; auto;
        try (complete (apply tygs; auto)). }

    { pose proof (dum B T3 A eq' eq) as q; repeat (autodimp q hyp); repnd;
        try (complete (apply tygs; auto)).
      pose proof (dum A B T3 eq eq') as w; repeat (autodimp w hyp); repnd; auto;
        try (complete (apply tygs; auto)). }

  - Case "type_gtransitive".
    apply tygs; auto.

  - Case "type_mtransitive".
    introv ee ts1 ts2.
    repndors; subst; try (complete (eapply dum; eauto));
      try (complete (pd (dum A T3 T4 eq1 eq2))).
Qed.

Lemma in_ext_type_sys_props4_sym {p} :
  forall (ts : cts(p)) lib A B eq,
    in_ext lib (fun lib => type_sys_props4 ts lib A B (eq lib))
    -> in_ext lib (fun lib => type_sys_props4 ts lib B A (eq lib)).
Proof.
  introv tsp ext.
  pose proof (tsp lib' ext) as tcsp; apply type_sys_props4_sym; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_sym {p} :
  forall (ts : cts(p)) lib A B eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eq lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B A (eq lib' x)).
Proof.
  introv tsp; repeat introv.
  pose proof (tsp lib' e) as tcsp; apply type_sys_props4_sym; auto.
Qed.

Lemma type_sys_props4_eqb_comm {p} :
  forall (ts : cts(p)) lib eqa (eqb : per-fam(eqa))
         a1 a2
         (e : eqa a1 a2) (e1 : eqa a2 a1) (e2 : eqa a1 a1) (e3 : eqa a2 a2)
         v1 B1 v2 B2,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        type_sys_props4 ts lib (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e))
    -> type_sys_props4 ts lib (substc a2 v1 B1) (substc a1 v2 B2) (eqb a1 a2 e).
Proof.
  introv e1 e2 e3 ftspb.

  pose proof (eq_term_equals_sym_tsp
                ts lib eqa eqb a2 a1 e3 e1 e
                v1 B1 v2 B2) as i.
  repeat (autodimp i hyp); eauto 3 with slow.
  destruct i as [eqtb2 i].
  destruct i as [eqtb1 eqtb3].

  prove_type_sys_props4 Case; introv; tcsp.

  - Case "uniquely_valued".
    introv tsts.

    pose proof (ftspb a2 a1 e1) as i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    implies_ts_or_eq (substc a2 v1 B1) T3 (substc a1 v2 B2) h.
    apply uv2 in h.
    apply eq_term_equals_trans with (eq2 := eqb a2 a1 e1); sp.
    apply eq_term_equals_sym; sp.

  - Case "type_symmetric".
    introv tsa eqiff.

    generalize (ftspb a2 a1 e1); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyst2 T3 (eqb a1 a2 e)); intro i.
    dest_imp i h; repnd.
    generalize (tyt2 T3 (eqb a1 a2 e)); intro j.
    dest_imp j h; repnd.
    generalize (tys2 (substc a2 v1 B1) T3 eq'); intro k.
    repeat (dest_imp k h).
    apply eq_term_equals_trans with (eq2 := eqb a1 a2 e); sp.

  - Case "type_value_respecting".
    introv ee ceq.
    repdors; subst.

    {
      generalize (ftspb a2 a2 e3); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
      generalize (tyvr2 (substc a2 v1 B1) T3); intro i.
      dest_imp i h.
      dest_imp i h.

      generalize (ftspb a1 a2 e); intro j.
      apply type_sys_props4_implies_type_sys_props in j.
      onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
      generalize (tygs3 (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro k.
      repeat (dest_imp k h); repnd.
      rw k in tygt3.
      rev_implies_ts_or (substc a2 v1 B1) tygt3.
      apply uv2 in tygt3.
      generalize (tys2 (substc a2 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro l.
      dest_imp l h.
    }

    {
      generalize (ftspb a1 a1 e2); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
      generalize (tyvr2 (substc a1 v2 B2) T3); intro i.
      dest_imp i h.
      dest_imp i h.

      generalize (ftspb a1 a2 e); intro j.
      apply type_sys_props4_implies_type_sys_props in j.
      onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
      implies_ts_or (substc a1 v2 B2) tygt3.
      apply uv2 in tygt3.
      generalize (tys2 (substc a1 v1 B1) T3 (eqb a1 a2 e)); intro l.
      dest_imp l h.
    }

  - Case "type_value_respecting_trans".
    introv ee ceq tsa.
    repdors; subst.

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

  - Case "term_symmetric".
    introv h.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "term_transitive".
    introv h1 h2.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.
    eapply tet2; eauto.

  - Case "term_value_respecting".
    introv h ceq.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "type_gsymmetric".
    introv; split; intro h.

    {
      pose proof (ftspb a2 a1 e1) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs; auto.
    }

    {
      pose proof (ftspb a2 a1 e1) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs; auto.
    }

  - Case "type_gtransitive".
    generalize (ftspb a2 a1 e1); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tys2 (substc a2 v1 B1) (substc a1 v2 B2) (eqb a2 a1 e1)); sp.

  - Case "type_mtransitive".
    introv ee ts1 ts2.
    repdors; subst.

    {
      generalize (ftspb a2 a1 e1); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      pd (tymt2 (substc a2 v1 B1) T3 T4 eq1 eq2).
    }

    {
      generalize (ftspb a2 a1 e1); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      pd (tymt2 (substc a1 v2 B2) T3 T4 eq1 eq2).
    }
Qed.

Lemma type_family_ext_cequivc2 {o} :
  forall C (ts : cts(o)) lib T1 T2 (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A1 v1 B1 A2 v2 B2 A v B,
    computes_to_valc lib T1 (C A1 v1 B1)
    -> computes_to_valc lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A1 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           type_sys_props4
                             ts lib'
                             (substc a1 v B)
                             (substc a2 v1 B1)
                             (eqb lib' x a1 a2 e))
    -> type_family_ext C ts lib T1 T2 eqa eqb.
Proof.
  introv co1 co2 ca cb tspa tspb.

  apply @type_family_ext_cequivc
    with
      (A1 := A1)
      (v1 := v1)
      (B1 := B1)
      (A2 := A2)
      (v2 := v2)
      (B2 := B2)
      (A := A)
      (v := v)
      (B := B); sp;
    try (complete (apply (in_ext_ext_type_sys_props4_sym ts lib); sp)).

  repeat introv.
  pose proof (tspa lib' e) as tspa.
  pose proof (tspb lib' e) as tspb.
  simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  assert (eqa lib' e a2 a1) as e1 by sp.
  assert (eqa lib' e a1 a1) as e2 by (apply tet with (t2 := a2); sp).
  assert (eqa lib' e a2 a2) as e3 by (apply tet with (t2 := a1); sp).

  apply type_sys_props4_sym; sp.
  apply type_sys_props4_eqb_comm; sp.
Qed.

Lemma type_family_ext_value_respecting_trans1 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> computes_to_valc lib T (C A v B)
    -> computes_to_valc lib T3 (C A1 v1 B1)
    -> ccequivc_ext lib A A1
    -> bcequivc_ext lib [v] B [v1] B1
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T3 T4 eqa1 eqb1
    -> type_family_ext C ts lib T T4 eqa1 eqb1.
Proof.
  introv cond comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  exists A A'0 v v'0 B B'0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    pose proof (tf1 a a' e0) as tf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceqb; auto.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A A1 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    dup e0 as e1.
    apply eqas in e1.
    pose proof (tspb a a' e1) as tspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto.
Qed.

Lemma type_family_ext_value_respecting_trans2 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> computes_to_valc lib T (C A' v' B')
    -> computes_to_valc lib T3 (C A1 v1 B1)
    -> ccequivc_ext lib A' A1
    -> bcequivc_ext lib [v'] B' [v1] B1
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T3 T4 eqa1 eqb1
    -> type_family_ext C ts lib T T4 eqa1 eqb1.
Proof.
  introv cond comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  exists A' A'0 v' v'0 B' B'0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A' A1 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (dum A' A A'0 (eqa lib' e) (eqa1 lib' e)) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' e a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply tes; apply eqas;exact e0].
      apply eqas; auto.
    }

    pose proof (tf1 a a' e0) as etf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceqb; auto.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a a e2) as etspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B')[[v'\\a]] (B1)[[v1\\a]] (B'0)[[v'0\\a']] (eqb1 lib' e a a' e0)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
Qed.

Lemma type_sys_props4_implies_eq_term_equals_sym {p} :
  forall (ts  : cts(p))
         (lib : library)
         (eqa : per)
         (eqb : per-fam(eqa))
         v1 B1 v2 B2,
    term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           type_sys_props4 ts lib
                           (substc a1 v1 B1)
                           (substc a2 v2 B2)
                           (eqb a1 a2 e))
    -> (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e))
     # (forall a1 a2 (e2 : eqa a2 a1) (e : eqa a1 a1),
          eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e))
     # (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa a2 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2)).
Proof.
  introv tet h.
  eapply eq_term_equals_sym_tsp2; auto.
  introv;apply type_sys_props4_implies_type_sys_props;eauto.
Qed.

Lemma type_sys_props4_implies_term_equality_transitive {o} :
  forall lib ts (A B : @CTerm o) eqa,
    type_sys_props4 ts lib A B eqa
    -> term_equality_transitive eqa.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_transitive : slow.

Lemma type_family_ext_value_respecting_trans3 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> computes_to_valc lib T (C A v B)
    -> computes_to_valc lib T3 (C A1 v1 B1)
    -> ccequivc_ext lib A A1
    -> bcequivc_ext lib [v] B [v1] B1
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T4 T3 eqa1 eqb1
    -> type_family_ext C ts lib T T4 eqa1 eqb1.
Proof.
  introv cond comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  exists A A0 v v0 B B0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A A1 A0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    assert (eqa1 lib' e a' a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply eqas;eauto]; apply tes; apply eqas; auto.
    }

    pose proof (tf1 a' a e1) as atf1.
    dup ceqb as aceqb.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in aceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in aceqb; auto.

    dup e0 as e2.
    apply eqas in e2.
    pose proof (tspb a a' e2) as atspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B)[[v\\a]] (B1)[[v1\\a]] (B0)[[v0\\a']] (eqb1 lib' e a' a e1)) as q.
    repeat (autodimp q hyp).

    applydup uv in q.
    apply tys.

    {
      pose proof (dum (B)[[v\\a]] (B')[[v'\\a']] (B0)[[v0\\a']] (eqb lib' e a a' e2) (eqb1 lib' e a' a e1)) as w.
      repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.
      pose proof (dum (B')[[v'\\a']] (B)[[v\\a]] (B0)[[v0\\a']] (eqb1 lib' e a' a e1) (eqb lib' e a a' e2)) as z.
      repeat (autodimp z hyp); try (complete (apply tygs; auto)); repnd; auto.
    }

    {
      dup x1 as x2.
      apply eqas in x2.
      pose proof (tspb a' a' x2) as btspb.

      assert ((eqb lib' e a' a' x2) <=2=> (eqb1 lib' e a a' e0)) as eqbs1.
      {
        pose proof (tf1 a a' e0) as btf1.
        dup ceqb as bceqb.
        apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a') in bceqb; auto.
        apply (lib_extends_preserves_ccequivc_ext lib lib') in bceqb; auto.

        onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt2 (B)[[v\\a']] (B1)[[v1\\a']] (B0)[[v0\\a]] (eqb1 lib' e a a' e0)) as z.
        repeat (autodimp z hyp);[].
        apply uv2 in z; auto.
      }
      eapply eq_term_equals_trans;[|eauto];[].

      apply type_sys_props4_implies_eq_term_equals_sym in tspb; eauto 3 with slow;[].
      repnd; tcsp.
    }
Qed.

Lemma type_family_ext_value_respecting_trans4 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> computes_to_valc lib T (C A' v' B')
    -> computes_to_valc lib T3 (C A1 v1 B1)
    -> ccequivc_ext lib A' A1
    -> bcequivc_ext lib [v'] B' [v1] B1
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T4 T3 eqa1 eqb1
    -> type_family_ext C ts lib T T4 eqa1 eqb1.
Proof.
  introv cond comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  exists A' A0 v' v0 B' B0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A' A1 A0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (dum A' A A0 (eqa lib' e) (eqa1 lib' e)) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' e a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[apply eqas;exact e0|].
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a) as e2.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply eqas;exact e0].
      apply tes; apply eqas; auto.
    }

    dup ceqb as aceqb.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in aceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in aceqb; auto.

    pose proof (tf1 a' a e2) as etf1.

    dup e1 as e3.
    apply eqas in e3.
    pose proof (tspb a a e3) as etspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B')[[v'\\a]] (B1)[[v1\\a]] (B0)[[v0\\a']] (eqb1 lib' e a' a e2)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.

    pose proof (dum (B)[[v\\a]] (B')[[v'\\a]] (B0)[[v0\\a']] (eqb lib' e a a e3) (eqb1 lib' e a a' e0)) as w.
    repeat (autodimp w hyp); repnd; tcsp; try (complete (apply tygs; auto)).

    pose proof (dum (B')[[v'\\a]] (B)[[v\\a]] (B0)[[v0\\a']] (eqb lib' e a a e3) (eqb1 lib' e a' a e2)) as z.
    repeat (autodimp z hyp); repnd; tcsp; try (complete (apply tygs; auto)).

    applydup uv in z.
    apply tys.

    {
      pose proof (dum (B')[[v'\\a]] (B)[[v\\a]] (B0)[[v0\\a']] (eqb lib' e a a e3) (eqb1 lib' e a' a e2)) as w.
      repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.
    }

    {
      dup x1 as x2.
      apply eqas in x2.
      pose proof (tspb a' a' x2) as btspb.

      assert ((eqb lib' e a' a' x2) <=2=> (eqb1 lib' e a a' e0)) as eqbs1.
      {
        pose proof (tf1 a a' e0) as btf1.
        dup ceqb as bceqb.
        apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a') in bceqb; auto.
        apply (lib_extends_preserves_ccequivc_ext lib lib') in bceqb; auto.

        onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt2 (B')[[v'\\a']] (B1)[[v1\\a']] (B0)[[v0\\a]] (eqb1 lib' e a a' e0)) as u.
        repeat (autodimp u hyp);[].
        pose proof (dum2 (B')[[v'\\a']] (B)[[v\\a']] (B0)[[v0\\a]] (eqb lib' e a' a' x2) (eqb1 lib' e a a' e0)) as w.
        repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.

        apply uv2 in w; auto.
      }
      eapply eq_term_equals_trans;[|eauto];[].

      apply type_sys_props4_implies_eq_term_equals_sym in tspb; eauto 3 with slow;[].
      repnd; tcsp.
      dup e0 as x3.
      apply eqas in x3.
      pose proof (tspb0 a a' x3 e3) as p1.
      pose proof (tspb1 a' a x3 x2) as p2.
      eapply eq_term_equals_trans;[|exact p2].
      apply eq_term_equals_sym; auto.
    }
Qed.

Lemma type_sys_props4_implies_term_equality_symmetric {o} :
  forall lib (ts : cts(o)) A B eqa,
    type_sys_props4 ts lib A B eqa
    -> term_equality_symmetric eqa.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_symmetric : slow.

Lemma type_sys_props4_change_per1 {o} :
  forall ts lib (A B C : @CTerm o) eqa1 eqa2,
    type_sys_props4 ts lib A B eqa1
    -> ts lib A C eqa2
    -> ts lib A C eqa1.
Proof.
  introv tsp tsts.
  apply type_sys_props4_implies_type_sys_props in tsp.
  eapply type_sys_props_ts_uv2; eauto.
Qed.

Lemma type_family_ext_sym {o} :
  forall ts lib C (T1 T2 : @CTerm o) A v B A' v' B' eqa eqb eqa1 eqb1,
    constructor_inj C
    -> computes_to_valc lib T1 (C A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T1 T2 eqa1 eqb1
    -> type_family_ext C ts lib T2 T1 eqa1 eqb1.
Proof.
  introv cond comp tspa tspb tf.

  pose proof (type_family_ext_implies_in_ext_eqbs
                ts lib C T1 T2 A A' v v' B B' eqa eqa1 eqb eqb1) as eqbs.
  repeat (autodimp eqbs hyp).

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  applydup (cons_inj1 _ cond) in eq; repnd; subst.
  apply (cons_inj2 _ cond) in eq; subst.

  eexists;eexists;eexists;eexists;eexists;eexists; dands; spcast; eauto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; tcsp.
    eapply tygs; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (eqbs lib' e) as eqbs.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply uv in tf3; auto.
    }

    assert (eqa1 lib' e a' a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    pose proof (tf1 a' a e1) as tf1.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a' a e2) as xtspb.
    eapply type_sys_props4_change_per1 in tf1;[|eauto].


    assert (term_equality_symmetric (eqa1 lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa1 lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a a) as e3 by (apply eqas; eauto).
    assert (eqa lib' e a' a') as e4 by (apply eqas; eauto).
    assert (eqa lib' e a a') as e5 by (apply eqas; eauto).

    pose proof (eq_term_equals_sym_tsp
                  ts lib' (eqa lib' e) (eqb lib' e) a a' e3 e5 e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    apply tygs.
    apply tys;auto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;exact q|];auto.
Qed.

Lemma per_func_ext_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    computes_to_valc lib T1 (mkc_function A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T1 T2 equ
    -> per_func_ext ts lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_func_ext in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].
  eapply type_family_ext_sym; eauto 3 with slow.
Qed.

Lemma bcequiv_refl {o} :
  forall lib (b : @BTerm o), bt_wf b -> bcequiv lib b b.
Proof.
  introv wf.
  unfold bcequiv.
  unfold blift.
  destruct b.
  allrw @bt_wf_iff.
  exists l n n; dands; eauto 3 with slow.
  apply cequiv_open_refl; auto.
Qed.
Hint Resolve bcequiv_refl : slow.

Lemma bcequivc_refl {o} :
  forall lib vs (B : @CVTerm o vs),
    bcequivc lib vs B vs B.
Proof.
  introv.
  destruct_cterms; simpl in *.
  unfold bcequivc; simpl; eauto 4 with slow.
Qed.
Hint Resolve bcequivc_refl : slow.

Lemma bcequivc_ext_refl {o} :
  forall lib vs (B : @CVTerm o vs),
    bcequivc_ext lib vs B vs B.
Proof.
  introv ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve bcequivc_ext_refl : slow.

Lemma per_func_ext_sym_rev {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    computes_to_valc lib T1 (mkc_function A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T2 T1 equ
    -> per_func_ext ts lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_func_ext in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].

  eapply type_family_ext_value_respecting_trans3;
    try (exact tspa);
    try (exact tspb); eauto; eauto 3 with slow.
Qed.

Lemma type_sys_props4_change_eq_term_equals1 {o} :
  forall ts lib (A B C : @CTerm o) eqa1 eqa2,
    (eqa1 <=2=> eqa2)
    -> type_sys_props4 ts lib A B eqa1
    -> ts lib A C eqa1
    -> ts lib A C eqa2.
Proof.
  introv eqiff tsp tsts.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tys; auto.
Qed.

Lemma type_sys_props4_sym_change_eq_term_equals1 {o} :
  forall ts lib (A B C : @CTerm o) eqa1 eqa2,
    (eqa1 <=2=> eqa2)
    -> type_sys_props4 ts lib B A eqa1
    -> ts lib A C eqa1
    -> ts lib A C eqa2.
Proof.
  introv eqiff tsp tsts.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum B A C eqa1 eqa2) as q; repeat (autodimp q hyp); tcsp.

  { apply tygs; auto. }

  apply tys; auto.

  pose proof (dum A B C eqa1 eqa1) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma type_family_ext_trans1 {o} :
  forall ts lib C (T T1 T2 : @CTerm o) eqa1 eqb1 eqa2 eqb2 eqa eqb A v B A' v' B',
    constructor_inj C
    -> computes_to_valc lib T (C A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T T2 eqa1 eqb1
    -> type_family_ext C ts lib T1 T eqa2 eqb2
    -> type_family_ext C ts lib T1 T2 eqa2 eqb2.
Proof.
  introv cond comp tspa tspb tfa tfb.

  pose proof (type_family_ext_implies_in_ext_eqbs
                ts lib C T T2 A A' v v' B B' eqa eqa1 eqb eqb1) as eqbs1.
  repeat (autodimp eqbs1 hyp);[].

  pose proof (type_family_ext_value_respecting_trans3
                ts lib C T T T1 A v B A' v' B' A v B eqa eqb eqa2 eqb2) as tfb'.
  repeat (autodimp tfb' hyp); eauto 3 with slow;[].

  pose proof (type_family_ext_implies_in_ext_eqbs
                ts lib C T T1 A A' v v' B B' eqa eqa2 eqb eqb2) as eqbs2.
  repeat (autodimp eqbs2 hyp);[].

  clear tfb'.

  unfold type_family_ext in *; exrepnd; spcast.
  repeat (repeat (computes_to_eqval);
          applydup (cons_inj1 _ cond) in eq; repnd; subst;
          apply (cons_inj2 _ cond) in eq; subst).

  eexists; eexists; eexists; eexists; eexists; eexists;
    dands; spcast; eauto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (tfa3 lib' e) as tfa3.
    pose proof (tfb3 lib' e) as tfb3.
    pose proof (tfa1 lib' e) as tfa1.
    pose proof (tfb1 lib' e) as tfb1.
    simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    pose proof (dum A A0 A'1 (eqa2 lib' e) (eqa1 lib' e)) as q; repeat (autodimp q hyp); tcsp.

  - repeat introv.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (tfa3 lib' e) as tfa3.
    pose proof (tfb3 lib' e) as tfb3.
    pose proof (tfa1 lib' e) as tfa1.
    pose proof (tfb1 lib' e) as tfb1.
    pose proof (eqbs1 lib' e) as eqbs1.
    pose proof (eqbs2 lib' e) as eqbs2.
    simpl in *.

    introv.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas1.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply uv in tfa3; auto.
    }

    assert ((eqa lib' e) <=2=> (eqa2 lib' e)) as eqas2.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs in tfb3.
      apply uv in tfb3; auto.
    }

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa2 lib' e a a) as e1.
    {
      apply eqas2; eapply teet;[apply eqas2;eauto|].
      apply tees; apply eqas2; auto.
    }

    assert (eqa1 lib' e a a') as e2.
    {
      apply eqas1; apply eqas2; auto.
    }

    assert (eqa lib' e a a') as e3.
    {
      apply eqas2; auto.
    }

    pose proof (tfa1 a a' e2) as h1.
    pose proof (tfb1 a a e1) as h2.

    pose proof (eqbs2 a a' e3 e0) as z1.

    pose proof (tspb a a' e3) as q1.
    eapply type_sys_props4_change_per1 in h1;[|exact q1].
    eapply type_sys_props4_change_eq_term_equals1 in h1;[|exact z1|]; eauto;[].

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (dum (B)[[v\\a]] (B0)[[v0\\a]] (B'1)[[v'1\\a']] (eqb2 lib' e a a e1) (eqb2 lib' e a a' e0)) as w.
    repeat (autodimp w hyp); tcsp.
Qed.

Lemma per_func_ext_function_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_function A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T T2 eq2
    -> per_func_ext ts lib T1 T eq1
    -> per_func_ext ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_func_ext in *; exrepnd.
  exists eqa0 eqb0; dands; auto.
  eapply type_family_ext_trans1; eauto 3 with slow.
Qed.

Lemma type_family_ext_trans2 {o} :
  forall ts lib C (T T1 T2 : @CTerm o) eqa1 eqb1 eqa2 eqb2 eqa eqb A v B A' v' B',
    constructor_inj C
    -> computes_to_valc lib T (C A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T T2 eqa1 eqb1
    -> type_family_ext C ts lib T1 T eqa2 eqb2
    -> type_family_ext C ts lib T1 T2 eqa1 eqb1.
Proof.
  introv cond comp tspa tspb tfa tfb.

  pose proof (type_family_ext_implies_in_ext_eqbs
                ts lib C T T2 A A' v v' B B' eqa eqa1 eqb eqb1) as eqbs1.
  repeat (autodimp eqbs1 hyp);[].

  pose proof (type_family_ext_value_respecting_trans3
                ts lib C T T T1 A v B A' v' B' A v B eqa eqb eqa2 eqb2) as tfb'.
  repeat (autodimp tfb' hyp); eauto 3 with slow;[].

  pose proof (type_family_ext_implies_in_ext_eqbs
                ts lib C T T1 A A' v v' B B' eqa eqa2 eqb eqb2) as eqbs2.
  repeat (autodimp eqbs2 hyp);[].

  clear tfb'.

  unfold type_family_ext in *; exrepnd; spcast.
  repeat (repeat computes_to_eqval;
          applydup (cons_inj1 _ cond) in eq; repnd; subst;
          apply (cons_inj2 _ cond) in eq; subst).

  eexists; eexists; eexists; eexists; eexists; eexists;
    dands; spcast; eauto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (tfa3 lib' e) as tfa3.
    pose proof (tfb3 lib' e) as tfb3.
    pose proof (tfa1 lib' e) as tfa1.
    pose proof (tfb1 lib' e) as tfb1.
    simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    pose proof (dum A A0 A'1 (eqa2 lib' e) (eqa1 lib' e)) as q; repeat (autodimp q hyp); tcsp.

  - repeat introv.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (tfa3 lib' e) as tfa3.
    pose proof (tfb3 lib' e) as tfb3.
    pose proof (tfa1 lib' e) as tfa1.
    pose proof (tfb1 lib' e) as tfb1.
    pose proof (eqbs1 lib' e) as eqbs1.
    pose proof (eqbs2 lib' e) as eqbs2.
    simpl in *.

    introv.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas1.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply uv in tfa3; auto.
    }

    assert ((eqa lib' e) <=2=> (eqa2 lib' e)) as eqas2.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs in tfb3.
      apply uv in tfb3; auto.
    }

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa2 lib' e a a) as e1.
    {
      apply eqas2; eapply teet;[apply eqas1;eauto|].
      apply tees; apply eqas1; auto.
    }

    assert (eqa1 lib' e a a') as e2.
    {
      apply eqas1; apply eqas1; auto.
    }

    assert (eqa lib' e a a') as e3.
    {
      apply eqas1; auto.
    }

    pose proof (tfa1 a a' e2) as h1.
    pose proof (tfb1 a a e1) as h2.

    pose proof (eqbs1 a a' e3 e0) as z1.

    pose proof (tspb a a' e3) as q1.
    eapply type_sys_props4_change_per1 in h1;[|exact q1].
    eapply type_sys_props4_change_eq_term_equals1 in h1;[|exact z1|]; eauto;[].

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (dum (B)[[v\\a]] (B0)[[v0\\a]] (B'1)[[v'1\\a']] (eqb2 lib' e a a e1) (eqb1 lib' e a a' e0)) as w.
    repeat (autodimp w hyp); tcsp.
Qed.

Lemma per_func_ext_function_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_function A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T T2 eq2
    -> per_func_ext ts lib T1 T eq1
    -> per_func_ext ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_func_ext in *; exrepnd.
  exists eqa1 eqb1; dands; auto.
  eapply type_family_ext_trans2; eauto 3 with slow.
Qed.

Lemma type_sys_props4_change_per {o} :
  forall ts lib (A B : @CTerm o) eqa eqb,
    (eqa <=2=> eqb)
    -> type_sys_props4 ts lib A B eqa
    -> type_sys_props4 ts lib A B eqb.
Proof.
  introv eqiff tsp.
  dup tsp as backup.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  prove_type_sys_props4 SCase; introv; tcsp.

  - Case "uniquely_valued".
    introv h1.
    apply uv in h1.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "type_symmetric".
    introv h1 h2.
    pose proof (tys B eq') as q; repeat (autodimp q hyp).
    { eapply eq_term_equals_trans; eauto. }
    pose proof (dum B A A eq' eq') as w; repeat (autodimp w hyp); tcsp.
    { apply tygs; auto. }
    repnd.
    pose proof (dum A A T3 eq' eqb) as z; repeat (autodimp z hyp); tcsp.

  - Case "type_value_respecting".
    introv h ceq.
    pose proof (tyvr T T3) as q; repeat (autodimp q hyp).
    repndors; subst.
    { eapply type_sys_props4_change_eq_term_equals1; eauto. }
    { eapply type_sys_props4_sym_change_eq_term_equals1; eauto. }

  - Case "type_value_respecting_trans".
    introv h ceq q.
    pose proof (tyvrt T T3 T4 eq') as z; repeat (autodimp z hyp).

  - Case "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; tcsp.

  - Case "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; tcsp.
    eapply tet; eauto.

  - Case "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; tcsp.

  - Case "type_mtransitive".
    introv h ts1 ts2.
    pose proof (dum T T3 T4 eq1 eq2); tcsp.
Qed.

Lemma per_func_ext_function_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_function A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T T2 eq2
    -> per_func_ext ts lib T1 T eq1
    -> per_func_ext ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_func_ext_function_trans1 ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_func_ext_function_trans4 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_function A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_func_ext ts lib T T2 eq2
    -> per_func_ext ts lib T1 T eq1
    -> per_func_ext ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_func_ext_function_trans2 ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma implies_eq_term_equals_per_union_bar {p} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 eqb1 eqb2 : lib-per(lib,p)),
    all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqb1 lib' x) <=2=> (eqb2 lib' x))
    -> (per_union_eq_bar lib eqa1 eqb1) <=2=> (per_union_eq_bar lib eqa2 eqb2).
Proof.
  introv eqta eqtb; introv.
  unfold per_union_eq_bar; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (h0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as h0; simpl in *.
    pose proof (eqta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqta; simpl in *.
    pose proof (eqtb lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqtb; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *.
    repndors; exrepnd;[left|right];
      eexists; eexists; dands; eauto;
        try (complete (apply eqta; auto));
        try (complete (apply eqtb; auto)).

  - exists (intersect_bars bar bar0).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (h0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as h0; simpl in *.
    pose proof (eqta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqta; simpl in *.
    pose proof (eqtb lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqtb; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *.
    repndors; exrepnd;[left|right];
      eexists; eexists; dands; eauto;
        try (complete (apply eqta; auto));
        try (complete (apply eqtb; auto)).
Qed.

Lemma per_union_eq_bar_symmetric {p} :
  forall lib (bar : BarLib lib) (eqa eqb : lib-per(lib,p)) t1 t2,
    all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqb lib' x))
    -> per_union_eq_bar lib eqa eqb t1 t2
    -> per_union_eq_bar lib eqa eqb t2 t1.
Proof.
  introv tes tet per.
  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *.
  exrepnd; exists (intersect_bars bar bar0); introv br ext; introv; simpl in *; exrepnd.
  pose proof (per0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as per0; simpl in *.
  pose proof (tes lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tes; simpl in *.
  pose proof (tet lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tet; simpl in *.
  repndors; exrepnd;[left|right]; eexists; eexists; dands; eauto.
Qed.

Lemma per_union_eq_bar_transitive {p} :
  forall lib (bar : BarLib lib) (eqa eqb : lib-per(lib,p)) t1 t2 t3,
    all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqb lib' x))
    -> per_union_eq_bar lib eqa eqb t1 t2
    -> per_union_eq_bar lib eqa eqb t2 t3
    -> per_union_eq_bar lib eqa eqb t1 t3.
Proof.
  introv teta tetb pera perb.
  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *.
  exrepnd.
  exists (intersect3bars bar bar0 bar1); introv br ext; introv.
  simpl in *; exrepnd.

  pose proof (pera0 lib3 br5 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br2) x) as q; simpl in q.
  pose proof (perb0 lib0 br4 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br6) x) as h; simpl in h.
  pose proof (teta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as teta; simpl in *.
  pose proof (tetb lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tetb; simpl in *.
  repndors; exrepnd; ccomputes_to_eqval.

  - left; eexists; eexists; dands; spcast; eauto.

  - right; eexists; eexists; dands; spcast; eauto.
Qed.

Lemma ccequivc_ext_inl {o} :
  forall lib (T T' : @CTerm o) a,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_inl a)
    -> {a' : CTerm ,
        ccomputes_to_valc lib T' (mkc_inl a')
        # ccequivc_ext lib a a' }.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_inl in ceq';[|eauto]; exrepnd.
  exists b; dands; spcast; auto.

  introv ext.
  pose proof (ceq lib' ext) as c; simpl in c; spcast.

  pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_inl a) comp) as w.
  pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_inl b) ceq'1) as z.
  eapply cequivc_mkc_inl in c;[|eauto]; exrepnd.
  computes_to_eqval; auto.
Qed.

Lemma ccequivc_ext_inr {o} :
  forall lib (T T' : @CTerm o) a,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_inr a)
    -> {a' : CTerm ,
        ccomputes_to_valc lib T' (mkc_inr a')
        # ccequivc_ext lib a a' }.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_inr in ceq';[|eauto]; exrepnd.
  exists b; dands; spcast; auto.

  introv ext.
  pose proof (ceq lib' ext) as c; simpl in c; spcast.

  pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_inr a) comp) as w.
  pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_inr b) ceq'1) as z.
  eapply cequivc_mkc_inr in c;[|eauto]; exrepnd.
  computes_to_eqval; auto.
Qed.

Lemma per_union_eq_bar_cequiv {p} :
  forall lib (bar1 bar2 : BarLib lib) (eqa eqb : lib-per(lib,p)) t1 t2,
    all_in_bar_ext bar1 (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> all_in_bar_ext bar2 (fun lib' x => term_equality_respecting lib' (eqb lib' x))
    -> all_in_bar_ext bar1 (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar2 (fun lib' x => term_equality_symmetric (eqb lib' x))
    -> all_in_bar_ext bar1 (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar2 (fun lib' x => term_equality_transitive (eqb lib' x))
    -> ccequivc_ext lib t1 t2
    -> per_union_eq_bar lib eqa eqb t1 t1
    -> per_union_eq_bar lib eqa eqb t1 t2.
Proof.
  introv tera terb tesa tesb teta tetb ceq per.

  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *; exrepnd.
  exists (intersect3bars bar1 bar2 bar).
  introv br ext; introv; simpl in *; exrepnd.

  pose proof (tera lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tera; simpl in *.
  pose proof (terb lib0 br4 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br6) x) as terb; simpl in *.
  pose proof (per0 lib3 br5 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br2) x) as per0; simpl in *.
  pose proof (teta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as teta; simpl in *.
  pose proof (tesa lib1 br0 lib'0 (lib_extends_trans ext br3) x) as tesa; simpl in *.
  pose proof (tetb lib0 br4 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br6) x) as tetb; simpl in *.
  pose proof (tesb lib0 br4 lib'0 (lib_extends_trans (lib_extends_trans ext br1) br6) x) as tesb; simpl in *.
  apply (lib_extends_preserves_ccequivc_ext _ lib'0) in ceq; eauto 4 with slow;[].
  spcast.

  repndors; exrepnd; spcast; computes_to_eqval;[left|right].

  { eapply ccequivc_ext_inl in ceq;[|eauto]; exrepnd.
    eexists; eexists; dands; spcast; eauto. }

  { eapply ccequivc_ext_inr in ceq;[|eauto]; exrepnd.
    eexists; eexists; dands; spcast; eauto. }
Qed.

Lemma approx_decomp_union {o} :
  forall lib (a b c d : @NTerm o),
    approx lib (mk_union a b) (mk_union c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_union; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_union_iff in Hyp1.
    applydup @isprogram_union_iff in Hyp0.
    repnd.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd.
    applydup @approx_relates_only_progs in Hyp; repnd.
    applydup @approx_relates_only_progs in Hyp0; repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (lia;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_union {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib (mk_union a b) (mk_union c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_union lib a b c d); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_union lib c d a b); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_union {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib (mkc_union a b) (mkc_union c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_union.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_union in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union1 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union2 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma all_in_bar_type_sys_props4_sym {o} :
  forall ts lib (bar : BarLib lib) (A B : @CTerm o) eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => type_sys_props4 ts lib B A eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  apply type_sys_props4_sym; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_sym : slow.

Lemma all_in_bar_type_sys_props4_implies_ts_sym2 {o} :
  forall ts lib (bar : BarLib lib) (A B C : @CTerm o) eqa eqb,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqb)
    -> all_in_bar bar (fun lib => ts lib C A eqb).
Proof.
  introv tsp tsts br ext; simpl in *; exrepnd.
  pose proof (tsp lib' br lib'0) as tsp; simpl in *; autodimp tsp hyp; eauto 3 with slow.
  pose proof (tsts lib' br lib'0) as tsts; simpl in *; autodimp tsts hyp; eauto 3 with slow.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa2).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
Qed.

Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 A2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa2).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 eqa2) in w; tcsp.
Qed.

Lemma all_in_bar_type_sys_props4_trans3 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa1 eqa2,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa1)
    -> all_in_bar bar (fun lib => ts lib A D eqa2)
    -> all_in_bar bar (fun lib => ts lib C D eqa).
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa1) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa2) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa eqa) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_type_sys_props4_trans4 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa1 eqa2,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa1)
    -> all_in_bar bar (fun lib => ts lib A D eqa2)
    -> all_in_bar bar (fun lib => ts lib C D eqa1).
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa1) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa2) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa1 eqa2) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_type_sys_props4_trans5 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa1 eqa2,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa1)
    -> all_in_bar bar (fun lib => ts lib A D eqa2)
    -> all_in_bar bar (fun lib => ts lib C D eqa2).
Proof.
  introv allts alla allb br ext.
  pose proof (allts lib' br lib'0 ext) as allts.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C eqa eqa1) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D eqa eqa2) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A eqa eqa) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D eqa1 eqa2) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma per_product_eq_bar_sym {o} :
  forall lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) (t1 t2 : @CTerm o),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall (a1 a2 : CTerm) (e : eqa lib' x a1 a2),
                           term_equality_symmetric (eqb lib' x a1 a2 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall (a1 a2 : CTerm) (e1 : eqa lib' x a1 a2) (e2 : eqa lib' x a2 a1),
                           (eqb lib' x a1 a2 e1) <=2=> (eqb lib' x a2 a1 e2))
    -> per_product_eq_bar lib eqa eqb t1 t2
    -> per_product_eq_bar lib eqa eqb t2 t1.
Proof.
  introv syma symb symb2 per.
  allunfold @per_product_eq_bar; exrepnd.
  exists bar.
  introv b e; repeat introv.
  pose proof (per0 lib' b lib'0 e x) as per0; simpl in *.
  pose proof (syma lib'0 x) as syma; simpl in *.
  pose proof (symb lib'0 x) as symb; simpl in *.
  pose proof (symb2 lib'0 x) as symb2; simpl in *.

  unfold per_product_eq in *; exrepnd.

  dup e0 as xx.
  apply syma in xx.
  eexists; eexists; eexists; eexists; exists xx; dands; eauto.

  apply (symb2 a a' e0 xx).
  apply symb; auto.
Qed.

Lemma in_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => term_equality_symmetric (eqa lib)).
Proof.
  introv i ext.
  pose proof (i lib' ext) as i; simpl in i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv i; introv.
  pose proof (i lib' e) as i; simpl in i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric : slow.

Lemma in_ext_type_sys_prop4_implies_in_ext_term_equality_transitive {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => term_equality_transitive (eqa lib)).
Proof.
  introv i ext.
  pose proof (i lib' ext) as i; simpl in i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_type_sys_prop4_implies_in_ext_term_equality_transitive : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv i; introv.
  pose proof (i lib' e) as i; simpl in i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive : slow.

Lemma in_ext_type_sys_prop4_implies_in_ext_term_equality_respecting {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => term_equality_respecting lib (eqa lib)).
Proof.
  introv i ext.
  pose proof (i lib' ext) as i; simpl in i; eauto 3 with slow.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_type_sys_prop4_implies_in_ext_term_equality_respecting : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_respecting {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv i; introv.
  pose proof (i lib' e) as i; simpl in i; eauto 3 with slow.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_respecting : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext lib
           (fun lib =>
              forall a a' (e : eqa lib a a'),
                type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a1 a2 (e : eqa lib a1 a2),
                   term_equality_symmetric (eqb lib a1 a2 e)).
Proof.
  introv i ext; introv.
  pose proof (i lib' ext a1 a2 e) as i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep : slow.

Lemma in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a1 a2 (e : eqa lib' x a1 a2),
              term_equality_symmetric (eqb lib' x a1 a2 e)).
Proof.
  introv i; introv.
  pose proof (i lib' e a1 a2 e0) as i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext lib
           (fun lib =>
              forall a a' (e : eqa lib a a'),
                type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a1 a2 (e : eqa lib a1 a2),
                   term_equality_transitive (eqb lib a1 a2 e)).
Proof.
  introv i ext; introv.
  pose proof (i lib' ext a1 a2 e) as i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep : slow.

Lemma in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a1 a2 (e : eqa lib' x a1 a2),
              term_equality_transitive (eqb lib' x a1 a2 e)).
Proof.
  introv i; introv.
  pose proof (i lib' e a1 a2 e0) as i; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext lib
           (fun lib =>
              forall a a' (e : eqa lib a a'),
                type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a1 a2 (e : eqa lib a1 a2),
                   term_equality_respecting lib (eqb lib a1 a2 e)).
Proof.
  introv i ext; introv.
  pose proof (i lib' ext a1 a2 e) as i; eauto 3 with slow.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep : slow.

Lemma in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' eqa eqb,
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a1 a2 (e : eqa lib' x a1 a2),
              term_equality_respecting lib' (eqb lib' x a1 a2 e)).
Proof.
  introv i; introv.
  pose proof (i lib' e a1 a2 e0) as i; eauto 3 with slow.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals1_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' (eqa : lib-per(lib,o)) eqb,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a1 a2 (e1 : eqa lib' x a1 a2) (e2 : eqa lib' x a2 a1),
                       (eqb lib' x a1 a2 e1) <=2=> (eqb lib' x a2 a1 e2)).
Proof.
  introv tr i; repeat introv.
  pose proof (tr lib' e) as tr; simpl in tr.
  pose proof (i lib' e) as i; simpl in i.
  pose proof (type_sys_props4_implies_eq_term_equals_sym
                ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as k.
  repeat (autodimp k hyp); repnd; tcsp; try apply k.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals1_dep : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals2_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' (eqa : lib-per(lib,o)) eqb,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a1 a2 (e1 : eqa lib' x a1 a2) (e2 : eqa lib' x a1 a1),
                       (eqb lib' x a1 a2 e1) <=2=> (eqb lib' x a1 a1 e2)).
Proof.
  introv tr i; repeat introv.
  pose proof (tr lib' e) as tr; simpl in tr.
  pose proof (i lib' e) as i; simpl in i.
  pose proof (type_sys_props4_implies_eq_term_equals_sym
                ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as k.
  repeat (autodimp k hyp); repnd; tcsp; try apply k0.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals2_dep : slow.

Lemma in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals3_dep {o} :
  forall ts lib v (B : @CVTerm o [v]) v' B' (eqa : lib-per(lib,o)) eqb,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a1 a2 (e1 : eqa lib' x a2 a1) (e2 : eqa lib' x a1 a1),
                       (eqb lib' x a2 a1 e1) <=2=> (eqb lib' x a1 a1 e2)).
Proof.
  introv tr i; repeat introv.
  pose proof (tr lib' e) as tr; simpl in tr.
  pose proof (i lib' e) as i; simpl in i.
  pose proof (type_sys_props4_implies_eq_term_equals_sym
                ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as k.
  repeat (autodimp k hyp); repnd; tcsp; try apply k1.
Qed.
Hint Resolve in_ext_type_sys_props4_dep_implies_in_ext_eq_term_equals3_dep : slow.

Lemma per_product_bar_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    computes_to_valc lib T1 (mkc_product A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T1 T2 equ
    -> per_product_bar ts lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_product_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].
  eapply type_family_ext_sym; eauto 3 with slow.
Qed.

Lemma per_product_bar_sym_rev {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    computes_to_valc lib T1 (mkc_product A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T2 T1 equ
    -> per_product_bar ts lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_product_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].

  eapply type_family_ext_value_respecting_trans3;
    try (exact tspa);
    try (exact tspb); eauto; eauto 3 with slow.
Qed.

Lemma per_product_bar_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_product A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T T2 eq2
    -> per_product_bar ts lib T1 T eq1
    -> per_product_bar ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_product_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto.
  eapply type_family_ext_trans1; eauto 3 with slow.
Qed.

Lemma per_product_bar_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_product A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T T2 eq2
    -> per_product_bar ts lib T1 T eq1
    -> per_product_bar ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_product_bar in *; exrepnd.
  exists eqa1 eqb1; dands; auto.
  eapply type_family_ext_trans2; eauto 3 with slow.
Qed.

Lemma per_product_eq_bar_trans {o} :
  forall lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)) (t1 t2 t3 : @CTerm o),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           term_equality_transitive (eqb lib' x a1 a2 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e1 : eqa lib' x a1 a2) (e : eqa lib' x a1 a1),
                           (eqb lib' x a1 a2 e1) <=2=> (eqb lib' x a1 a1 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e2 : eqa lib' x a2 a1) (e : eqa lib' x a1 a1),
                           (eqb lib' x a2 a1 e2) <=2=> (eqb lib' x a1 a1 e))
    -> per_product_eq_bar lib eqa eqb t1 t2
    -> per_product_eq_bar lib eqa eqb t2 t3
    -> per_product_eq_bar lib eqa eqb t1 t3.
Proof.
  introv syma tra trb refb1 refb2 per1 per2.

  allunfold @per_product_eq_bar; exrepnd.

  exists (intersect_bars bar bar0).
  introv b e; repeat introv.

  pose proof (syma lib'0 x) as syma.
  pose proof (tra lib'0 x) as tra.
  pose proof (trb lib'0 x) as trb.
  pose proof (refb1 lib'0 x) as refb1.
  pose proof (refb2 lib'0 x) as refb2.
  simpl in *; exrepnd.

  pose proof (per2 lib2 b2 lib'0 (lib_extends_trans e b1) x) as per2; simpl in *.
  pose proof (per0 lib1 b0 lib'0 (lib_extends_trans e b3) x) as per0; simpl in *.

  unfold per_product_eq in *; exrepnd.
  ccomputes_to_eqval.

  assert (eqa lib'0 x a0 a') as e' by (eapply tra; eauto).

  exists a0 a' b4 b' e'; sp; try (complete (spcast; sp)).
  assert (eqa lib'0 x a0 a0) as ee1 by (eapply tra; eauto).
  assert (eqa lib'0 x a'0 a'0) as e2 by (eapply tra; eauto).

  generalize (refb1 a'0 a' e0 e2); intro eqt1.
  apply eqt1 in per1.

  generalize (refb2 a'0 a0 e1 e2); intro eqt2.
  apply eqt2 in per1.

  generalize (trb a0 a'0 e1 b4 b'0 b'); intro trb1.
  repeat (autodimp trb1 hyp).
  generalize (refb1 a0 a'0 e1 ee1); intro eqt3.
  generalize (refb1 a0 a' e' ee1); intro eqt4.
  rw eqt3 in trb1.
  rw eqt4; sp.
Qed.

Lemma ccequivc_ext_pair {o} :
  forall lib (T T' : @CTerm o) a b,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_pair a b)
    -> {a' : CTerm , {b' : CTerm ,
        ccomputes_to_valc lib T' (mkc_pair a' b')
        # ccequivc_ext lib a a'
        # ccequivc_ext lib b b' }}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_pair in ceq';[|eauto]; exrepnd.
  exists a' b'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_pair a b) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_pair a' b') ceq'0) as z.
    eapply cequivc_mkc_pair in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_pair a b) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_pair a' b') ceq'0) as z.
    eapply cequivc_mkc_pair in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma per_product_eq_bar_cequivc {o} :
  forall lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           term_equality_respecting lib' (eqb lib' x a1 a2 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e1 : eqa lib' x a1 a2) (e : eqa lib' x a1 a1),
                           eq_term_equals (eqb lib' x a1 a2 e1) (eqb lib' x a1 a1 e))
    -> ccequivc_ext lib t1 t2
    -> per_product_eq_bar lib eqa eqb t1 t1
    -> per_product_eq_bar lib eqa eqb t1 t2.
Proof.
  introv tera terb eqt1 ceq peq.

  allunfold @per_product_eq_bar; exrepnd.
  exists bar.
  introv b e; repeat introv.

  pose proof (peq0 lib' b lib'0 e x) as peq0; simpl in *.
  pose proof (tera lib'0 x) as tera.
  pose proof (terb lib'0 x) as terb.
  pose proof (eqt1 lib'0 x) as eqt1.
  apply (lib_extends_preserves_ccequivc_ext _ lib'0) in ceq; eauto 3 with slow.

  unfold per_product_eq in *; exrepnd; spcast; computes_to_eqval.
  pose proof (ccequivc_ext_pair lib'0 t1 t2 a b0) as k.
  repeat (autodimp k hyp); exrepnd.
  assert (eqa lib'0 x a a') as e' by (apply tera; auto).
  exists a a' b0 b' e'; sp; try (complete (spcast; sp)).
  generalize (eqt1 a a' e' e0); intro eqt.
  apply eqt in peq1.
  generalize (terb a a' e'); intro k.
  apply k; sp; try (spcast; sp).
Qed.

Lemma per_product_bar_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_product A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T T2 eq2
    -> per_product_bar ts lib T1 T eq1
    -> per_product_bar ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_product_bar_trans1 ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_product_bar_trans4 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    computes_to_valc lib T (mkc_product A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_product_bar ts lib T T2 eq2
    -> per_product_bar ts lib T1 T eq1
    -> per_product_bar ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_product_bar_trans2 ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A1 B1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A2 B2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib' => ccequivc_ext lib' A1 A2)
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tsp cl ceq b ext; repeat introv.

  pose proof (tsp lib' b lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' b lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' b lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
  apply uv in ceq; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans : slow.

Lemma all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B1 A1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A2 B2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as h; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  unfold type_equality_respecting_trans in tyvrt.
  apply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; auto;[].
  pose proof (dum A1 B1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.
Qed.

Lemma implies_all_in_bar_ext_intersect_bars_left {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    all_in_bar_ext bar F
    -> all_in_bar_ext (intersect_bars bar bar') F.
Proof.
  introv a i j; introv.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_intersect_bars_left : slow.

Lemma implies_all_in_bar_ext_intersect_bars_right {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    all_in_bar_ext bar F
    -> all_in_bar_ext (intersect_bars bar' bar) F.
Proof.
  introv a i j; introv.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_intersect_bars_right : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_symmetric {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv h b ext ea.
  pose proof (h lib' b lib'0 ext x) as h; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_symmetric : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h b ext ea eb.
  pose proof (h lib' b lib'0 ext x) as h; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
  eapply tet; eauto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_transitive : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_respecting {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv h b ext eq ceq.
  pose proof (h lib' b lib'0 ext x) as h; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_respecting : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A1 B1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A2 B2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => ts lib' A1 B2 (eqa1 lib' x)).
Proof.
  introv tsp cl ceq br ext; repeat introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
  applydup uv in ceq.

  pose proof (dum A1 A1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma implies_all_in_bar_ext_eqorceq_trans_ccequivc {o} :
  forall lib (bar : @BarLib o lib) a b c eqa,
    all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> all_in_bar bar (fun lib => a ~=~(lib) b)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) b c)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a c).
Proof.
  introv tes tet ter alla allb br ext; introv.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext x) as allb; simpl in *.
  pose proof (ter lib' br lib'0 ext x) as ter; simpl in *.
  pose proof (tet lib' br lib'0 ext x) as tet; simpl in *.
  pose proof (tes lib' br lib'0 ext x) as tes; simpl in *.
  eapply eqorceq_trans; eauto.
  right; eauto.
Qed.

Lemma all_in_bar_ext_eqorceq_eq_term_equals {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    all_in_bar_ext bar (fun lib' x => eqorceq lib' (eq1 lib' x) a b)
    -> all_in_bar_ext bar (fun lib' x => (eq1 lib' x) <=2=> (eq2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eq2 lib' x) a b).
Proof.
  introv alla eqiff br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (eqiff lib' br lib'0 ext x) as eqiff; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve all_in_bar_ext_eqorceq_eq_term_equals : slow.

Lemma all_in_bar_ext_eqorceq_eq_term_equals2 {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    all_in_bar_ext bar (fun lib' x => eqorceq lib' (eq1 lib' x) a b)
    -> all_in_bar_ext bar (fun lib' x => (eq2 lib' x) <=2=> (eq1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eq2 lib' x) a b).
Proof.
  introv alla eqiff br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (eqiff lib' br lib'0 ext x) as eqiff; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto]; auto.
Qed.
Hint Resolve all_in_bar_ext_eqorceq_eq_term_equals2 : slow.

Lemma all_in_bar_ext_eqorceq_refl {o} :
  forall lib (bar : @BarLib o lib) eqa a,
    all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a a).
Proof.
  introv br ext; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_eqorceq_refl : slow.

Lemma all_in_bar_ext_type_sys_props_ts_refl_left {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A A (eqa lib' x)).
Proof.
  introv alla br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props_ts_refl_left : slow.

Lemma all_in_bar_ext_type_sys_props_ts_refl_right {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' B B (eqa lib' x)).
Proof.
  introv alla br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props_ts_refl_right : slow.

Lemma all_in_bar_ext_eq_term_equals_refl {o} :
  forall lib (bar : @BarLib o lib) (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqa lib' x)).
Proof.
  introv br ext; introv; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_eq_term_equals_refl : refl.

Lemma all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B1 A1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A2 B2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib' => ccequivc_ext lib' A1 A2)
    -> all_in_bar_ext bar (fun lib' x => ts lib' A1 B2 (eqa1 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  apply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; auto;[].
  pose proof (dum A1 B1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.

  pose proof (dum A1 A1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A1 B1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' B2 A2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
  apply uv in ceq; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A1 B1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' B2 A2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => ts lib' A1 B2 (eqa1 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
  applydup uv in ceq.

  pose proof (dum A1 A1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma implies_all_in_bar_ext_eqorceq_sym {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b A B,
    all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) b a).
Proof.
  introv tes alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext x) as allb; simpl in *.
  pose proof (tes lib' br lib'0 ext x) as tes; simpl in *.
  apply eqorceq_sym; eauto.
Qed.
Hint Resolve implies_all_in_bar_ext_eqorceq_sym : slow.

Lemma all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B1 A1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' B2 A2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
  pose proof (dum A1 B1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B1 A1 (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' B2 A2 (eqa2 lib' x))
    -> all_in_bar bar (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar_ext bar (fun lib' x => ts lib' A1 B2 (eqa1 lib' x)).
Proof.
  introv tsp cl ceq br ext; introv.

  pose proof (tsp lib' br lib'0 ext x) as tsp; simpl in *.
  pose proof (cl lib' br lib'0 ext x) as cl; simpl in *.
  pose proof (ceq lib' br lib'0 ext) as ceq; simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply (tyvrt A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.

  pose proof (dum A1 B1 B2 (eqa1 lib'0 x) (eqa2 lib'0 x)) as q; repeat (autodimp q hyp); repnd.
  pose proof (dum B1 A1 B2 (eqa1 lib'0 x) (eqa1 lib'0 x)) as z; repeat (autodimp z hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_ts_sym {o} :
  forall ts lib (bar : BarLib lib) (A B C : @CTerm o) eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' C A (eqa lib' x)).
Proof.
  introv alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in alla.
  pose proof (allb lib' br lib'0 ext x) as allb; simpl in allb.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_ts_sym : slow.

Lemma all_in_bar_ext_eq_term_equals_sym {o} :
  forall lib (bar : @BarLib o lib) (eqa eqb : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqb lib' x) <=2=> (eqa lib' x)).
Proof.
  introv alla br ext; introv.
  apply eq_term_equals_sym.
  eapply alla; eauto.
Qed.
Hint Resolve all_in_bar_ext_eq_term_equals_sym : sym.

Lemma all_in_bar_ext_eq_term_equals_trans {o} :
  forall lib (bar : @BarLib o lib) (eqa eqb eqc : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqb lib' x) <=2=> (eqc lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqc lib' x)).
Proof.
  introv alla allb br ext; introv.
  eapply eq_term_equals_trans;[eapply alla; eauto|eapply allb;eauto].
Qed.
Hint Resolve all_in_bar_ext_eq_term_equals_trans : trans.

Lemma eq_term_equals_preserves_all_in_bar_ext_term_equality_respecting {o} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa2 lib' x)).
Proof.
  introv eqiff alla br ext ee ceq.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in alla.
  pose proof (eqiff lib' br lib'0 ext x) as eqiff; simpl in eqiff.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_all_in_bar_ext_term_equality_respecting : slow.

Lemma eq_term_equals_preserves_all_in_bar_ext_term_equality_symmetric {o} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa2 lib' x)).
Proof.
  introv eqiff alla br ext ee.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in alla.
  pose proof (eqiff lib' br lib'0 ext x) as eqiff; simpl in eqiff.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_all_in_bar_ext_term_equality_symmetric : slow.

Lemma eq_term_equals_preserves_all_in_bar_ext_term_equality_transitive {o} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa2 lib' x)).
Proof.
  introv eqiff alla br ext ee1 ee2.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in alla.
  pose proof (eqiff lib' br lib'0 ext x) as eqiff; simpl in eqiff.
  apply eqiff in ee1; apply eqiff in ee2; apply eqiff; eapply alla; eauto.
Qed.
Hint Resolve eq_term_equals_preserves_all_in_bar_ext_term_equality_transitive : slow.

Lemma all_in_bar_ext_type_sys_props4_change_eq_term_equals1 {o} :
  forall ts lib (bar : @BarLib o lib) (A B C : @CTerm o) eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa2 lib' x)).
Proof.
  introv allts alla eqpers br ext; introv.
  pose proof (allts lib' br lib'0 ext x) as allts; simpl in *.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (eqpers lib' br lib'0 ext x) as eqpers; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tys; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_trans1 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A D (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' C D (eqa lib' x)).
Proof.
  introv allts alla allb br ext; introv.
  pose proof (allts lib' br lib'0 ext x) as allts.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext x) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C (eqa lib'0 x) (eqa' lib'0 x)) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D (eqa lib'0 x) (eqa' lib'0 x)) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D (eqa lib'0 x) (eqa lib'0 x)) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A D (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' C D (eqa' lib' x)).
Proof.
  introv allts alla allb br ext; introv.
  pose proof (allts lib' br lib'0 ext x) as allts.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext x) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C (eqa lib'0 x) (eqa' lib'0 x)) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D (eqa lib'0 x) (eqa' lib'0 x)) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D (eqa lib'0 x) (eqa' lib'0 x)) as h; repeat (autodimp h hyp); tcsp.
  apply tygs; auto.
Qed.

Lemma implies_all_in_bar_ext_intersect3bars1 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar_ext bar1 F
    -> all_in_bar_ext (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; introv; simpl in *; exrepnd.
  apply (alla lib1); eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_intersect3bars1 : slow.

Lemma implies_all_in_bar_ext_intersect3bars2 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar_ext bar2 F
    -> all_in_bar_ext (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  apply (alla lib0); eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_intersect3bars2 : slow.

Lemma implies_all_in_bar_ext_intersect3bars3 {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar_ext bar3 F
    -> all_in_bar_ext (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  apply (alla lib3); eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_intersect3bars3 : slow.

Lemma intersect_bars_1_2_implies_all_in_bar_ext_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar1 bar2) F
    -> all_in_bar_ext (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_1_2_implies_all_in_bar_ext_intersect3bars : slow.

Lemma intersect_bars_1_3_implies_all_in_bar_ext_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar1 bar3) F
    -> all_in_bar_ext (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_1_3_implies_all_in_bar_ext_intersect3bars : slow.

Lemma intersect_bars_2_3_implies_all_in_bar_ext_intersect3bars {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) F,
    all_in_bar (intersect_bars bar2 bar3) F
    -> all_in_bar (intersect3bars bar1 bar2 bar3) F.
Proof.
  introv alla br ext; simpl in *; exrepnd.
  eapply alla; simpl.
  { eexists; eexists; dands; eauto; eauto 3 with slow. }
  { eauto 3 with slow. }
Qed.
Hint Resolve intersect_bars_2_3_implies_all_in_bar_ext_intersect3bars : slow.

Lemma implies_all_in_bar_ext_eqorceq_trans {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b c A B,
    all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) b c)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a c).
Proof.
  introv tes tet ter alla allb allc br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext x) as allb; simpl in *.
  pose proof (allc lib' br lib'0 ext x) as allc; simpl in *.
  pose proof (ter lib' br lib'0 ext x) as ter; simpl in *.
  pose proof (tes lib' br lib'0 ext x) as tes; simpl in *.
  pose proof (tet lib' br lib'0 ext x) as tet; simpl in *.
  eapply eqorceq_trans; eauto.
Qed.
Hint Resolve implies_all_in_bar_ext_eqorceq_trans : slow.

Lemma all_in_bar_ccequivc_ext {o} :
  forall lib (bar : @BarLib o lib) A,
    all_in_bar bar (fun lib => ccequivc_ext lib A A).
Proof.
  introv br ext; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ccequivc_ext : slow.

Lemma all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 {o} :
  forall ts lib (bar : @BarLib o lib) A B C eqa1 eqa2,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B A (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa2 lib' x)).
Proof.
  introv allts alla eqpers br ext; introv.
  pose proof (allts lib' br lib'0 ext x) as allts; simpl in *.
  pose proof (alla lib' br lib'0 ext x) as alla; simpl in *.
  pose proof (eqpers lib' br lib'0 ext x) as eqpers; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum B A C (eqa1 lib'0 x) (eqa2 lib'0 x)) as q; repeat (autodimp q hyp); tcsp.

  { apply tygs; auto. }

  apply tys; auto.

  pose proof (dum A B C (eqa1 lib'0 x) (eqa1 lib'0 x)) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma all_in_bar_ext_type_sys_props4_sym_trans2 {o} :
  forall ts lib (bar : @BarLib o lib) A B C D eqa eqa',
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' B A (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A C (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A D (eqa' lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' C D (eqa' lib' x)).
Proof.
  introv allts alla allb br ext; introv.
  pose proof (allts lib' br lib'0 ext x) as allts.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext x) as allb.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (dum A A C (eqa lib'0 x) (eqa' lib'0 x)) as q1; repeat (autodimp q1 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A A D (eqa lib'0 x) (eqa' lib'0 x)) as q2; repeat (autodimp q2 hyp).
  { pose proof (dum B A A (eqa lib'0 x) (eqa lib'0 x)) as w; repeat (autodimp w hyp); tcsp.
    apply tygs; auto. }
  repnd.

  pose proof (dum A C D (eqa lib'0 x) (eqa' lib'0 x)) as h; repeat (autodimp h hyp); tcsp.

  pose proof (dum B C A (eqa lib'0 x) (eqa lib'0 x)) as h; repeat (autodimp h hyp); tcsp.
  apply tygs.

  pose proof (dum A B C (eqa lib'0 x) (eqa lib'0 x)) as h; repeat (autodimp h hyp); tcsp.
Qed.

Lemma ccomputes_to_valc_implies_computes_to_valc_ceq_bar {o} :
  forall lib (bar : @BarLib o lib) (a b : @CTerm o),
    (a ===>(lib) b)
    -> a ==b==>(bar) b.
Proof.
  introv comp br ext.
  exists b; dands; spcast; eauto 4 with slow.
Qed.
Hint Resolve ccomputes_to_valc_implies_computes_to_valc_ceq_bar : slow.

Lemma in_ext_ext_implies_all_in_bar_ext_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext_ext lib F
    -> all_in_bar_ext (trivial_bar lib) F.
Proof.
  introv f br ext; introv.
  eapply f.
Qed.

Lemma all_in_bar_ext_trivial_bar_implies_in_ext_ext {o} :
  forall (lib : @library o) F,
    all_in_bar_ext (trivial_bar lib) F
    -> in_ext_ext lib F.
Proof.
  introv f; introv.
  pose proof (f lib' e lib' (lib_extends_refl lib')) as f; simpl in *; apply f.
Qed.

Lemma lib_extends_preserves_ccomputes_to_valc {o} :
  forall {lib lib'} (x : lib_extends lib' lib) (a b : @CTerm o),
    a ===>(lib) b -> a ===>(lib') b.
Proof.
  introv x comp; spcast.
  eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_ccomputes_to_valc : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals {o} :
  forall (ts : cts(o)) lib A B C eqa eqa1 eqa2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => ts lib' A C (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv h w q; introv.
  pose proof (h _ e) as h.
  pose proof (w _ e) as w.
  pose proof (q _ e) as q.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in w.
  apply uv in q.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2 {o} :
  forall (ts : cts(o)) {lib lib'} (ext : lib_extends lib' lib) A B C eqa eqa1 eqa2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa2 lib' x))
    -> in_ext_ext lib' (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv ext h w q; introv.
  pose proof (w _ e) as w.
  pose proof (q _ e) as q.
  pose proof (h _ (lib_extends_trans e ext)) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in w.
  apply uv in q.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma lib_extends_preserves_in_ext_ext {o} :
  forall {lib lib'} (ext : @lib_extends o lib' lib) F,
    in_ext_ext lib F -> in_ext_ext lib' (fun lib'' x => F lib'' (lib_extends_trans x ext)).
Proof.
  introv h; introv.
  eapply h.
Qed.

Definition local_ts_T {o} (ts : cts(o)) (lib : @library o) (T : @CTerm o) :=
  forall (bar : @BarLib o lib) T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

Lemma implies_in_ext_ext_raise_ext_per {o} :
  forall F {lib lib'} (x : lib_extends lib' lib) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => F lib' (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' y => F lib'' (raise_lib_per eqa x lib'' y)).
Proof.
  introv h; introv.
  eapply h.
Qed.
Hint Resolve implies_in_ext_ext_raise_ext_per : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3 {o} :
  forall (ts : cts(o)) {lib lib'} (ext : lib_extends lib' lib) A B C eqa eqa1 eqa2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B A (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa2 lib' x))
    -> in_ext_ext lib' (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv ext h w q; introv.
  pose proof (w _ e) as w.
  pose proof (q _ e) as q.
  pose proof (h _ (lib_extends_trans e ext)) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs in tygt.
  pose proof (dum A C B (eqa1 lib'0 e) (eqa lib'0 (lib_extends_trans e ext))) as h1; repeat (autodimp h1 hyp).
  pose proof (dum A C B (eqa2 lib'0 e) (eqa lib'0 (lib_extends_trans e ext))) as h2; repeat (autodimp h2 hyp).
  repnd.
  apply tygs in h3; apply tygs in h0.
  apply uv in h3; apply uv in h0.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Definition local_ts_T2 {o} (ts : cts(o)) (lib : @library o) (T' : @CTerm o) :=
  forall (bar : @BarLib o lib) T eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

Definition per_bar_eq_bi {o} {lib}
           (bar : @BarLib o lib)
           (eqa : lib-per(lib,o))
           (t1 t2 : CTerm) :=
  exists bar', all_in_bar_ext (intersect_bars bar bar') (fun lib' x => eqa lib' x t1 t2).

Lemma per_bar_eq_iff {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) t1 t2,
    per_bar_eq bar eqa t1 t2
    <=> per_bar_eq_bi bar eqa t1 t2.
Proof.
  introv; unfold per_bar_eq; split; introv h.

  - apply all_in_bar_ext_exists_bar_implies in h; simpl in *; exrepnd.
    exists (bar_of_bar_fam fbar).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (h0 _ br _ ext0 x0 _ br4 _ (lib_extends_trans ext br1) (lib_extends_trans (lib_extends_trans ext br1) (bar_lib_ext _ _ br4))) as h0; simpl in *.
    eapply (lib_per_cond _ eqa); eauto.

  - introv br ext; introv.
    unfold per_bar_eq_bi in *; exrepnd.
    exists (raise_bar bar' x).
    introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (h0 lib'1) as h0; simpl in *; autodimp h0 hyp.
    eexists; eexists; dands; eauto; eauto 3 with slow.
Qed.
