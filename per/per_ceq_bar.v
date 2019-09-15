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


Require Export cequiv_stable.
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

(*(* !!MOVE *)
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
Qed.*)

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
  forall (lib : @library o) (T : @CTerm o) v1 v2,
    T ==o==>(lib) v1
    -> T ==o==>(lib) v2
    -> in_open_bar lib (fun lib => ccequivc lib v1 v2).
Proof.
  introv comp1 comp2.
  unfold computes_to_valc_ceq_open in *.
  eapply in_open_bar_comb; try exact comp1; clear comp1.
  eapply in_open_bar_comb; try exact comp2; clear comp2.
  apply in_ext_implies_in_open_bar; introv ext comp2 comp1; exrepnd.
  computes_to_eqval; spcast.
  eapply cequivc_trans;[apply cequivc_sym;eauto|].
  eapply cequivc_trans;[|eauto]; auto.
Qed.

(*Lemma two_computes_to_valc_ceq_bar_same_bar_implies {o} :
  forall (lib : @library o) (T : @CTerm o) v1 v2,
    T ==o==>(lib) v1
    -> T ==o==>(lib) v2
    -> in_open_bar lib (fun lib => ccequivc lib v1 v2).
Proof.
  introv comp1 comp2.

  simpl in *; exrepnd.
  pose proof (comp1 lib' b lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (comp2 lib' b lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  exrepnd.
  spcast.
  computes_to_eqval.
  apply cequivc_sym in q0.
  eapply cequivc_trans in h0;[|eauto]; auto.
Qed.*)

Lemma ccequivc_ext_ccomputes_to_valc_ext {o} :
  forall lib (T T' : @CTerm o) v,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T v
    -> ccomputes_to_valc_ext lib T' v.
Proof.
  introv ceq comp i.
  applydup comp in i as comp'; exrepnd.
  applydup ceq in i; spcast.
  dup comp'1 as xx.
  eapply cequivc_val in xx;[|eauto]; exrepnd.
  exists w; dands; spcast; eauto 3 with slow.
  eapply cequivc_trans;[eauto|].
  eapply cequivc_trans;[apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto|].
  eapply cequivc_trans;[eauto|].
  apply computes_to_valc_implies_cequivc; auto.
Qed.
Hint Resolve ccequivc_ext_ccomputes_to_valc_ext : slow.

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
  forall (lib : @library o) (a1 a2 b1 b2 : @CTerm o),
    in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2)
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_approx_eq_bar, per_approx_eq.
  split; introv h; exrepnd.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd; dands; spcast; auto.
    eapply approxc_cequivc_trans;[|eauto].
    eapply cequivc_approxc_trans;[apply cequivc_sym;eauto|].
    auto.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd; dands; spcast; auto.
    eapply cequivc_approxc_trans;[eauto|].
    eapply approxc_cequivc_trans;[eauto|].
    apply cequivc_sym; auto.
Qed.

Lemma approx_iff_implies_eq_per_approx_eq_bar {o} :
  forall (lib : @library o) (a1 a2 b1 b2 : @CTerm o),
    in_open_bar lib (fun lib => (a1 ~<~(lib) b1) <=> (a2 ~<~(lib) b2))
    -> ((per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_approx_eq_bar, per_approx_eq.
  split; introv h; exrepnd.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd; dands; auto.
    apply ceq; tcsp.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd; dands; auto.
    apply ceq; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_approx {o} :
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2,
    T ==o==>(lib) (mkc_approx a1 b1)
    -> T ==o==>(lib) (mkc_approx a2 b2)
    -> in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  eapply in_open_bar_comb; eauto; apply in_ext_implies_in_open_bar; introv ext h.
  spcast.
  apply cequivc_decomp_approx in h; repnd; dands; spcast; auto.
Qed.

(*Lemma two_computes_to_valc_ceq_bar_mkc_approx_same_bar {o} :
  forall {lib} (bar : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==o==>(bar) (mkc_approx a1 b1)
    -> T ==b==>(bar) (mkc_approx a2 b2)
    -> all_in_bar bar (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_same_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_approx in q; repnd; dands; spcast; auto.
Qed.*)

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
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2,
    T ==o==>(lib) (mkc_cequiv a1 b1)
    -> T ==o==>(lib) (mkc_cequiv a2 b2)
    -> in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  eapply in_open_bar_comb; eauto; apply in_ext_implies_in_open_bar; introv ext h.
  spcast.
  apply cequivc_decomp_cequiv in h; repnd; dands; spcast; auto.
Qed.

(*Lemma two_computes_to_valc_ceq_bar_mkc_cequiv_same_bar {o} :
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
Qed.*)

Lemma eq_per_cequiv_eq_bar {o} :
  forall (lib : @library o) (a1 a2 b1 b2 : @CTerm o),
    in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2)
    -> ((per_cequiv_eq_bar lib a1 b1) <=2=> (per_cequiv_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_cequiv_eq_bar, per_cequiv_eq.
  split; introv h; exrepnd.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd.

    dands; auto; spcast.
    eapply cequivc_trans;[|eauto].
    eapply cequivc_trans;[apply cequivc_sym;eauto|].
    auto.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd.

    dands; auto; spcast.
    eapply cequivc_trans;[|apply cequivc_sym;eauto].
    eapply cequivc_trans;[eauto|].
    auto.
Qed.

Lemma cequiv_iff_implies_eq_per_cequiv_eq_bar {o} :
  forall (lib : @library o) (a1 a2 b1 b2 : @CTerm o),
    in_open_bar lib (fun lib => (a1 ~=~(lib) b1) <=> (a2 ~=~(lib) b2))
    -> ((per_cequiv_eq_bar lib a1 b1) <=2=> (per_cequiv_eq_bar lib a2 b2)).
Proof.
  introv ceq; introv.
  unfold per_cequiv_eq_bar, per_cequiv_eq.
  split; introv h; exrepnd.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd.
    dands; auto.
    apply ceq; tcsp.

  - apply e_all_in_ex_bar_as in h; apply e_all_in_ex_bar_as.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_comb; try exact ceq; clear ceq.
    apply in_ext_implies_in_open_bar; introv ext ceq h.
    repnd.
    dands; auto.
    apply ceq; tcsp.
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
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==o==>(lib) (mkc_equality a1 b1 A)
    -> T ==o==>(lib) (mkc_equality a2 b2 B)
    -> in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2 # ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  eapply in_open_bar_comb; eauto.
  apply in_ext_implies_in_open_bar; introv ext h.
  spcast.
  apply cequivc_decomp_equality in h; repnd; dands; spcast; auto.
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
  forall (lib : @library o) (T T' : @CTerm o) v,
    ccequivc_ext lib T T'
    -> in_open_bar lib (fun lib => T ===>(lib) v)
    -> T' ==o==>(lib) v.
Proof.
  introv ceq inbar.
  eapply in_open_bar_comb; eauto; clear inbar.
  eapply in_ext_implies_in_open_bar; introv ext inbar.
  eapply ccequivc_ext_ccomputes_to_valc_ext in inbar;
    [|eapply lib_extends_preserves_ccequivc_ext; eauto].
  eexists; dands; eauto; spcast; eauto 3 with slow.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality {o} :
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==o==>(lib) (mkc_equality a1 b1 A)
    -> T ==o==>(lib) (mkc_equality a2 b2 B)
    -> in_open_bar lib (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2 # ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  eapply in_open_bar_comb; eauto; clear comp2.
  eapply in_ext_implies_in_open_bar; introv ext q.
  spcast.
  apply cequivc_decomp_equality in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality1 {o} :
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==o==>(lib) (mkc_equality a1 b1 A)
    -> T ==o==>(lib) (mkc_equality a2 b2 B)
    -> in_open_bar lib (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  eapply in_open_bar_comb; eauto; clear comp2.
  eapply in_ext_implies_in_open_bar; introv ext q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality2 {o} :
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==o==>(lib) (mkc_equality a1 b1 A)
    -> T ==o==>(lib) (mkc_equality a2 b2 B)
    -> in_open_bar lib (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  eapply in_open_bar_comb; eauto; clear comp2.
  eapply in_ext_implies_in_open_bar; introv ext q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_equality3 {o} :
  forall (lib : @library o) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==o==>(lib) (mkc_equality a1 b1 A)
    -> T ==o==>(lib) (mkc_equality a2 b2 B)
    -> in_open_bar lib (fun lib => ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  eapply in_open_bar_comb; eauto; clear comp2.
  eapply in_ext_implies_in_open_bar; introv ext q; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
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

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.

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

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.

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

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp4 uv2 tys2 tyvr2 tyvrt2 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  apply uv1 in tygt2.
  apply tygt2; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_change_lib_extends_bar : slow.

(*Lemma implies_iff_per_eq_eq {o} :
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
Hint Resolve implies_iff_per_eq_eq : slow.*)

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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

(*Lemma eqorceq_implies_iff_per_eq_eq {o} :
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
Hint Resolve eqorceq_implies_iff_per_eq_eq : slow.*)

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
    -> type_equality_respecting_trans1 ts lib T1 T2.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  apply (tyvrt1 A1 A2 B2 eqa2) in w; auto;[].
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  apply (tyvrt1 A1 A2 B2 eqa2) in w; auto;[].
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  split; introv h; apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as.

  { eapply in_open_bar_ext_pres; eauto; introv q; introv; clear h.
    pose proof (eqas lib' e) as eqas.
    pose proof (eqbs lib' e) as eqbs.
    simpl in *.
    dup e0 as e'.
    apply eqas in e'.
    apply (eqbs _ _ e'); tcsp. }

  { eapply in_open_bar_ext_pres; eauto; introv q; introv; clear h.
    pose proof (eqas lib' e) as eqas.
    pose proof (eqbs lib' e) as eqbs.
    simpl in *.
    dup e0 as e'.
    apply eqas in e'.
    apply (eqbs _ _ _ e'); tcsp. }
Qed.

Lemma eq_term_equals_per_product_eq_bar {o} :
  forall lib (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => forall a1 a2 (e1 : eqa1 lib' x a1 a2) (e2 : eqa2 lib' x a1 a2), (eqb1 lib' x a1 a2 e1) <=2=> (eqb2 lib' x a1 a2 e2))
    -> (per_product_eq_bar lib eqa1 eqb1) <=2=> (per_product_eq_bar lib eqa2 eqb2).
Proof.
  introv eqas eqbs; introv.
  unfold per_product_eq_bar.
  split; introv h; apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as.

  { eapply in_open_bar_ext_pres; eauto; introv q; clear h.
    unfold per_product_eq in *; exrepnd.
    dup q3 as xx.
    apply eqas in xx; eauto 3 with slow.
    eexists; eexists; eexists; eexists; exists xx; dands; eauto.
    eapply eqbs; eauto 3 with slow. }

  { eapply in_open_bar_ext_pres; eauto; introv q; clear h.
    unfold per_product_eq in *; exrepnd.
    dup q3 as xx.
    apply eqas in xx; eauto 3 with slow.
    eexists; eexists; eexists; eexists; exists xx; dands; eauto.
    eapply eqbs; eauto 3 with slow. }
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

Definition bapprox {o} lib l1 (t1 : @NTerm o) l2 (t2 : @NTerm o) :=
  blift (approx_open lib) (bterm l1 t1) (bterm l2 t2).

Lemma bcequiv_implies_bapprox {o} :
  forall lib l1 (t1 : @NTerm o) l2 t2,
    bcequiv lib (bterm l1 t1) (bterm l2 t2)
    -> bapprox lib l1 t1 l2 t2 # bapprox lib l2 t2 l1 t1.
Proof.
  introv bc.
  unfold bcequiv, bapprox in *.
  dands.
  { unfold blift in *; exrepnd.
    exists lv nt1 nt2; dands; auto.
    apply olift_cequiv_approx in bc1; tcsp. }
  { unfold blift in *; exrepnd.
    exists lv nt2 nt1; dands; auto.
    apply olift_cequiv_approx in bc1; tcsp. }
Qed.

Lemma isprog_vars_implies_subvars {o} :
  forall l (b : @NTerm o),
    isprog_vars l b
    -> subvars (free_vars b) l.
Proof.
  introv isp.
  apply isprog_vars_eq in isp; tcsp.
Qed.
Hint Resolve isprog_vars_implies_subvars : slow.

Lemma implies_isprogram_product {o} :
  forall (a : @NTerm o) (v : NVar) (b : NTerm),
    isprogram a
    -> isprog_vars [v] b
    -> isprogram (mk_product a v b).
Proof.
  introv ispa ispb.
  apply isprogram_product; eauto 2 with slow.
Qed.
Hint Resolve implies_isprogram_product : slow.

Lemma implies_isprogram_function {o} :
  forall (a : @NTerm o) (v : NVar) (b : NTerm),
    isprogram a
    -> isprog_vars [v] b
    -> isprogram (mk_function a v b).
Proof.
  introv ispa ispb.
  apply isprogram_function; eauto 2 with slow.
Qed.
Hint Resolve implies_isprogram_function : slow.

Lemma implies_approx_product {o} :
  forall lib (A1 A2 : @NTerm o) v1 v2 B1 B2,
    approx lib A1 A2
    -> bapprox lib [v1] B1 [v2] B2
    -> isprog_vars [v1] B1
    -> isprog_vars [v2] B2
    -> approx lib (mk_product A1 v1 B1) (mk_product A2 v2 B2).
Proof.
  introv H1p H2p isp1 isp2.
  applydup @approx_relates_only_progs in H1p; repnd.
  repnd; repeat (prove_approx);sp.
  apply approx_congruence; fold_terms; eauto 2 with slow.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_product {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    cequivc lib A1 A2
    -> bcequivc lib [v1] B1 [v2] B2
    -> cequivc lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2).
Proof.
  unfold cequivc, bcequivc.
  introv H1c H2c.
  destruct_cterms.
  allsimpl.
  apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  apply bcequiv_implies_bapprox in H2c; repnd.
  split; apply implies_approx_product; auto.
Qed.

Lemma implies_approx_function {o} :
  forall lib (A1 A2 : @NTerm o) v1 v2 B1 B2,
    approx lib A1 A2
    -> bapprox lib [v1] B1 [v2] B2
    -> isprog_vars [v1] B1
    -> isprog_vars [v2] B2
    -> approx lib (mk_function A1 v1 B1) (mk_function A2 v2 B2).
Proof.
  introv H1p H2p isp1 isp2.
  applydup @approx_relates_only_progs in H1p; repnd.
  repnd; repeat (prove_approx);sp.
  apply approx_congruence; fold_terms; eauto 3 with slow.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_function {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    cequivc lib A1 A2
    -> bcequivc lib [v1] B1 [v2] B2
    -> cequivc lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  unfold cequivc, bcequivc.
  introv H1c H2c.
  destruct_cterms.
  allsimpl.
  apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  apply bcequiv_implies_bapprox in H2c; repnd.
  split; apply implies_approx_function; auto.
Qed.

Lemma ccequivc_ext_product {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> ccomputes_to_valc_ext lib T' (mkc_product A v B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_function {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_function A v B)
    -> ccomputes_to_valc_ext lib T' (mkc_function A v B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Record constructor_inj {o} (C : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o) :=
  {
    cons_inj : forall lib x y z a b c, cequivc lib (C x y z) (C a b c) -> cequivc lib x a # bcequivc lib [y] z [b] c;
  }.

Lemma constructor_inj_implies_ext {o} :
  forall (C : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o) lib x y z a b c,
    constructor_inj C
    -> ccequivc_ext lib (C x y z) (C a b c)
    -> ccequivc_ext lib x a # bcequivc_ext lib [y] z [b] c.
Proof.
  introv inj ceq; dands; introv ext;
    pose proof (ceq _ ext) as ceq; simpl in *; spcast; apply inj in ceq; tcsp.
Qed.

Lemma constructor_inj_function {o} :
  @constructor_inj o mkc_function.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
  eapply cequivc_mkc_function in h;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; eqconstr h1; tcsp.
Qed.
Hint Resolve constructor_inj_function : slow.

Lemma constructor_inj_product {o} :
  @constructor_inj o mkc_product.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
  eapply cequivc_mkc_product in h;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; eqconstr h1; tcsp.
Qed.
Hint Resolve constructor_inj_product : slow.

Lemma constructor_inj_set {o} :
  @constructor_inj o mkc_set.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
  eapply cequivc_mkc_set in h;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; eqconstr h1; tcsp.
Qed.
Hint Resolve constructor_inj_set : slow.

Lemma type_family_ext_implies_in_ext_eqas {o} :
  forall ts lib C (T T' : @CTerm o) A A' v B eqa1 eqa2 eqb2,
    constructor_inj C
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa1 lib' x))
    -> type_family_ext C ts lib T T' eqa2 eqb2
    -> ccomputes_to_valc_ext lib T (C A v B)
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv cond tsp tf comp; repeat introv.
  pose proof (tsp lib' e) as tsp; simpl in tsp.
  unfold type_family_ext in tf; exrepnd; spcast.
  eapply ccomputes_to_valc_ext_monotone in tf0;[|eauto].
  eapply ccomputes_to_valc_ext_monotone in tf2;[|eauto].
  eapply ccomputes_to_valc_ext_monotone in comp;[|eauto].
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.
  pose proof (tf3 lib' e) as tf3; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A0 A'0 (eqa2 lib' e)) as q; repeat (autodimp q hyp).
  apply uv in q; auto.
Qed.
Hint Resolve type_family_ext_implies_in_ext_eqas : slow.

Lemma type_family_ext_implies_in_ext_eqbs {o} :
  forall ts lib C (T T' : @CTerm o) A1 A2 v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    constructor_inj C
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A1 A2 (eqa1 lib' x))
    -> type_family_ext C ts lib T T' eqa2 eqb2
    -> ccomputes_to_valc_ext lib T (C A1 v1 B1)
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

  eapply ccomputes_to_valc_ext_monotone in tf0;[|eauto].
  eapply ccomputes_to_valc_ext_monotone in tf2;[|eauto].
  eapply ccomputes_to_valc_ext_monotone in comp;[|eauto].
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  pose proof (tf3 lib' e) as tf3; simpl in *.
  pose proof (tf1 lib' e) as tf1; simpl in *.

  clear tspa.

  pose proof (tspb a1 a2 e1) as tsp; clear tspb.

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  pose proof (tf1 a1 a2 e2) as q.
  pose proof (tyvrt1 (substc a1 v1 B1) (substc a1 v B) (substc a2 v' B') (eqb2 lib' e a1 a2 e2)) as w.
  repeat (autodimp w hyp); eauto 3 with slow; try (complete (apply bcequivc_ext1; eauto));[].
  apply uv in w; auto.
Qed.
Hint Resolve type_family_ext_implies_in_ext_eqbs : slow.

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
    ccomputes_to_valc_ext lib T1 (C A1 v1 B1)
    -> ccomputes_to_valc_ext lib T2 (C A2 v2 B2)
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

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvr; eauto 3 with slow.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.

    onedtsp4 uv tys tyvr tyvrt1 tyvrt11 tes tet tevr tygs tygt dum.

    assert (eqa lib' e a' a') as e' by (apply tet with (t2 := a); sp).

    pose proof (tspb a' a' e') as i.

    onedtsp4 uv2 tys2 tyvr2 tyvrt2 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.

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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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

  - Case "type_value_respecting_trans1".
    introv ee ceq tsts.
    repndors; subst; try (complete (eapply tyvrt1; eauto)).

  - Case "type_value_respecting_trans2".
    introv ee ceq tsts.
    repndors; subst; try (complete (eapply tyvrt2; eauto)).

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

  - Case "type_value_respecting_trans1".
    introv ee ceq tsa.
    repdors; subst.

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt1; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt1; eauto.
    }

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt1; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt1; eauto.
    }

  - Case "type_value_respecting_trans2".
    introv ee ceq tsa.
    repdors; subst.

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt2; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt2; eauto.
    }

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt2; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tyvrt2; eauto.
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
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      apply tygs; auto.
    }

    {
      pose proof (ftspb a2 a1 e1) as i.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
    ccomputes_to_valc_ext lib T1 (C A1 v1 B1)
    -> ccomputes_to_valc_ext lib T2 (C A2 v2 B2)
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  assert (eqa lib' e a2 a1) as e1 by sp.
  assert (eqa lib' e a1 a1) as e2 by (apply tet with (t2 := a2); sp).
  assert (eqa lib' e a2 a2) as e3 by (apply tet with (t2 := a1); sp).

  apply type_sys_props4_sym; sp.
  apply type_sys_props4_eqb_comm; sp.
Qed.

Lemma type_family_ext_value_respecting_trans1 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> ccomputes_to_valc_ext lib T (C A v B)
    -> ccomputes_to_valc_ext lib T3 (C A1 v1 B1)
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

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  exists A A'0 v v'0 B B'0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 3 with slow.
    eapply lib_extends_preserves_ccequivc_ext; [eauto|].
    eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.

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
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A0 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      eapply lib_extends_preserves_ccequivc_ext; [eauto|].
      eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.
    }

    dup e0 as e1.
    apply eqas in e1.
    pose proof (tspb a a' e1) as tspb.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1;[| |eauto]; auto.
    eapply ccequivc_ext_trans;
      [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
        apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
Qed.

Lemma type_family_ext_value_respecting_trans2 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> ccomputes_to_valc_ext lib T (C A' v' B')
    -> ccomputes_to_valc_ext lib T3 (C A1 v1 B1)
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

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  exists A' A'0 v' v'0 B' B'0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 3 with slow.
    eapply lib_extends_preserves_ccequivc_ext; [eauto|].
    eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A' A0 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      { eapply lib_extends_preserves_ccequivc_ext; [eauto|].
        eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto. }
      pose proof (dum A' A A'0 (eqa lib' e) (eqa1 lib' e)) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' e a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tet;[|apply tes; apply eqas;exact e0].
      apply eqas; auto.
    }

    pose proof (tf1 a a' e0) as etf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceqb; auto.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a a e2) as etspb.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 (B')[[v'\\a]] (B0)[[v0\\a]] (B'0)[[v'0\\a']] (eqb1 lib' e a a' e0)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    eapply ccequivc_ext_trans;
      [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
        apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_transitive : slow.

Lemma type_family_ext_value_respecting_trans3 {o} :
  forall ts lib C (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    constructor_inj C
    -> ccomputes_to_valc_ext lib T (C A v B)
    -> ccomputes_to_valc_ext lib T3 (C A1 v1 B1)
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

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  exists A A0 v v0 B B0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 3 with slow.
    eapply lib_extends_preserves_ccequivc_ext; [eauto|].
    eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A'0 A0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      eapply lib_extends_preserves_ccequivc_ext; [eauto|].
      eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.
    }

    assert (eqa1 lib' e a' a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tet;[|apply eqas;eauto]; apply tes; apply eqas; auto.
    }

    pose proof (tf1 a' a e1) as atf1.
    dup ceqb as aceqb.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in aceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in aceqb; auto.

    dup e0 as e2.
    apply eqas in e2.
    pose proof (tspb a a' e2) as atspb.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 (B)[[v\\a]] (B'0)[[v'0\\a]] (B0)[[v0\\a']] (eqb1 lib' e a' a e1)) as q.
    repeat (autodimp q hyp).

    {
      eapply ccequivc_ext_trans;
        [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
          apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
    }

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

        onedtsp4 uv2 tys2 tyvr2 tyvrt21 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt21 (B)[[v\\a']] (B'0)[[v'0\\a']] (B0)[[v0\\a]] (eqb1 lib' e a a' e0)) as z.
        repeat (autodimp z hyp).

        {
          eapply ccequivc_ext_trans;
            [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
              apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
        }

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
    -> ccomputes_to_valc_ext lib T (C A' v' B')
    -> ccomputes_to_valc_ext lib T3 (C A1 v1 B1)
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

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  exists A' A0 v' v0 B' B0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 3 with slow.
    eapply lib_extends_preserves_ccequivc_ext; [eauto|].
    eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A' A'0 A0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
      { eapply lib_extends_preserves_ccequivc_ext; [eauto|].
        eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym]; eauto. }
      pose proof (dum A' A A0 (eqa lib' e) (eqa1 lib' e)) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' e a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tet;[apply eqas;exact e0|].
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a) as e2.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' e a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 (B')[[v'\\a]] (B'0)[[v'0\\a]] (B0)[[v0\\a']] (eqb1 lib' e a' a e2)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.

    {
      eapply ccequivc_ext_trans;
        [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
          apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
    }

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

        onedtsp4 uv2 tys2 tyvr2 tyvrt21 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt21 (B')[[v'\\a']] (B'0)[[v'0\\a']] (B0)[[v0\\a]] (eqb1 lib' e a a' e0)) as u.
        repeat (autodimp u hyp);[|].

        {
          eapply ccequivc_ext_trans;
            [|eapply lib_extends_preserves_ccequivc_ext; [eauto|];
              apply ccequivc_ext_sym;apply bcequivc_ext1; eauto];auto.
        }

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_symmetric : slow.

Lemma type_sys_props4_implies_term_equality_respecing {o} :
  forall lib ts (A B : @CTerm o) (eqa : per(o)),
    type_sys_props4 ts lib A B eqa -> term_equality_respecting lib eqa.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_respecing : slow.

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

Lemma type_sys_props4_implies_type_equality_respecting_trans1 {o} :
  forall ts lib (A B : @CTerm o) per,
    type_sys_props4 ts lib A B per
    -> type_equality_respecting_trans1 ts lib A B.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; tcsp.
Qed.

Lemma type_sys_props4_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (A B : @CTerm o) per,
    type_sys_props4 ts lib A B per
    -> type_equality_respecting_trans2 ts lib A B.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; tcsp.
Qed.

Lemma type_family_ext_sym {o} :
  forall ts lib C (T1 T2 : @CTerm o) A v B A' v' B' eqa eqb eqa1 eqb1,
    constructor_inj C
    -> ccomputes_to_valc_ext lib T1 (C A v B)
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

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  eexists;eexists;eexists;eexists;eexists;eexists; dands; spcast; eauto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; tcsp.
    pose proof (tyvrt1 A A0 A'0 (eqa1 lib' e)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    apply tygs in q.
    pose proof (tyvr A A0) as z; repeat (autodimp z hyp); eauto 3 with slow.
    pose proof (dum A A'0 A0 (eqa1 lib' e) (eqa lib' e)) as w; repeat (autodimp w hyp); tcsp.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    pose proof (eqbs lib' e) as eqbs.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A0 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    assert (eqa1 lib' e a' a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    pose proof (tf1 a' a e1) as tf1.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a' a e2) as xtspb.

    applydup @type_sys_props4_implies_type_equality_respecting_trans1 in xtspb as resp.

    pose proof (resp (substc a' v B) (substc a' v0 B0) (substc a v'0 B'0) (eqb1 lib' e a' a e1)) as w.
    repeat (autodimp w hyp).

    { apply ccequivc_ext_sym.
      eapply lib_extends_preserves_ccequivc_ext;[eauto|].
      apply bcequivc_ext1;auto. }

    eapply type_sys_props4_change_per1 in w;[|eauto].

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

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; tcsp.

    apply tygs in w.

    pose proof (dum (substc a' v B) (substc a v'0 B'0) (substc a' v0 B0) (eqb lib' e a' a e2) (eqb1 lib' e a a' e0)) as z.
    repeat (autodimp z hyp); eauto; tcsp;[].

    apply tys; tcsp.
    { eapply tyvr; tcsp.
      apply ccequivc_ext_sym.
      eapply lib_extends_preserves_ccequivc_ext;[eauto|].
      eapply bcequivc_ext1;auto. }
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;exact q|];auto.
Qed.

Lemma per_func_ext_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    ccomputes_to_valc_ext lib T1 (mkc_function A v B)
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
    ccomputes_to_valc_ext lib T1 (mkc_function A v B)
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  pose proof (dum B A C eqa1 eqa2) as q; repeat (autodimp q hyp); tcsp.

  { apply tygs; auto. }

  apply tys; auto.

  pose proof (dum A B C eqa1 eqa1) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma type_family_ext_trans1 {o} :
  forall ts lib C (T T1 T2 : @CTerm o) eqa1 eqb1 eqa2 eqb2 eqa eqb A v B A' v' B',
    constructor_inj C
    -> ccomputes_to_valc_ext lib T (C A v B)
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

  computes_to_eqval_ext.
  hide_hyp tfb2.
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.
  apply constructor_inj_implies_ext in ceq0; auto; repnd.

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

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    pose proof (dum A A0 A'1 (eqa2 lib' e) (eqa1 lib' e)) as q; repeat (autodimp q hyp); tcsp.

    {
      pose proof (tyvrt1 A A'0 A0 (eqa2 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply tygs in q; auto.
    }

    {
      pose proof (tyvrt1 A A1 A'1 (eqa1 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
    }

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
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A1 A'1 (eqa1 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply uv in q; auto.
    }

    assert ((eqa lib' e) <=2=> (eqa2 lib' e)) as eqas2.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A'0 A0 (eqa2 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply uv in q; auto.
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

    applydup @type_sys_props4_implies_type_equality_respecting_trans1 in q1 as resp.

    pose proof (resp (substc a v B) (substc a v1 B1) (substc a' v'1 B'1) (eqb1 lib' e a a' e2)) as w.
    repeat (autodimp w hyp).

    { apply ccequivc_ext_sym.
      eapply lib_extends_preserves_ccequivc_ext;[eauto|].
      apply bcequivc_ext1;auto. }

    eapply type_sys_props4_change_per1 in w;[|exact q1].
    eapply type_sys_props4_change_eq_term_equals1 in w;[|exact z1|]; eauto;[].

    pose proof (resp (substc a v B) (substc a v'0 B'0) (substc a v0 B0) (eqb2 lib' e a a e1)) as z.
    repeat (autodimp z hyp).

    { apply ccequivc_ext_sym.
      eapply ccequivc_ext_trans;
        eapply lib_extends_preserves_ccequivc_ext; try exact e;
          apply bcequivc_ext1;eauto. }

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (dum (B)[[v\\a]] (B0)[[v0\\a]] (B'1)[[v'1\\a']] (eqb2 lib' e a a e1) (eqb2 lib' e a a' e0)) as u.
    repeat (autodimp u hyp); tcsp.
    apply tygs; auto.
Qed.

Lemma per_func_ext_function_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_function A v B)
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
    -> ccomputes_to_valc_ext lib T (C A v B)
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

  computes_to_eqval_ext.
  hide_hyp tfb2.
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.
  apply constructor_inj_implies_ext in ceq0; auto; repnd.

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

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    pose proof (dum A A0 A'1 (eqa2 lib' e) (eqa1 lib' e)) as q; repeat (autodimp q hyp); tcsp.

    {
      pose proof (tyvrt1 A A'0 A0 (eqa2 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply tygs in q; auto.
    }

    {
      pose proof (tyvrt1 A A1 A'1 (eqa1 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
    }

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
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A1 A'1 (eqa1 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply uv in q; auto.
    }

    assert ((eqa lib' e) <=2=> (eqa2 lib' e)) as eqas2.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A'0 A0 (eqa2 lib' e)) as q; repeat (autodimp q hyp).
      { apply ccequivc_ext_sym; eauto 3 with slow. }
      apply uv in q; auto.
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

    applydup @type_sys_props4_implies_type_equality_respecting_trans1 in q1 as resp.

    pose proof (resp (substc a v B) (substc a v1 B1) (substc a' v'1 B'1) (eqb1 lib' e a a' e2)) as w.
    repeat (autodimp w hyp).

    { apply ccequivc_ext_sym.
      eapply lib_extends_preserves_ccequivc_ext;[eauto|].
      apply bcequivc_ext1;auto. }

    eapply type_sys_props4_change_per1 in w;[|exact q1].
    eapply type_sys_props4_change_eq_term_equals1 in w;[|exact z1|]; eauto;[].

    pose proof (resp (substc a v B) (substc a v'0 B'0) (substc a v0 B0) (eqb2 lib' e a a e1)) as z.
    repeat (autodimp z hyp).

    { apply ccequivc_ext_sym.
      eapply ccequivc_ext_trans;
        eapply lib_extends_preserves_ccequivc_ext; try exact e;
          apply bcequivc_ext1;eauto. }

    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (dum (B)[[v\\a]] (B0)[[v0\\a]] (B'1)[[v'1\\a']] (eqb2 lib' e a a e1) (eqb1 lib' e a a' e0)) as xx.
    repeat (autodimp xx hyp); tcsp.
    apply tygs; auto.
Qed.

Lemma per_func_ext_function_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_function A v B)
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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

  - Case "type_value_respecting_trans1".
    introv h ceq q.
    pose proof (tyvrt1 T T3 T4 eq') as z; repeat (autodimp z hyp).

  - Case "type_value_respecting_trans2".
    introv h ceq q.
    pose proof (tyvrt2 T T3 T4 eq') as z; repeat (autodimp z hyp).

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
    ccomputes_to_valc_ext lib T (mkc_function A' v' B')
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
    ccomputes_to_valc_ext lib T (mkc_function A' v' B')
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

Lemma implies_eq_term_equals_per_union_bar {o} :
  forall (lib : @library o) (eqa1 eqa2 eqb1 eqb2 : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_open_bar_ext lib (fun lib' x => (eqb1 lib' x) <=2=> (eqb2 lib' x))
    -> (per_union_eq_bar lib eqa1 eqb1) <=2=> (per_union_eq_bar lib eqa2 eqb2).
Proof.
  introv eqta eqtb; introv.
  unfold per_union_eq_bar; split; introv h; exrepnd;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as.

  - eapply in_open_bar_ext_comb;[|exact eqta]; clear eqta.
    eapply in_open_bar_ext_comb;[|exact eqtb]; clear eqtb.
    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv h eqta eqtb.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *.
    repndors; exrepnd;[left|right];
      eexists; eexists; dands; eauto;
        try (complete (apply eqta; auto));
        try (complete (apply eqtb; auto)).

  - eapply in_open_bar_ext_comb;[|exact eqta]; clear eqta.
    eapply in_open_bar_ext_comb;[|exact eqtb]; clear eqtb.
    eapply in_open_bar_ext_comb;[|exact h]; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv h eqta eqtb.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *.
    repndors; exrepnd;[left|right];
      eexists; eexists; dands; eauto;
        try (complete (apply eqta; auto));
        try (complete (apply eqtb; auto)).
Qed.

Lemma per_union_eq_bar_symmetric {p} :
  forall lib (eqa eqb : lib-per(lib,p)) t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqb lib' x))
    -> per_union_eq_bar lib eqa eqb t1 t2
    -> per_union_eq_bar lib eqa eqb t2 t1.
Proof.
  introv tes tet per.
  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *;
    apply e_all_in_ex_bar_ext_as in per; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_comb;[|exact tes]; clear tes.
  eapply in_open_bar_ext_comb;[|exact tet]; clear tet.
  eapply in_open_bar_ext_comb;[|exact per]; clear per.
  apply in_ext_ext_implies_in_open_bar_ext; introv per tet tes.
  repndors; exrepnd;[left|right]; eexists; eexists; dands; eauto.
Qed.

Lemma implies_approx_inl {o} :
  forall lib (A1 A2 : @NTerm o),
    approx lib A1 A2
    -> approx lib (mk_inl A1) (mk_inl A2).
Proof.
  introv H1p.
  applydup @approx_relates_only_progs in H1p; repnd.
  repnd; repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_inl {o} :
  forall lib (A1 A2 : @CTerm o),
    cequivc lib A1 A2
    -> cequivc lib (mkc_inl A1) (mkc_inl A2).
Proof.
  unfold cequivc, bcequivc.
  introv H1c.
  destruct_cterms.
  allsimpl.
  apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  split; apply implies_approx_inl; auto.
Qed.

Lemma implies_approx_inr {o} :
  forall lib (A1 A2 : @NTerm o),
    approx lib A1 A2
    -> approx lib (mk_inr A1) (mk_inr A2).
Proof.
  introv H1p.
  applydup @approx_relates_only_progs in H1p; repnd.
  repnd; repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_inr {o} :
  forall lib (A1 A2 : @CTerm o),
    cequivc lib A1 A2
    -> cequivc lib (mkc_inr A1) (mkc_inr A2).
Proof.
  unfold cequivc, bcequivc.
  introv H1c.
  destruct_cterms.
  allsimpl.
  apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  split; apply implies_approx_inr; auto.
Qed.

Lemma ccequivc_ext_inl {o} :
  forall lib (T T' : @CTerm o) a,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_inl a)
    -> ccomputes_to_valc_ext lib T' (mkc_inl a).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_inr {o} :
  forall lib (T T' : @CTerm o) a,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_inr a)
    -> ccomputes_to_valc_ext lib T' (mkc_inr a).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma inr_ccomputes_to_valc_ext_inl_false {o} :
  forall lib (a b : @CTerm o),
    (mkc_inr a) ===>(lib) (mkc_inl b) -> False.
Proof.
  introv h.
  pose proof (h _ (lib_extends_refl _)) as h; simpl in h; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; subst.
  eapply cequivc_mkc_inl in h0;[|apply computes_to_valc_refl;eauto 3 with slow].
  exrepnd.
  apply computes_to_valc_isvalue_eq in h0; ginv; eauto 3 with slow; try eqconstr h0.
Qed.

Lemma inl_ccomputes_to_valc_ext_inr_false {o} :
  forall lib (a b : @CTerm o),
    (mkc_inl a) ===>(lib) (mkc_inr b) -> False.
Proof.
  introv h.
  pose proof (h _ (lib_extends_refl _)) as h; simpl in h; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; subst.
  eapply cequivc_mkc_inr in h0;[|apply computes_to_valc_refl;eauto 3 with slow].
  exrepnd.
  apply computes_to_valc_isvalue_eq in h0; ginv; eauto 3 with slow; try eqconstr h0.
Qed.

Lemma ccequivc_ext_inl_inl_implies {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib (mkc_inl a) (mkc_inl b)
    -> ccequivc_ext lib a b.
Proof.
  introv ceq ext; pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  eapply cequivc_mkc_inl in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
  exrepnd.
  apply computes_to_valc_isvalue_eq in ceq1; eauto 3 with slow.
  eqconstr ceq1; auto.
Qed.

Lemma ccequivc_ext_inr_inr_implies {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib (mkc_inr a) (mkc_inr b)
    -> ccequivc_ext lib a b.
Proof.
  introv ceq ext; pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  eapply cequivc_mkc_inr in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
  exrepnd.
  apply computes_to_valc_isvalue_eq in ceq1; eauto 3 with slow.
  eqconstr ceq1; auto.
Qed.

Lemma per_union_eq_bar_transitive {p} :
  forall lib (eqa eqb : lib-per(lib,p)) t1 t2 t3,
    in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqb lib' x))
    -> per_union_eq_bar lib eqa eqb t1 t2
    -> per_union_eq_bar lib eqa eqb t2 t3
    -> per_union_eq_bar lib eqa eqb t1 t3.
Proof.
  introv teta tetb syma symb respa respb pera perb.
  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *.
  apply e_all_in_ex_bar_ext_as in pera; apply e_all_in_ex_bar_ext_as in perb; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_comb;[|exact teta]; clear teta.
  eapply in_open_bar_ext_comb;[|exact tetb]; clear tetb.
  eapply in_open_bar_ext_comb;[|exact syma]; clear syma.
  eapply in_open_bar_ext_comb;[|exact symb]; clear symb.
  eapply in_open_bar_ext_comb;[|exact respa]; clear respa.
  eapply in_open_bar_ext_comb;[|exact respb]; clear respb.
  eapply in_open_bar_ext_comb;[|exact pera]; clear pera.
  eapply in_open_bar_ext_comb;[|exact perb]; clear perb.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb pera respb respa symb syma tetb teta.

  repndors; exrepnd; computes_to_eqval_ext;
    try (complete (eapply ccequivc_ext_inl in ceq;[|apply ccomputes_to_valc_ext_refl; eauto 3 with slow];
                   apply inr_ccomputes_to_valc_ext_inl_false in ceq; tcsp));
    try (complete (eapply ccequivc_ext_inr in ceq;[|apply ccomputes_to_valc_ext_refl; eauto 3 with slow];
                   apply inl_ccomputes_to_valc_ext_inr_false in ceq; tcsp)).

  - apply ccequivc_ext_inl_inl_implies in ceq.
    left; eexists; eexists; dands; eauto.
    apply respa in ceq.

    { eapply teta;[eauto|].
      eapply teta;[|eauto].
      apply syma; auto. }

    { eapply teta;[eauto|].
      apply syma; auto. }

  - apply ccequivc_ext_inr_inr_implies in ceq.
    right; eexists; eexists; dands; eauto.
    apply respb in ceq.

    { eapply tetb;[eauto|].
      eapply tetb;[|eauto].
      apply symb; auto. }

    { eapply tetb;[eauto|].
      apply symb; auto. }
Qed.

Lemma per_union_eq_bar_cequiv {p} :
  forall lib (eqa eqb : lib-per(lib,p)) t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqb lib' x))
    -> ccequivc_ext lib t1 t2
    -> per_union_eq_bar lib eqa eqb t1 t1
    -> per_union_eq_bar lib eqa eqb t1 t2.
Proof.
  introv tera terb tesa tesb teta tetb ceq per.

  unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in *; exrepnd.
  apply e_all_in_ex_bar_ext_as in per; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_comb;[|exact tera]; clear tera.
  eapply in_open_bar_ext_comb;[|exact terb]; clear terb.
  eapply in_open_bar_ext_comb;[|exact tesa]; clear tesa.
  eapply in_open_bar_ext_comb;[|exact tesb]; clear tesb.
  eapply in_open_bar_ext_comb;[|exact teta]; clear teta.
  eapply in_open_bar_ext_comb;[|exact tetb]; clear tetb.
  eapply in_open_bar_ext_comb;[|exact per]; clear per.
  apply in_ext_ext_implies_in_open_bar_ext; introv per tetb teta tesb tesa terb tera.
  apply (lib_extends_preserves_ccequivc_ext _ lib') in ceq; eauto 4 with slow;[].
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
      repeat(destruct n; try (omega;fail); allsimpl);
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

(*Lemma two_computes_to_valc_ceq_bar_mkc_union {o} :
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
Qed.*)

(*Lemma two_computes_to_valc_ceq_bar_mkc_union1 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.*)

(*Lemma two_computes_to_valc_ceq_bar_mkc_union2 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.*)

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 eqa2) in w; tcsp.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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

  apply e_all_in_ex_bar_ext_as in per.
  apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (syma lib' e) as syma; simpl in *.
  pose proof (symb lib' e) as symb; simpl in *.
  pose proof (symb2 lib' e) as symb2; simpl in *.

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
Qed.
Hint Resolve in_ext_type_sys_prop4_implies_in_ext_term_equality_respecting : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_respecting {o} :
  forall ts lib (A A' : @CTerm o) eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv i; introv.
  pose proof (i lib' e) as i; simpl in i; eauto 3 with slow.
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
    ccomputes_to_valc_ext lib T1 (mkc_product A v B)
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
    ccomputes_to_valc_ext lib T1 (mkc_product A v B)
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
    ccomputes_to_valc_ext lib T (mkc_product A v B)
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
    ccomputes_to_valc_ext lib T (mkc_product A v B)
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

Lemma implies_approx_pair {o} :
  forall lib (A1 A2 : @NTerm o) B1 B2,
    approx lib A1 A2
    -> approx lib B1 B2
    -> approx lib (mk_pair A1 B1) (mk_pair A2 B2).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p; repnd.
  applydup @approx_relates_only_progs in H2p; repnd.
  repnd; repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_pair {o} :
  forall lib (A1 A2 : @CTerm o) B1 B2,
    cequivc lib A1 A2
    -> cequivc lib B1 B2
    -> cequivc lib (mkc_pair A1 B1) (mkc_pair A2 B2).
Proof.
  unfold cequivc, bcequivc.
  introv H1c H2c.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  split; apply implies_approx_pair; auto.
Qed.

Lemma ccequivc_ext_pair {o} :
  forall lib (T T' : @CTerm o) a b,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_pair a b)
    -> ccomputes_to_valc_ext lib T' (mkc_pair a b).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma iscvalue_mkc_pair {o} :
  forall (a b : @CTerm o), iscvalue (mkc_pair a b).
Proof.
  introv; destruct_cterms; repeat constructor; simpl.
  { apply closed_if_isprog in i0.
    apply closed_if_isprog in i.
    unfold closed; simpl; rw i0; rw i; simpl; auto. }
  { introv h; repndors; subst; tcsp; apply bt_wf_iff; eauto 3 with slow. }
Qed.
Hint Resolve iscvalue_mkc_pair : slow.

Lemma ccequivc_ext_pair_pair_implies {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_pair a b) (mkc_pair c d)
    -> ccequivc_ext lib a c /\ ccequivc_ext lib b d.
Proof.
  introv ceq; split; introv ext; pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  { eapply cequivc_mkc_pair in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
    exrepnd.
    apply computes_to_valc_isvalue_eq in ceq0; eauto 3 with slow.
    eqconstr ceq0; auto. }
  { eapply cequivc_mkc_pair in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
    exrepnd.
    apply computes_to_valc_isvalue_eq in ceq0; eauto 3 with slow.
    eqconstr ceq0; auto. }
Qed.

Lemma per_product_eq_bar_trans {o} :
  forall lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)) (t1 t2 t3 : @CTerm o),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           term_equality_symmetric (eqb lib' x a1 a2 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           term_equality_transitive (eqb lib' x a1 a2 e))
    -> in_ext_ext lib (fun lib' x =>
                         forall a1 a2 (e : eqa lib' x a1 a2),
                           term_equality_respecting lib' (eqb lib' x a1 a2 e))
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
  introv syma tra respa symb trb respb refb1 refb2 per1 per2.

  allunfold @per_product_eq_bar; exrepnd.

  apply e_all_in_ex_bar_ext_as in per1.
  apply e_all_in_ex_bar_ext_as in per2.
  apply e_all_in_ex_bar_ext_as.

  eapply in_open_bar_ext_pres2;[|exact per1|exact per2].
  clear per1 per2; introv pera perb.

  pose proof (syma  lib' e) as syma.
  pose proof (tra   lib' e) as tra.
  pose proof (respa lib' e) as respa.
  pose proof (symb  lib' e) as symb.
  pose proof (trb   lib' e) as trb.
  pose proof (respb lib' e) as respb.
  pose proof (refb1 lib' e) as refb1.
  pose proof (refb2 lib' e) as refb2.
  simpl in *; exrepnd.

  unfold per_product_eq in *; exrepnd.

  computes_to_eqval_ext.
  apply ccequivc_ext_pair_pair_implies in ceq; repnd.

  assert (eqa lib' e a0 a') as e'.
  { eapply tra;[eauto|].
    eapply tra;[|eauto].
    apply syma.
    apply respa; auto.
    eapply tra;[eauto|]; apply syma; auto. }

  exists a0 a' b0 b' e'; sp; try (complete (spcast; sp)).
  assert (eqa lib' e a0 a0) as ee1 by (eapply tra; eauto).
  assert (eqa lib' e a a) as e2 by (eapply tra; eauto).
  assert (eqa lib' e a0 a) as e3 by (eapply tra; eauto).

  generalize (refb1 a a' e0 e2); intro eqt1.
  apply eqt1 in perb0.

  generalize (refb2 a a0 e3 e2); intro eqt2.
  apply eqt2 in perb0.

  generalize (trb a0 a'0 e1 b0 b'0 b'); intro trb1.
  repeat (autodimp trb1 hyp).

  {
    generalize (refb1 a0 a'0 e1 ee1); intro eqt3.
    apply eqt3.
    generalize (refb1 a0 a e3 ee1); intro eqt4.
    apply eqt4; auto.
    pose proof (trb a0 a e3 b'0 b b') as q; repeat (autodimp q hyp).
    apply symb.
    apply respb; auto.
    pose proof (trb a0 a e3 b b' b) as q; repeat (autodimp q hyp).
    apply symb; auto.
  }

  generalize (refb1 a0 a'0 e1 ee1); intro eqt3.
  generalize (refb1 a0 a' e' ee1); intro eqt4.
  rw eqt3 in trb1.
  rw eqt4; sp.
Qed.

Lemma ccequivc_ext_preserves_ccomputes_to_valc_ext_pair {o} :
  forall lib (t : @CTerm o) a a' b b',
    ccequivc_ext lib a' a
    -> ccequivc_ext lib b' b
    -> t ===>(lib) (mkc_pair a b)
    -> t ===>(lib) (mkc_pair a' b').
Proof.
  introv ceqa ceqb comp ext.
  pose proof (ceqa _ ext) as ceqa.
  pose proof (ceqb _ ext) as ceqb.
  pose proof (comp _ ext) as comp.
  simpl in *; exrepnd; spcast.
  clear dependent lib; rename lib' into lib.
  exists c; dands; spcast; eauto 3 with slow.
  eapply cequivc_trans;[|eauto].
  apply implies_cequivc_pair; auto.
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

  apply e_all_in_ex_bar_ext_as in peq.
  apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto.
  clear peq; introv peq.

  pose proof (tera lib' e) as tera.
  pose proof (terb lib' e) as terb.
  pose proof (eqt1 lib' e) as eqt1.
  apply (lib_extends_preserves_ccequivc_ext _ lib') in ceq; eauto 3 with slow.

  unfold per_product_eq in *; exrepnd; spcast; computes_to_eqval_ext.
  apply ccequivc_ext_pair_pair_implies in ceq0; repnd.
  pose proof (ccequivc_ext_pair lib' t1 t2 a b) as k.
  repeat (autodimp k hyp); exrepnd.
  exists a a' b b' e0; sp; try (complete (spcast; sp)).
  eapply ccequivc_ext_preserves_ccomputes_to_valc_ext_pair; eauto.
Qed.

Lemma per_product_bar_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_product A' v' B')
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
    ccomputes_to_valc_ext lib T (mkc_product A' v' B')
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  apply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; auto;[].
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_symmetric : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h b ext ea eb.
  pose proof (h lib' b lib'0 ext x) as h; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

  apply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; auto;[].
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.
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

  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply (tyvrt1 A1 A2 B2 (eqa2 lib'0 x)) in ceq; tcsp.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

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
  exists lib'0 (lib_extends_refl lib'0).
  introv xt.
  exists b; dands; spcast; eauto 5 with slow.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  forall T' eq eqa,
    (eq <=2=> (per_bar_eq lib eqa))
    -> in_open_bar_ext lib (fun lib' x => ts lib' T T' (eqa lib' x))
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
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
  forall T eq eqa,
    (eq <=2=> (per_bar_eq lib eqa))
    -> in_open_bar_ext lib (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

Definition per_bar_eq_bi {o} {lib}
           (bar : @BarLib o lib)
           (eqa : lib-per(lib,o))
           (t1 t2 : CTerm) :=
  exists bar', all_in_bar_ext (intersect_bars bar bar') (fun lib' x => eqa lib' x t1 t2).

(*Lemma per_bar_eq_iff {o} :
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
Qed.*)

Lemma trans_ccequivc_ext_in_ext_eq_types_implies {o} :
  forall ts lib' lib (A B C D : @CTerm o) eqa eqa',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' C D (eqa lib' x))
    -> ccequivc_ext lib' A C
    -> in_ext_ext lib' (fun lib' x => ts lib' A B (eqa' lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C B (eqa' lib' x)).
Proof.
  introv ext tsp ceq h; introv.
  pose proof (h _ e) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *; spcast.
  apply type_sys_props4_implies_type_equality_respecting_trans1 in tsp.
  eapply tsp; try (left; eauto).
  apply ccequivc_ext_sym;eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_implies2 {o} :
  forall ts lib' lib (A B C D : @CTerm o) eqa eqa',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' C D (eqa lib' x))
    -> ccequivc_ext lib' B A
    -> in_ext_ext lib' (fun lib' x => ts lib' C B (eqa' lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa' lib' x)).
Proof.
  introv ext tsp ceq h; introv.
  pose proof (h _ e) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *; spcast.
  apply type_sys_props4_implies_type_equality_respecting_trans2 in tsp.
  eapply tsp; try (left; eauto).
  apply ccequivc_ext_sym;eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_fam_implies {o} :
  forall ts lib' lib va vb vc vd A B C D
         (eqa : lib-per(lib,o)) (eqa' : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa)) (eqb' : lib-per-fam(lib',eqa'))
         (ext : lib_extends lib' lib),
    in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a vc C) (substc a' vd D) (eqb lib' x a a' e))
    -> bcequivc_ext lib' [va] A [vc] C
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            (eqa' lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a va A) (substc a' vb B) (eqb' lib'' x a a' e))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a vc C) (substc a' vb B) (eqb' lib'' x a a' e)).
Proof.
  introv tsp ceq eqas h; introv.
  pose proof (eqas _ e) as eqas; simpl in *.
  dup e0 as e1; apply eqas in e1.
  pose proof (h _ e a a' e0) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext) a a' e1) as tsp; simpl in *; spcast.
  apply type_sys_props4_implies_type_equality_respecting_trans1 in tsp.
  eapply tsp; try (left; eauto).
  apply ccequivc_ext_sym;eauto 3 with slow.
  eapply lib_extends_preserves_ccequivc_ext;[eauto|].
  apply bcequivc_ext1; eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_fam_implies2 {o} :
  forall ts lib' lib va vb vc vd A B C D
         (eqa : lib-per(lib,o)) (eqa' : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa)) (eqb' : lib-per-fam(lib',eqa'))
         (ext : lib_extends lib' lib),
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (substc a vc C) (substc a' vd D) (eqb lib' x a a' e))
    -> bcequivc_ext lib' [vb] B [va] A
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            (eqa' lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a vc C) (substc a' vb B) (eqb' lib'' x a a' e))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
            ts lib'' (substc a vc C) (substc a' va A) (eqb' lib'' x a a' e)).
Proof.
  introv tsp ceq eqas h; introv.
  pose proof (h _ e a a' e0) as h; simpl in *.
  pose proof (eqas _ e) as eqas; simpl in *.
  dup e0 as e1; apply eqas in e1.
  pose proof (tsp _ (lib_extends_trans e ext) a a' e1) as tsp; simpl in *; spcast.
  apply type_sys_props4_implies_type_equality_respecting_trans2 in tsp.
  eapply tsp; try (left; eauto).
  eapply lib_extends_preserves_ccequivc_ext;[eauto|].
  apply bcequivc_ext1; eauto 3 with slow.
Qed.

Hint Resolve respects_alpha_cequiv : slow.

Lemma disjoint_bv_sub_csub2sub {o} :
  forall t (sub : @CSub o),
    disjoint_bv_sub t (csub2sub sub).
Proof.
  introv i j.
  apply in_csub2sub in i.
  apply closed_if_program in i; rw i in j; simpl in *; tcsp.
Qed.
Hint Resolve disjoint_bv_sub_csub2sub : slow.

Lemma isprog_vars_one_implies_subvars_free_vars_lsubst_var_ren {o} :
  forall v (t : @NTerm o) w,
    isprog_vars [v] t
    -> subvars (free_vars (lsubst t (var_ren [v] [w]))) [w].
Proof.
  introv isp.
  rw subvars_prop; introv i; simpl; left.
  apply eqset_free_vars_disjoint in i; simpl in *.
  apply isprog_vars_implies_subvars in isp.
  rw subvars_eq in isp.
  boolvar; simpl in *.

  {
    apply in_app_iff in i; simpl in *; repndors; tcsp.
    apply in_remove_nvars in i; simpl in *; repnd; tcsp.
    apply isp in i0; simpl in *; tcsp.
  }

  {
    autorewrite with slow in *.
    apply in_remove_nvars in i; repnd; simpl in *.
    apply isp in i0; simpl in *;tcsp.
  }
Qed.
Hint Resolve isprog_vars_one_implies_subvars_free_vars_lsubst_var_ren : slow.

Lemma isprog_vars_one_implies_subset_free_vars_lsubst_var_ren {o} :
  forall v (t : @NTerm o) w,
    isprog_vars [v] t
    -> subset (free_vars (lsubst t (var_ren [v] [w]))) [w].
Proof.
  introv isp.
  apply subvars_eq; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_one_implies_subset_free_vars_lsubst_var_ren : slow.

Lemma sub_find_some_implies_csubst_single {o} :
  forall (t : @NTerm o) sub v u,
    cl_sub sub
    -> subset (free_vars t) [v]
    -> sub_find sub v = Some u
    -> alpha_eq (lsubst t sub) (lsubst t [(v,u)]).
Proof.
  introv clsub ss sf.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  introv i.
  apply ss in i; simpl in i; repndors; subst; tcsp.
  simpl.
  allrw; boolvar; tcsp.
  apply alpha_eq_option_refl.
Qed.

Lemma isprog_vars_implies_subset_free_vars {o} :
  forall v (t : @NTerm o),
    isprog_vars [v] t
    -> subset (free_vars t) [v].
Proof.
  introv isp.
  apply subvars_eq; apply isprog_vars_implies_subvars; auto.
Qed.
Hint Resolve isprog_vars_implies_subset_free_vars : slow.

Lemma ccequivc_ext_implies_bcequivc_ext {o} :
  forall (lib : @library o) v1 t1 v2 t2,
    (forall t, ccequivc_ext lib t1[[v1\\t]] t2[[v2\\t]])
    -> bcequivc_ext lib [v1] t1 [v2] t2.
Proof.
  introv ceq ext.
  spcast.
  destruct_cterms; simpl in *.
  unfold bcequivc; simpl.

  exists [nvarx] (lsubst x0 (var_ren [v1] [nvarx])) (lsubst x (var_ren [v2] [nvarx])).
  dands;
    [|apply alpha_eq_bterm_single_change2; eauto 3 with slow
     |apply alpha_eq_bterm_single_change2; eauto 3 with slow].

  unfold cequiv_open.
  apply olift_iff_oliftp; eauto 3 with slow;[].
  unfold oliftp; dands; eauto 3 with slow;[].
  introv cov1 cov2.

  remember (sub_find (csub2sub sub) nvarx) as b; symmetry in Heqb.
  destruct b.

  {
    eapply cequiv_rw_l_eauto;
      [apply alpha_eq_sym; apply sub_find_some_implies_csubst_single; eauto; eauto 3 with slow|].
    eapply cequiv_rw_r_eauto;
      [apply alpha_eq_sym; apply sub_find_some_implies_csubst_single; eauto; eauto 3 with slow|].

    eapply cequiv_rw_l_eauto;[apply lsubst_nest_single; eauto 3 with slow|].
    eapply cequiv_rw_r_eauto;[apply lsubst_nest_single; eauto 3 with slow|].

    applydup @sub_find_some in Heqb as isn.
    apply in_csub2sub in isn.
    pose proof (ceq (mk_cterm n isn) _ ext) as ceq; simpl in ceq.
    apply cequiv_stable in ceq.
    unfold cequivc in ceq; simpl in ceq; auto.
  }

  {
    assert (free_vars (lsubst x0 (var_ren [v1] [nvarx])) = []) as fv1.
    {
      apply null_iff_nil; introv xx.
      apply cover_vars_eq in cov1; apply subvars_eq in cov1.
      applydup cov1 in xx.
      apply isprog_vars_one_implies_subset_free_vars_lsubst_var_ren in xx; auto.
      simpl in *; repndors; subst; tcsp.
      apply sub_find_none2 in Heqb; rewrite dom_csub_eq in Heqb; tcsp.
    }

    assert (free_vars (lsubst x (var_ren [v2] [nvarx])) = []) as fv2.
    {
      apply null_iff_nil; introv xx.
      apply cover_vars_eq in cov1; apply subvars_eq in cov2.
      applydup cov2 in xx.
      apply isprog_vars_one_implies_subset_free_vars_lsubst_var_ren in xx; auto.
      simpl in *; repndors; subst; tcsp.
      apply sub_find_none2 in Heqb; rewrite dom_csub_eq in Heqb; tcsp.
    }

    repeat (rewrite csubst_trivial;[|allrw;auto]).
    pose proof (ceq mkc_axiom _ ext) as ceq; simpl in ceq.
    apply cequiv_stable in ceq.
    unfold cequivc in ceq; simpl in ceq; auto.

    assert (closed x0) as cl1.
    {
      apply null_iff_nil; introv xx.
      pose proof (eqset_free_vars_disjoint x0 [(v1,vterm nvarx)]) as w.
      unfold var_ren in *; simpl in *.
      rewrite fv1 in w.
      boolvar; simpl in *.

      - pose proof (w nvarx) as w; destruct w as [w' w]; clear w'; simpl in w.
        autodimp w hyp; tcsp; apply in_app_iff; simpl; tcsp.

      - autorewrite with slow in *.
        pose proof (w x1) as w; destruct w as [w' w]; clear w'; simpl in w.
        autodimp w hyp; tcsp.
        apply in_remove_nvars; simpl; dands; tcsp.
        introv w; repndors; subst; tcsp.
    }

    assert (closed x) as cl2.
    {
      apply null_iff_nil; introv xx.
      pose proof (eqset_free_vars_disjoint x [(v2,vterm nvarx)]) as w.
      unfold var_ren in *; simpl in *.
      rewrite fv2 in w.
      boolvar; simpl in *.

      - pose proof (w nvarx) as w; destruct w as [w' w]; clear w'; simpl in w.
        autodimp w hyp; tcsp; apply in_app_iff; simpl; tcsp.

      - autorewrite with slow in *.
        pose proof (w x1) as w; destruct w as [w' w]; clear w'; simpl in w.
        autodimp w hyp; tcsp.
        apply in_remove_nvars; simpl; dands; tcsp.
        introv w; repndors; subst; tcsp.
    }

    eapply cequiv_rw_l_eauto;[apply alpha_eq_sym;apply alpha_eq_lsubst_closed;auto|].
    eapply cequiv_rw_r_eauto;[apply alpha_eq_sym;apply alpha_eq_lsubst_closed;auto|].

    eapply cequiv_rw_l_eauto in ceq;[|apply alpha_eq_lsubst_closed;auto].
    eapply cequiv_rw_r_eauto in ceq;[|apply alpha_eq_lsubst_closed;auto].
    auto.
  }
Qed.

Lemma bcequivc_ext_trans {o} :
  forall (lib : @library o) v1 v2 v3 B1 B2 B3,
    bcequivc_ext lib [v1] B1 [v2] B2
    -> bcequivc_ext lib [v2] B2 [v3] B3
    -> bcequivc_ext lib [v1] B1 [v3] B3.
Proof.
  introv ceq1 ceq2.
  apply ccequivc_ext_implies_bcequivc_ext; introv.
  eapply ccequivc_ext_trans;apply bcequivc_ext1; eauto.
Qed.

Lemma bcequivc_ext_sym {o} :
  forall (lib : @library o) v1 v2 B1 B2,
    bcequivc_ext lib [v1] B1 [v2] B2
    -> bcequivc_ext lib [v2] B2 [v1] B1.
Proof.
  introv ceq.
  apply ccequivc_ext_implies_bcequivc_ext; introv.
  apply ccequivc_ext_sym;apply bcequivc_ext1; eauto.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_sym {o} :
  forall ts lib' lib (A B C : @CTerm o) eqa eqa',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa' lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa' lib' x)).
Proof.
  introv ext tsp h; introv.
  pose proof (h _ e) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *; spcast.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_implies3 {o} :
  forall ts lib' lib (A B C D : @CTerm o) eqa eqa',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' D C (eqa lib' x))
    -> ccequivc_ext lib' A C
    -> in_ext_ext lib' (fun lib' x => ts lib' B A (eqa' lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' B C (eqa' lib' x)).
Proof.
  introv ext tsp ceq h; introv.
  pose proof (h _ e) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *; spcast.
  apply type_sys_props4_sym in tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs.
  eapply tyvrt1; tcsp; try (right; eauto); eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_implies4 {o} :
  forall ts lib' lib (A B C D : @CTerm o) eqa eqa',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' D C (eqa lib' x))
    -> ccequivc_ext lib' B A
    -> in_ext_ext lib' (fun lib' x => ts lib' B C (eqa' lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa' lib' x)).
Proof.
  introv ext tsp ceq h; introv.
  pose proof (h _ e) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *; spcast.
  apply type_sys_props4_sym in tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs.
  eapply tyvrt2; tcsp; try (right; eauto); eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_fam_implies3 {o} :
  forall ts lib' lib va vb vc vd A B C D
         (eqa : lib-per(lib,o)) (eqa' : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa)) (eqb' : lib-per-fam(lib',eqa'))
         (ext : lib_extends lib' lib),
    in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a vd D) (substc a' vc C) (eqb lib' x a a' e))
    -> bcequivc_ext lib' [va] A [vc] C
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            (eqa' lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a vb B) (substc a' va A) (eqb' lib'' x a a' e))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a vb B) (substc a' vc C) (eqb' lib'' x a a' e)).
Proof.
  introv tsp ceq eqas h; introv.
  pose proof (eqas _ e) as eqas; simpl in *.
  dup e0 as e1; apply eqas in e1.
  pose proof (h _ e a a' e0) as h; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext) a a' e1) as tsp; simpl in *; spcast.
  apply type_sys_props4_sym in tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs.
  eapply tyvrt1; tcsp; try (right; eauto); eauto 3 with slow.
  apply ccequivc_ext_sym;eauto 3 with slow.
  eapply lib_extends_preserves_ccequivc_ext;[eauto|].
  apply bcequivc_ext1; eauto 3 with slow.
Qed.

Lemma trans_ccequivc_ext_in_ext_eq_types_fam_implies4 {o} :
  forall ts lib' lib va vb vc vd A B C D
         (eqa : lib-per(lib,o)) (eqa' : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa)) (eqb' : lib-per-fam(lib',eqa'))
         (ext : lib_extends lib' lib),
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           type_sys_props4 ts lib' (substc a vd D) (substc a' vc C) (eqb lib' x a a' e))
    -> bcequivc_ext lib' [vb] B [va] A
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            (eqa' lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
              ts lib'' (substc a vb B) (substc a' vc C) (eqb' lib'' x a a' e))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : eqa' lib'' x a a'),
            ts lib'' (substc a va A) (substc a' vc C) (eqb' lib'' x a a' e)).
Proof.
  introv tsp ceq eqas h; introv.
  pose proof (h _ e a a' e0) as h; simpl in *.
  pose proof (eqas _ e) as eqas; simpl in *.
  dup e0 as e1; apply eqas in e1.
  pose proof (tsp _ (lib_extends_trans e ext) a a' e1) as tsp; simpl in *; spcast.
  apply type_sys_props4_sym in tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs.
  eapply tyvrt2; tcsp; try (right; eauto); eauto 3 with slow.
  eapply lib_extends_preserves_ccequivc_ext;[eauto|].
  apply bcequivc_ext1; eauto 3 with slow.
Qed.

Lemma eq_term_equals_preserves_in_ext_ext_term_equality_respecting {o} :
  forall lib (eqa1 eqa2 : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa2 lib' x)).
Proof.
  introv h w; introv u c.
  pose proof (h _ e) as h; simpl in h.
  pose proof (w _ e) as w; simpl in w.
  apply h; apply w; auto.
  apply h; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A A1
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A A1 B1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
  apply uv in w.
  introv a b.
  apply w in a; apply w.
  eapply tet; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A A1
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A A1 B1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A A1
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A A1 B1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per2 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' B B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 B B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
  eapply tymt in w; try exact tygt; tcsp; repnd.
  apply uv in w.
  introv a b.
  apply w in a; apply w.
  eapply tet; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per2 : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per2 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' B B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 B B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
  eapply tymt in w; try exact tygt; tcsp; repnd; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per2 : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per2 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' B B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 B B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
  eapply tymt in w; try exact tygt; tcsp; repnd; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per2 : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
  apply uv in w.
  introv a b.
  apply w in a; apply w.
  eapply tet; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3 : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3 : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3 {o} :
  forall ts lib lib' (A B A1 B1 : @CTerm o) eqa eqa1,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A1 B1 (eqa1 lib'' x))
    -> ccequivc_ext lib' A B1
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp h ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  pose proof (h _ e) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt tymt.
  pose proof (tyvrt1 A B1 A1 (eqa1 lib'0 e)) as w.
  repeat (autodimp w hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per2 : slow.

Lemma type_family_ext_value_respecting_trans5 {o} :
  forall ts lib C (T T1 T2 : @CTerm o) A v B A' v' B' eqa eqb eqa1 eqb1,
    constructor_inj C
    -> ccomputes_to_valc_ext lib T (C A v B)
    -> ccequivc_ext lib T1 T2
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> type_family_ext C ts lib T T1 eqa1 eqb1
    -> type_family_ext C ts lib T T2 eqa1 eqb1.
Proof.
  introv cond comp1 ceqa tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.

  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; auto; repnd.

  eapply ccequivc_ext_ccomputes_to_valc_ext in ceqa;[|eauto].

  exists A A'0 v v'0 B B'0; dands; spcast; auto.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 3 with slow.

  - repeat introv.
    pose proof (tf3 lib' e) as tf3.
    pose proof (tf1 lib' e) as tf1.
    pose proof (tspa lib' e) as tspa.
    pose proof (tspb lib' e) as tspb.
    simpl in *.

    assert ((eqa lib' e) <=2=> (eqa1 lib' e)) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      pose proof (tyvrt1 A A0 A'0 (eqa1 lib' e)) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    assert (eqa1 lib' e a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
      eapply tet;[|apply tes; apply eqas;exact e0].
      apply eqas; auto.
    }

    pose proof (tf1 a a' e0) as etf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceq; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceq; auto.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a a e2) as etspb.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 (B)[[v\\a]] (B0)[[v0\\a]] (B'0)[[v'0\\a']] (eqb1 lib' e a a' e0)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
Qed.

Lemma type_ceq_sym {o} :
  forall (ts : cts(o)) (lib : @library o) A A' A1 A2 (eqa eqa1 : per(o)),
    ccequivc_ext lib A2 A
    -> type_sys_props4 ts lib A A' eqa
    -> ts lib A1 A2 eqa1
    -> ts lib A2 A1 eqa1.
Proof.
  introv ceq tya tsa.
  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  unfold type_equality_respecting_trans1 in *.
  unfold type_equality_respecting_trans2 in *.

  pose proof (tyvrt1 A A2 A1 eqa1) as tsb.
  repeat (autodimp tsb hyp); eauto 3 with slow;[].

  pose proof (tyvr1 A A2) as tsc; repeat (autodimp tsc hyp); eauto 3 with slow;[].
  apply tygs1 in tsc.
  eapply dum1 in tsb; try exact tsc; tcsp.
Qed.

Lemma in_ext_ext_type_ceq_sym {o} :
  forall ts (lib lib0 : @library o) A A' A1 A2 (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib0,o)),
    lib_extends lib0 lib
    -> ccequivc_ext lib0 A2 A
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts lib' A2 A1 (eqa1 lib' x)).
Proof.
  introv ext ceq tya tsa; introv.
  pose proof (tya lib' (lib_extends_trans e ext)) as tya; simpl in *.
  pose proof (tsa lib' e) as tsa; simpl in *.
  eapply type_ceq_sym; eauto; eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_ceq_sym : slow.

Hint Resolve bcequivc_ext_refl : slow.
Hint Resolve bcequivc_ext_sym : slow.
Hint Resolve bcequivc_ext_trans : slow.
Hint Resolve bcequivc_ext_implies_ccequivc_ext : slow.

Lemma in_ext_ext_type_ceq_sym_fam {o} :
  forall ts (lib lib0 : @library o)
         (ext  : lib_extends lib0 lib)
         A A' v v' B B' v1 B1 v2 B2
         (eqa  : lib-per(lib,o))
         (eqb  : lib-per-fam(lib,eqa,o))
         (eqa1 : lib-per(lib0,o))
         (eqb1 : lib-per-fam(lib0,eqa1,o)),
    bcequivc_ext lib0 [v2] B2 [v] B
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext lib0 (fun lib' x => (eqa1 lib' x) <=2=> (eqa lib' (lib_extends_trans x ext)))
    -> in_ext_ext lib0 (fun lib' x => forall a a' (e : eqa1 lib' x a a'), ts lib' (substc a v1 B1) (substc a' v2 B2) (eqb1 lib' x a a' e))
    -> in_ext_ext lib0 (fun lib' x => forall a a' (e : eqa1 lib' x a a'), ts lib' (substc a v2 B2) (substc a' v1 B1) (eqb1 lib' x a a' e)).
Proof.
  introv ceq tya tyb eqas tsb; introv.
  pose proof (tya lib' (lib_extends_trans e ext)) as tya; simpl in *.
  pose proof (tyb lib' (lib_extends_trans e ext)) as tyb; simpl in *.
  pose proof (eqas lib' e) as eqas; simpl in *.
  pose proof (tsb lib' e) as tsb; simpl in *.

  applydup @type_sys_props4_implies_eq_term_equals_sym in tyb; eauto 3 with slow; repnd;[].
  applydup @type_sys_props4_implies_term_equality_symmetric in tya as syma.
  applydup @type_sys_props4_implies_term_equality_transitive in tya as trana.

  dup e0 as e1.
  apply eqas in e1.
  applydup syma in e1 as e2.
  applydup eqas in e2 as e3.

  pose proof (tsb _ _ e3) as wa.
  pose proof (tyb _ _ e1) as wb.

  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  unfold type_equality_respecting_trans1 in *.
  unfold type_equality_respecting_trans2 in *.

  pose proof (tyvrt1 (substc a v B) (substc a v2 B2) (substc a' v1 B1) (eqb1 lib' e a' a e3)) as wc.
  repeat (autodimp wc hyp); eauto 3 with slow; tcsp.
  { apply ccequivc_ext_sym; eauto 3 with slow. }

  pose proof (tyvr1 (substc a v B) (substc a v2 B2)) as wd.
  repeat (autodimp wd hyp); eauto 3 with slow.
  { apply ccequivc_ext_sym; eauto 3 with slow. }

  apply tygs1 in wd.
  applydup uv1 in wc.
  apply tygs1 in wd.

  assert ((eqb1 lib' e a' a e3) <=2=> (eqb1 lib' e a a' e0)) as eqs.
  { apply uv1 in wc.
    apply eq_term_equals_sym;eapply eq_term_equals_trans;[|exact wc].
    pose proof (tsb _ _ e0) as wb.
    assert (eqa lib' (lib_extends_trans e ext) a' a') as e4.
    { eapply trana; eauto. }
    pose proof (tyb _ _ e4) as we.

    onedtsp4 uv2 tys2 tyvr2 tyvrt2 tyvrt22 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    unfold type_equality_respecting_trans1 in *.
    unfold type_equality_respecting_trans2 in *.

    pose proof (tyvrt2 (substc a' v B) (substc a' v2 B2) (substc a v1 B1) (eqb1 lib' e a a' e0)) as we.
    repeat (autodimp we hyp); eauto 3 with slow; tcsp.
    { apply ccequivc_ext_sym; eauto 3 with slow. }

    pose proof (tyvr2 (substc a' v B) (substc a' v2 B2)) as wf.
    repeat (autodimp wf hyp); eauto 3 with slow.
    { apply ccequivc_ext_sym; eauto 3 with slow. }

    apply uv2 in we.
    apply eq_term_equals_sym; eapply eq_term_equals_trans;[|eauto]; tcsp. }

  eapply tys1 in wd;[|eapply eq_term_equals_trans;[exact wc0|exact eqs] ].
  apply tygs1 in wd.
  eapply dum1 in wc; try exact wd; tcsp.
Qed.
Hint Resolve in_ext_ext_type_ceq_sym_fam : slow.

Lemma in_ext_ext_type_sys_props4_implies_eq_term_equals {o} :
  forall ts (lib lib0 : @library o) (ext : lib_extends lib0 lib) A A' B C eqa eqa0,
    ccequivc_ext lib0 B A
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts lib' C B (eqa0 lib' x))
    -> in_ext_ext lib0 (fun lib' x => (eqa0 lib' x) <=2=> (eqa lib' (lib_extends_trans x ext))).
Proof.
  introv ceq tya tsa; introv.
  pose proof (tya _ (lib_extends_trans e ext)) as tya.
  pose proof (tsa _ e) as tsa; simpl in *.
  onedtsp4 uv1 tys1 tyvr1 tyvrt1 tyvrt11 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  apply ccequivc_ext_sym in ceq.
  apply (lib_extends_preserves_ccequivc_ext lib0 lib') in ceq; auto.
  unfold type_equality_respecting_trans1 in *.
  unfold type_equality_respecting_trans2 in *.
  eapply tyvrt1 in ceq;[| |right;exact tsa]; tcsp.
  apply uv1 in ceq.
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_eq_term_equals : slow.

Lemma in_ext_ext_type_sys_props4_fam_sym {o} :
  forall ts (lib : @library o)
         (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o))
         A A' v B v' B',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e)).
Proof.
  introv tsa tsb; introv.
  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.

  applydup @type_sys_props4_implies_eq_term_equals_sym in tsb; eauto 3 with slow; repnd;[].
  applydup @type_sys_props4_implies_term_equality_symmetric in tsa.
  dup e0 as e1.
  apply tsa0 in e1.
  pose proof (tsb0 a a' e0 e1) as xx.
  pose proof (tsb a' a e1) as yy.

  apply type_sys_props4_sym.
  eapply type_sys_props4_change_per;[|eauto]; auto.
Qed.

Lemma ccomputes_to_valc_ext_implies_computes_valc_ceq_open {o} :
  forall (lib : @library o) a b,
    a ===>(lib) b
    -> a ==o==>(lib) b.
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext.
  exists b; dands; eauto 3 with slow.
  spcast; eauto 3 with slow.
Qed.
Hint Resolve ccomputes_to_valc_ext_implies_computes_valc_ceq_open : slow.

Lemma ccequivc_ext_implies_eqorceq {o} :
  forall (lib : @library o) (eqa : per(o)) a b,
    ccequivc_ext lib a b
    -> eqorceq lib eqa a b.
Proof.
  tcsp.
Qed.
Hint Resolve ccequivc_ext_implies_eqorceq : slow.

Lemma pre_commutes {o} :
  forall lib (a b c d : @CTerm o) (eqa : per(o)),
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib c d
    -> eqa a c
    -> eqa b d.
Proof.
  introv ter tes tet eo1 eo2 e.
  eapply eqorceq_commutes; eauto; eauto 3 with slow.
Qed.

Lemma implies_in_ext_ccequivc_ext {o} :
  forall (lib : @library o) a b,
    ccequivc_ext lib a b
    -> in_ext lib (fun lib' => ccequivc_ext lib' a b).
Proof.
  introv ceq ext; eauto 3 with slow.
Qed.
Hint Resolve implies_in_ext_ccequivc_ext : slow.

Lemma ccomputes_to_valc_ext_implies_in_open_bar {o} :
  forall (lib : @library o) a b,
    a ===>(lib) b
    -> in_open_bar lib (fun lib' => a ===>(lib') b).
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext; eauto 3 with slow.
Qed.
Hint Resolve ccomputes_to_valc_ext_implies_in_open_bar : slow.
