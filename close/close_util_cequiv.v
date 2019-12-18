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


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.
Require Export close_util_bar.


(*Lemma per_cequiv_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_cequiv_bar ts).
Proof.
  unfold uniquely_valued, per_cequiv_bar, eq_term_equals; sp.
  pose proof (two_computes_to_valc_ceq_bar_mkc_cequiv bar0 bar T a0 b0 a b) as q; repeat (autodimp q hyp).
  allrw; sp.
  eapply eq_per_cequiv_eq_bar; eauto.
Qed.
Hint Resolve per_cequiv_bar_uniquely_valued : slow.

Lemma per_cequiv_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_cequiv_bar ts).
Proof.
  unfold type_extensionality, per_cequiv_bar, eq_term_equals; sp.
  exists a b c d; sp; allrw <-; sp.
  exists bar; dands; tcsp.
Qed.
Hint Resolve per_cequiv_bar_type_extensionality : slow.

Lemma per_cequiv_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_cequiv_bar ts).
Proof.
  introv per.
  unfold per_cequiv_bar in *; exrepnd.
  exists c d a b; sp.
  { exists bar; dands; tcsp.
    introv i j; symm; eapply per2; eauto. }
  introv; rw per1; clear per1.

  split; intro h; unfold per_cequiv_eq_bar, per_cequiv_eq in *; exrepnd.

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }
Qed.
Hint Resolve per_cequiv_bar_type_symmetric : slow.

Lemma per_cequiv_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_cequiv_bar ts).
Proof.
  introv per1 per2.
  unfold per_cequiv_bar in *; exrepnd.

  exists a0 b0 c d; sp; spcast; sp.
  exists (intersect_bars bar0 bar).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per5 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per6 lib1) as q; autodimp q hyp.
    pose proof (per3 lib2) as w; autodimp w hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; clear q.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; clear w.
    simpl in *.
    rw z.
    rw <- u.

    pose proof (two_computes_to_valc_ceq_bar_mkc_cequiv bar0 bar T2 c0 d0 a b) as h; repeat (autodimp h hyp).
    pose proof (h lib') as w; simpl in w; autodimp w hyp; clear h;
      [exists lib1 lib2; dands; auto|].
    pose proof (w lib'0 j) as w; simpl in w; repnd; spcast.

    split; introv h; spcast.

    { eapply cequivc_trans;[|eauto].
      eapply cequivc_trans;[apply cequivc_sym;eauto|].
      auto. }

    { eapply cequivc_trans;[|apply cequivc_sym;eauto].
      eapply cequivc_trans;[eauto|].
      auto. }
Qed.
Hint Resolve per_cequiv_bar_type_transitive : slow.

Lemma per_cequiv_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_cequiv_bar ts).
Proof.
  introv per eceq.
  unfold per_cequiv_bar in *; exrepnd.

  pose proof (two_computes_to_valc_ceq_bar_mkc_cequiv_same_bar bar T a b c d) as q.
  repeat (autodimp q hyp).

  exists a b a b.
  dands; auto.

  exists bar; dands; auto;[|introv w z; tcsp];[].

  eapply cequivc_ext_preserves_computes_to_valc_ceq_bar; eauto.
Qed.
Hint Resolve per_cequiv_bar_type_value_respecting : slow.

Lemma per_cequiv_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_cequiv_bar ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_cequiv_bar.
  introv cts i e.
  exrepnd.

  apply i1 in e; apply i1; clear i1.
  unfold per_cequiv_eq_bar, per_cequiv_eq in *; exrepnd.
  exists bar0.
  introv w z.
  pose proof (e0 lib' w lib'0 z) as q; simpl in q; tcsp.
Qed.
Hint Resolve per_cequiv_bar_term_symmetric : slow.

Lemma per_cequiv_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_cequiv_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_cequiv_bar.
  introv cts i e1 e2.
  exrepnd.

  apply i1 in e1; apply i1 in e2; apply i1; clear i1.
  unfold per_cequiv_eq_bar, per_cequiv_eq in *; exrepnd.
  exists (intersect_bars bar1 bar0).
  introv w z.
  simpl in *; exrepnd.
  pose proof (e2 lib1 w0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; tcsp.
  pose proof (e0 lib2 w2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h; tcsp.
Qed.
Hint Resolve per_cequiv_bar_term_transitive : slow.

Lemma per_cequiv_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_cequiv_bar ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_cequiv_bar.
  introv i e c; exrepnd.

  apply i1 in e; apply i1; clear i1.
  unfold per_cequiv_eq_bar, per_cequiv_eq in *; exrepnd.
  exists bar0; introv w z.
  pose proof (e0 lib' w lib'0 z) as q; clear e0; simpl in q.
  repnd; dands; auto.

  pose proof (c lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  spcast.
  eapply cequivc_axiom; eauto.
Qed.
Hint Resolve per_cequiv_bar_term_value_respecting : slow.

Lemma per_cequiv_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_cequiv_bar ts).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_bar_type_system : slow.
*)

Lemma per_bar_per_cequiv_implies_close {o} :
  forall inh (ts : cts(o)) lib T T' eq,
    per_bar inh (per_cequiv inh (close inh ts)) lib T T' eq
    -> close inh ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb; eauto; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv per1.
  apply CL_cequiv; auto.
Qed.

Lemma ccequivc_ext_cequiv {o} :
  forall inh lib (T T' : @CTerm o) a b,
    ccequivc_ext inh lib T T'
    -> ccomputes_to_valc_ext inh lib T (mkc_cequiv a b)
    -> ccomputes_to_valc_ext inh lib T' (mkc_cequiv a b).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma type_equality_respecting_trans1_per_cequiv_bar_implies {o} :
  forall inh (ts : cts(o)) lib T T' a b a' b',
    type_system inh ts
    -> defines_only_universes inh ts
    -> type_monotone inh ts
    -> ccomputes_to_valc_ext inh lib T (mkc_cequiv a b)
    -> ccomputes_to_valc_ext inh lib T' (mkc_cequiv a' b')
    -> type_equality_respecting_trans1 inh (per_bar inh (per_cequiv inh (close inh ts))) lib T T'
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_cequiv_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_bar_per_cequiv_implies {o} :
  forall inh (ts : cts(o)) lib T T' a b c d,
    type_system inh ts
    -> defines_only_universes inh ts
    -> type_monotone inh ts
    -> ccomputes_to_valc_ext inh lib T  (mkc_cequiv a b)
    -> ccomputes_to_valc_ext inh lib T' (mkc_cequiv c d)
    -> type_equality_respecting_trans2 inh (per_bar inh (per_cequiv inh (close inh ts))) lib T T'
    -> type_equality_respecting_trans2 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_cequiv_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_bar_eq_per_cequiv_eq_bar_lib_per {o} :
  forall inh (lib : @library o) a b,
    (per_bar_eq inh lib (per_cequiv_eq_bar_lib_per inh lib a b))
    <=2=> (per_cequiv_eq_bar inh lib a b).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_cequiv_eq_bar.
    apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_cequiv_eq_bar in h.
    eapply in_open_bar_pres; eauto; clear h.
    introv h; introv; simpl in *; tcsp.

  - unfold per_cequiv_eq_bar in h.
    apply in_open_bar_ext_in_open_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_cequiv_eq_bar.
    eapply in_open_bar_pres; eauto; clear h.
    introv h; introv; simpl in *; tcsp.
Qed.

Lemma per_cequiv_uniquely_valued {p} :
  forall inh (ts : cts(p)), uniquely_valued (per_cequiv inh ts).
Proof.
  unfold uniquely_valued, per_cequiv, eq_term_equals; introv cts h q; introv.
  exrepnd.
  computes_to_eqval_ext.
  hide_hyp q2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_cequiv_right in ceq.
  apply cequivc_ext_mkc_cequiv_right in ceq0.
  repnd.
  allrw.
  split; intro w; eapply per_cequiv_eq_bar_respects_ccequivc_ext; try exact w; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_uniquely_valued : slow.

Lemma per_bar_per_cequiv_uniquely_valued {p} :
  forall inh (ts : cts(p)), uniquely_valued (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_cequiv_uniquely_valued : slow.

Lemma per_cequiv_type_extensionality {p} :
  forall inh (ts : cts(p)), type_extensionality (per_cequiv inh ts).
Proof.
  introv per eqiff.
  unfold per_cequiv in *; exrepnd.
  exists a b c d; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve per_cequiv_type_extensionality : slow.

Lemma per_bar_per_cequiv_type_extensionality {p} :
  forall inh (ts : cts(p)), type_extensionality (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_cequiv_type_extensionality : slow.

Lemma per_cequiv_type_symmetric {p} :
  forall inh (ts : cts(p)), type_symmetric (per_cequiv inh ts).
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists c d a b; dands; auto.

  {
    introv ext.
    pose proof (per3 _ ext) as per3; simpl in *.
    allrw; tcsp.
  }

  eapply eq_term_equals_trans;[eauto|].
  apply (cequiv_iff_implies_eq_per_cequiv_eq_bar inh lib).
  apply in_ext_implies_in_open_bar; auto.
Qed.
Hint Resolve per_cequiv_type_symmetric : slow.

Lemma per_bar_per_cequiv_type_symmetric {p} :
  forall inh (ts : cts(p)), type_symmetric (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_type_symmetric : slow.

Lemma ccequivc_ext_implies_iff_ccequivc_ext {o} :
  forall inh lib lib' (a a' b b' : @CTerm o),
    lib_extends inh lib' lib
    -> ccequivc_ext inh lib a a'
    -> ccequivc_ext inh lib b b'
    -> a' ~=~(lib') b' <=> a ~=~(lib') b.
Proof.
  introv ext ceqa ceqb.
  pose proof (ceqa _ ext) as ceqa.
  pose proof (ceqb _ ext) as ceqb.
  simpl in *.
  split; introv h; spcast.
  { eapply cequivc_trans;[exact ceqa|].
    eapply cequivc_trans;[exact h|].
    apply cequivc_sym; auto. }
  { eapply cequivc_trans;[|exact ceqb].
    apply cequivc_sym.
    eapply cequivc_trans;[|exact ceqa].
    apply cequivc_sym; auto. }
Qed.

Lemma per_cequiv_type_transitive {p} :
  forall inh (ts : cts(p)), type_transitive (per_cequiv inh ts).
Proof.
  introv pera perb.
  unfold per_cequiv in *; exrepnd.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_cequiv_right in ceq; repnd.

  exists a0 b0 c d; dands; spcast; auto.

  introv x.
  pose proof (pera3 _ x) as pera3.
  pose proof (perb3 _ x) as perb3.
  simpl in *.
  rw pera3; rw <- perb3.
  eapply ccequivc_ext_implies_iff_ccequivc_ext; eauto.
Qed.
Hint Resolve per_cequiv_type_transitive : slow.

Lemma per_bar_per_cequiv_type_transitive {p} :
  forall inh (ts : cts(p)), type_transitive (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_type_transitive : slow.

Lemma cequivc_implies_ccequivc {o} :
  forall lib (a a' b b' : @CTerm o),
    cequivc lib a a'
    -> cequivc lib b b'
    -> (a ~=~(lib) b) <=> (a' ~=~(lib) b').
Proof.
  introv ceq1 ceq2; split; intro h; spcast; eauto 3 with slow.

  - eapply cequivc_trans;[|eauto].
    eapply cequivc_trans;[apply cequivc_sym;eauto|];auto.

  - eapply cequivc_trans;[eauto|].
    eapply cequivc_trans;[|apply cequivc_sym;eauto];auto.
Qed.
Hint Resolve cequivc_implies_ccequivc : slow.

Lemma per_cequiv_type_value_respecting {p} :
  forall inh (ts : cts(p)), type_value_respecting inh (per_cequiv inh ts).
Proof.
  introv per ceq.
  unfold per_cequiv in *; exrepnd.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_cequiv_right in ceq0; repnd.
  exists a b a b; dands; spcast; auto; eauto 3 with slow.
  introv ext; tcsp.
Qed.
Hint Resolve per_cequiv_type_value_respecting : slow.

Lemma per_bar_per_cequiv_type_value_respecting {p} :
  forall inh (ts : cts(p)), type_value_respecting inh (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_type_value_respecting : slow.

Lemma type_equality_respecting_trans1_per_bar_per_cequiv_implies {o} :
  forall inh (ts : cts(o)) lib T T' a b c d,
    type_system inh ts
    -> defines_only_universes inh ts
    -> type_monotone inh ts
    -> ccomputes_to_valc_ext inh lib T  (mkc_cequiv a b)
    -> ccomputes_to_valc_ext inh lib T' (mkc_cequiv c d)
    -> type_equality_respecting_trans1 inh (per_bar inh (per_cequiv inh (close inh ts))) lib T T'
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_cequiv_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_cequiv in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.
Qed.

Lemma per_cequiv_term_symmetric {p} :
  forall inh (ts : cts(p)), term_symmetric (per_cequiv inh ts).
Proof.
  introv pera perb.
  unfold per_cequiv in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw pera1; clear pera1.

  unfold per_cequiv_eq_bar in *; exrepnd.
  eapply in_open_bar_pres; eauto; clear perb.
  introv ext perb.
  unfold per_cequiv_eq in *; repnd; dands; auto.
Qed.
Hint Resolve per_cequiv_term_symmetric : slow.

Lemma per_bar_per_cequiv_term_symmetric {p} :
  forall inh (ts : cts(p)), term_symmetric (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_term_symmetric : slow.

Lemma per_cequiv_term_transitive {p} :
  forall inh (ts : cts(p)), term_transitive (per_cequiv inh ts).
Proof.
  introv per e1 e2.
  unfold per_cequiv in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw per1; clear per1.

  unfold per_cequiv_eq_bar in *; exrepnd.
  eapply in_open_bar_comb; try exact e1; clear e1.
  eapply in_open_bar_comb; try exact e2; clear e2.
  apply in_ext_implies_in_open_bar; introv ext e2 e1.
  unfold per_cequiv_eq in *; repnd; dands; auto.
Qed.
Hint Resolve per_cequiv_term_transitive : slow.

Lemma per_bar_per_cequiv_term_transitive {p} :
  forall inh (ts : cts(p)), term_transitive (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_term_transitive : slow.

Lemma per_cequiv_eq_ccequivc_ext_terms {o} :
  forall inh lib (a b : @CTerm o) t1 t2 t3 t4,
    ccequivc_ext inh lib t1 t2
    -> ccequivc_ext inh lib t3 t4
    -> per_cequiv_eq inh lib a b t1 t3
    -> per_cequiv_eq inh lib a b t2 t4.
Proof.
  introv ceqa ceqb per; unfold per_cequiv_eq in *; repnd; dands; eauto 3 with slow.
Qed.

Lemma per_cequiv_term_value_respecting {p} :
  forall inh (ts : cts(p)), term_value_respecting inh (per_cequiv inh ts).
Proof.
  introv per e ceq.
  unfold per_cequiv in *; exrepnd.
  allrw per1; clear per1.

  unfold per_cequiv_eq_bar in *; exrepnd.
  eapply in_open_bar_comb; try exact e; clear e.
  apply in_ext_implies_in_open_bar; introv ext e.

  eapply per_cequiv_eq_ccequivc_ext_terms; try exact e; eauto 4 with slow.
Qed.
Hint Resolve per_cequiv_term_value_respecting : slow.

Lemma per_bar_per_cequiv_term_value_respecting {p} :
  forall inh (ts : cts(p)), term_value_respecting inh (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_term_value_respecting : slow.

Lemma per_bar_per_cequiv_type_system {p} :
  forall inh (ts : cts(p)), type_system inh (per_bar inh (per_cequiv inh ts)).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_cequiv_type_system : slow.

(*Lemma per_cequiv_bar_uniquely_valued2 {p} :
  forall inh (ts : cts(p)), uniquely_valued2 (per_cequiv_bar ts).
Proof.
  unfold uniquely_valued2, per_cequiv_bar, eq_term_equals; sp.
  pose proof (two_computes_to_valc_ceq_bar_mkc_cequiv bar0 bar T a0 b0 a b) as q; repeat (autodimp q hyp).
  allrw; sp.
  eapply eq_per_cequiv_eq_bar; eauto.
Qed.
Hint Resolve per_cequiv_bar_uniquely_valued2 : slow.*)

Lemma per_cequiv_eq_ccequivc_ext {o} :
  forall inh lib (a1 b1 a2 b2 : @CTerm o) t1 t2,
    ccequivc_ext inh lib a1 a2
    -> ccequivc_ext inh lib b1 b2
    -> per_cequiv_eq inh lib a1 b1 t1 t2
    -> per_cequiv_eq inh lib a2 b2 t1 t2.
Proof.
  introv ceqa ceqb per; unfold per_cequiv_eq in *; repnd; dands; eauto 3 with slow.
  pose proof (ceqa _ (lib_extends_refl _ _)) as ceqa; simpl in *.
  pose proof (ceqb _ (lib_extends_refl _ _)) as ceqb; simpl in *.
  spcast.
  eapply cequivc_trans;[apply cequivc_sym;exact ceqa|].
  eapply cequivc_trans;[exact per|]; auto.
Qed.
Hint Resolve per_cequiv_eq_ccequivc_ext : slow.

Lemma per_cequiv_uniquely_valued2 {p} :
  forall inh (ts : cts(p)), uniquely_valued2 (per_cequiv inh ts).
Proof.
  unfold uniquely_valued2, per_cequiv, eq_term_equals; sp.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_cequiv_right in ceq; repnd.
  allrw.
  split; introv h; eauto 4 with slow.
Qed.
Hint Resolve per_cequiv_uniquely_valued2 : slow.

Lemma per_bar_per_cequiv_uniquely_valued2 {p} :
  forall inh (ts : cts(p)), uniquely_valued2 (per_bar inh (per_cequiv inh ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_cequiv_uniquely_valued2 : slow.
