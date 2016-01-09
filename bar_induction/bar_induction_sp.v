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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export bar_induction2.


Lemma bar_induction_meta2 {o} :
  forall lib P (X c : @CTerm o) v,
    barind_meta2_fun_bar lib P X v
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar ind.
  pose proof (classic (meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta2_fun_ind_implies_cont in ind.
  apply barind_meta2_fun_ind_cont_implies_cont2 in ind.
  apply barind_meta2_fun_ind_cont2_implies_cont3 in ind.
  unfold barind_meta2_fun_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c 0 v) as nc.
  clear Heqnc.

  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind) as g.
  remember (fun m => meta2_fun_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta2_fun_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta2_fun_kseq_NA_nat (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (meta2_fun_alpha_prop1 lib P X (seq2kseq c 0 v) v nc ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
      unfold meta2_fun_kseq_NA in am; exrepnd; simphyps.
      rw @meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact h1].
    auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.

  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact q1].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.

  eapply cequivc_preserves_not_meta2_fun_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
  unfold meta2_fun_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_meta2_fun_seq_NA (S m) s am0 am1)) as fn.

  assert (eq_kseq lib (update_seq s (S m) fn v) s (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    eapply member_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  apply (seq2kseq_prop2 _ v) in ee1.
  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact ee1].
  clear ee1.

  unfold seq_normalizable in am2.
  eapply cequivc_preserves_meta2_fun_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.

(*Print Assumptions bar_induction_meta4.*)

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
