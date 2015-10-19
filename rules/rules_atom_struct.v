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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents_atom_tacs.
Require Export rules_struct.



Lemma utok_ren_cseq_thin_hyps {o} :
  forall H J C t wg cg c wfs ct ce D deq fresh
         (f : @utok_ren_cseq
                (set_dset_string o)
                (mk_dset D deq fresh)
                (mk_wcseq ((H ++ J) ||- (mk_concl C t))
                          (ext_wf_cseq (H ++ J) ||- (mk_concl C t) wg cg c))),
    @utok_ren_cseq
      (set_dset_string o)
      (mk_dset D deq fresh)
      (mk_wcseq (H) ||- (mk_concl C t) (wfs, (ct, ce))).
Proof.
  introv f.
  intro p; exrepnd; simpl in p0.
  assert (dset_member
            x
            (get_utokens_cseq
               (mk_wcseq (H ++ J) ||- (mk_concl C t)
                         (ext_wf_cseq (H ++ J) ||- (mk_concl C t) wg cg c)))) as m.
  (* -- begin proof of m *)
  allrw @dset_member_iff.
  allunfold @get_utokens_cseq; allsimpl.
  allunfold @get_utokens_ctseq; allsimpl.
  allunfold @get_utokens_seq; allsimpl.
  allunfold @get_utokens_bseq; allsimpl.
  allrw @get_utokens_bhyps_app; allrw in_app_iff; sp.
  (* -- end proof of m *)
  pose proof (f (existT _ x m)); auto.
Defined.

(* !! MOVE to lsubst_hyps *)
Lemma wf_hyps_proof_irrelevance {o} :
  forall (hs : @barehypotheses o)
         (p1 p2 : wf_hyps hs),
    p1 = p2.
Proof.
  introv.
  allunfold @wf_hyps.
  allunfold @wf_hyp.
  apply functional_extensionality_dep; introv.
  apply functional_extensionality_dep; introv.
  apply wf_term_proof_irrelevance.
Qed.

Lemma rule_thin_hyps_atom_true {o} :
  forall lib (H J : @barehypotheses (s2s o))
         (C t : NTerm),
    rule_atom_true lib (rule_thin_hyps H J C t).
Proof.
  introv.
  unfold rule_atom_true, closed_type_baresequent, closed_extract_baresequent.
  introv cargs hyps; allsimpl.

  clear cargs.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct wf1 as [wfs wf1].
  destruct wf1 as [ct ce].
  allsimpl.

  assert (closed_extract (H ++ J) (mk_concl C t))
    as c by (wfseq; apply covered_app_weak_l; auto).
  exists c.

  unfold sequent_atom_true.
  introv kelts; introv.

  pose proof (replace_utokens_cseq_mk_wcseq
                ((H ++ J) ||- (mk_concl C t))
                (ext_wf_cseq (H ++ J) ||- (mk_concl C t) wg cg c)
                f) as e; exrepnd.
  rw e0; clear e0.

  revert w'.
  unfold replace_utokens_bseq; introv; allsimpl.
  foldseq.

  revert w'.
  rw @replace_utokens_bhyps_app; introv.

  destruct w' as [wsr w']; destruct w' as [ctr cer]; allsimpl.

  pose proof (rule_thin_hyps_true
                (replace_utokens_library lib fl)
                (replace_utokens_bhyps
                   H
                   (wf_hyps_app_left H J (wf_sequent_2hyps (H ++ J) ||- (mk_concl C t) wg))
                   (utok_ren_bhyps_app_2bhyps1
                      H J
                      (utok_ren_bseq_2h (H ++ J) ||- (mk_concl C t) f)))
                (replace_utokens_bhyps
                   J
                   (wf_hyps_app_right H J (wf_sequent_2hyps (H ++ J) ||- (mk_concl C t) wg))
                   (utok_ren_bhyps_app_2bhyps2
                      H J
                      (utok_ren_bseq_2h (H ++ J) ||- (mk_concl C t) f)))
                (replace_utokens_t
                   C
                   (wf_concl_ext_2typ C t (wf_sequent_2concl (H ++ J) ||- (mk_concl C t) wg))
                   (utok_ren_concle_2t
                      C t
                      (utok_ren_bseq_2c (H ++ J) ||- (mk_concl C t) f)))
                (replace_utokens_t
                   t
                   (wf_concl_ext_2ext C t (wf_sequent_2concl (H ++ J) ||- (mk_concl C t) wg))
                   (utok_ren_concle_2e
                      C t
                      (utok_ren_bseq_2c (H ++ J) ||- (mk_concl C t) f)))
                wsr
                ctr
                (args_constraints_nil _)) as h; simpl in h.

  repeat (autodimp h hyp).

  - clear cer ctr wsr.
    introv h.
    dorn h; tcsp; subst.
    pose proof (hyp1 k D deq fresh kelts) as h; clear hyp1.

    pose proof (h (utok_ren_cseq_thin_hyps
                     H J C t wg cg c wfs ct ce D deq fresh f)
                  fl) as hh; clear h.

    pose proof (replace_utokens_cseq_mk_wcseq
                  ((H) ||- (mk_concl C t))
                  (wfs,(ct,ce))
                  (utok_ren_cseq_thin_hyps
                     H J C t wg cg c wfs ct ce D deq fresh f)) as e; exrepnd.
    rw e0 in hh; clear e0.
    allunfold @replace_utokens_bseq; allsimpl.
    foldseq.
    rw <- @sequent_true_eq_VR in hh.

    assert (eq_utok_ren_bhyps
              H
              (utok_ren_bseq_2h
                 ((H) ||- (mk_concl C t))
                 (utok_ren_cseq_thin_hyps H J C t wg cg c wfs ct ce D deq fresh f))
              (utok_ren_bhyps_app_2bhyps1
                 H J
                 (utok_ren_bseq_2h (H ++ J) ||- (mk_concl C t) f))) as e1.
    introv; exrepnd; simpl.
    gen_s2s; PI2.

    assert (eq_utok_ren
              C
              (utok_ren_concle_2t
                 C t
                 (utok_ren_bseq_2c (H) ||- (mk_concl C t)
                                   (utok_ren_cseq_thin_hyps H J C t wg cg c wfs ct
                                                            ce D deq fresh f)))
              (utok_ren_concle_2t
                 C t
                 (utok_ren_bseq_2c (H ++ J) ||- (mk_concl C t) f))
           ) as e2.
    introv; exrepnd; simpl.
    gen_s2s; PI2.

    assert (eq_utok_ren
              t
              (utok_ren_concle_2e
                 C t
                 (utok_ren_bseq_2c (H) ||- (mk_concl C t)
                                   (utok_ren_cseq_thin_hyps H J C t wg cg c wfs ct
                                                            ce D deq fresh f)))
              (utok_ren_concle_2e
                 C t
                 (utok_ren_bseq_2c (H ++ J) ||- (mk_concl C t) f))
           ) as e3.
    introv; exrepnd; simpl.
    gen_s2s; PI2.

    remember (wf_hyps_app_left H J (wf_sequent_2hyps (H ++ J) ||- (mk_concl C t) wg)) as wH.
    remember (wf_concl_ext_2typ C t (wf_sequent_2concl (H ++ J) ||- (mk_concl C t) wg)) as wC.
    remember (wf_concl_ext_2ext C t (wf_sequent_2concl (H ++ J) ||- (mk_concl C t) wg)) as wt.

    rw <- (replace_utokens_bhyps_eq H wH wH _ _ e1).
    rw <- (replace_utokens_t_eq C wC wC _ _ e2).
    rw <- (replace_utokens_t_eq t wt wt _ _ e3).

    remember (wf_sequent_2hyps (H) ||- (mk_concl C t) wfs) as wH'.
    remember (wf_concl_ext_2typ C t (wf_sequent_2concl (H) ||- (mk_concl C t) wfs)) as wC'.
    remember (wf_concl_ext_2ext C t (wf_sequent_2concl (H) ||- (mk_concl C t) wfs)) as wt'.
    allsimpl.

    pose proof (wf_term_proof_irrelevance C wC wC') as e; rw e; clear e.
    pose proof (wf_term_proof_irrelevance t wt wt') as e; rw e; clear e.
    pose proof (wf_hyps_proof_irrelevance H wH wH') as e; rw e; clear e.

    exists w'; auto.

  - exrepnd.
    allunfold @closed_extract_baresequent; allsimpl; PI2.
    unfold ext_wf_cseq in h0.
    rw @sequent_true_eq_VR in h0; auto.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
