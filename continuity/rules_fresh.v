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

Require Export continuity_stuff.
Require Export sequents_equality.
Require Export seq_util.
Require Export subst_tacs_aeq.


(*
   H |- fresh(v.t) in T

     By freshMember a z

     H, a : Name, z : fresh(v.t)#a |- t[v\a] in T
     H, a : Name, z : fresh(v.t)#a |- t[v\a]#a

 *)
Definition rule_fresh_member {o}
           (H : barehypotheses)
           (t T : @NTerm o)
           (v z a : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_fresh v t) T) ))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom)) (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v t) (mk_var a))))
        (mk_conclax (mk_member (subst t v (mk_var a)) T)),
      mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom)) (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v t) (mk_var a))))
        (mk_conclax (mk_free_from_atom mk_base (subst t v (mk_var a)) (mk_var a)))
    ]
    [].

Lemma rule_fresh_member_true {o} :
  forall lib (H : barehypotheses)
         (t T : @NTerm o)
         (v z a : NVar),
    rule_true lib (rule_fresh_member H t T v z a).
Proof.
  unfold rule_fresh_member, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  assert ((a <> v -> !LIn a (free_vars t))
          # a <> z
          # !LIn a (vars_hyps H)
          # !LIn z (vars_hyps H)) as vhyps.

  {
    clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (pose proof (cg0 a) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp)).
  }

  destruct vhyps as [ nat vhyps ].
  destruct vhyps as [ daz vhyps ].
  destruct vhyps as [ naH nzH ].

  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.

  pose proof (get_fresh_atom_prop t) as fa.
  remember (get_fresh_atom t) as ua; clear Hequa.

  pose proof (teq_and_member_if_member
                lib T (mk_fresh v t) s1 s2 H wT wt ct1 ct2 cT cT0)
    as teq.
  repeat (autodimp teq hyp); auto;[| |lsubst_tac; auto].

  - vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      * introv equ' sim'.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow.

        { pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c4) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.
        }

Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
