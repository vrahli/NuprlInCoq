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
Require Export per_props_atom.
Require Export per_props_equality.


Definition rule_utoken_intro {o}
           (H : @barehypotheses (s2s o))
           (s : String.string) : @rule (s2s o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (@mk_utoken (s2s o) s) mk_uatom)))
    [] [].

Lemma rule_utoken_intro_atom_true {o} :
  forall lib (H : @barehypotheses (s2s o))
         (s : String.string),
    rule_atom_true lib (rule_utoken_intro H s).
Proof.
  unfold rule_utoken_intro, rule_atom_true, closed_type_baresequent, closed_extract_baresequent.
  introv cargs hyps.
  clear cargs hyps.
  destseq; allsimpl.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  unfold sequent_atom_true; introv kelts; introv.
  rw @VR_sequent_true_all.

  intros s1 s2.

  simpl.

  introv sim hf; introv.

  repeat gen_utok_ren.
  repeat foldall.
  repeat wf_gen.

  lsubst_tac.

  rw <- @member_equality_iff.

  assert (@app_utok_c (set_dset_string o) (mk_dset D deq fresh) s f13
          = @app_utok_c (set_dset_string o) (mk_dset D deq fresh) s f14) as e.
  unfold app_utok_c.
  unfold eq_utok_ren_o_c in h12; rw h12; clear h12.
  unfold eq_utok_ren_o_c in h13; rw h13; clear h13.
  unfold eq_utok_ren_t_o in h11; rw h11; clear h11.
  unfold eq_utok_ren_t_o in h10; rw h10; clear h10.
  unfold eq_utok_ren_b_t in h8; rw h8; clear h8.
  unfold eq_utok_ren_b_t in h9; rw h9; clear h9.
  unfold eq_utok_ren_bs_b in h7; rw h7; clear h7.
  unfold eq_utok_ren_bs_b in h6; rw h6; clear h6.
  unfold eq_utok_ren_bs_bs in h5; rw h5; clear h5.
  gen_in_utok; PI2.

  rw e.

  dands.

  apply tequality_mkc_equality2_sp; dands.
  apply tequality_uatom.
  split; right; spcast; apply cequivc_refl.
  apply equality_in_uatom_iff.
  exists (@app_utok_c (set_dset_string o) (mk_dset D deq fresh) s f14); dands; auto;
  spcast; apply computes_to_value_isvalue_refl; repeat constructor; simpl; sp.
Qed.

Lemma rule_utoken_intro_true {o} :
  forall lib (H : @barehypotheses (s2s o))
         (s : String.string),
    rule_true lib (rule_utoken_intro H s).
Proof.
  introv.
  unfold rule_utoken_intro, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  introv cargs hyps.
  clear cargs hyps.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
Abort.


Definition mk_injective {o} (A B f : @NTerm o) :=
  match newvars2 [f,A,B] with
    | (a1,a2) =>
      mk_all
        A a1
        (mk_all
           A a2
           (mk_fun
              (mk_equality (mk_apply f (mk_var a1)) (mk_apply f (mk_var a2)) B)
              (mk_equality (mk_var a1) (mk_var a2) A)))
  end.

Definition rule_utoken_exists_1to1 {o}
           (H J : @barehypotheses (s2s o))
           (k f : NVar)
           (e : NTerm) : @rule (s2s o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp k mk_tnat) ++ J)
       (mk_concl
          (mk_exists
             (mk_fun mk_tnat mk_uatom)
             f
             (mk_injective mk_tnat mk_uatom (mk_var f)))
          e))
    [] [].

Lemma rule_utoken_exists_1to1_atom_true {o} :
  forall lib (H J : @barehypotheses (s2s o))
         (k f : NVar),
    {e : NTerm & rule_atom_true lib (rule_utoken_exists_1to1 H J k f e) }.
Proof.
Abort.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
