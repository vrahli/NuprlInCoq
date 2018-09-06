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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents_equality.
Require Export sequents_tacs2.
Require Import sequents_tacs.
Require Import sequents_useful.
Require Import tactics2.
Require Import cequiv_tacs.
Require Import subst_tacs.
Require Export rules_pertype.
Require Export subst_per.
Require Export per_props_pertype.


(**

  This is the kind of subgoal we get from using [rule_pertype_elimination4]

 *)
Definition rule_sqper_type {o}
           (R : @NTerm o)
           (x v1 v2 : NVar)
           (H J : barehypotheses) :=
  mk_rule
    (mk_bseq (snoc H (mk_hyp x (mk_pertype (sqper_rel v1 v2 R))) ++ J)
             (mk_concl_t (mk_apply2 (sqper_rel v1 v2 R) (mk_var x) (mk_var x))))
    [ ]
    [ ].

Lemma rule_sqper_type_true {o} :
  forall lib (R : @NTerm o),
  forall x v1 v2 : NVar,
  forall H J : barehypotheses,
    rule_true lib
              (rule_sqper_type
                 R
                 x v1 v2
                 H J).
Proof.
  unfold rule_sqper_type, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  clear hyps.
  unfold closed_extract; simpl.
  exists (@eq_refl bool true).

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
           # !LIn x (vars_hyps J)
           # disjoint (vars_hyps H) (vars_hyps J)) as vhyps.

  dwfseq.
  sp.

  destruct vhyps as [ nifH vhyps ].
  destruct vhyps as [ nifJ disjHJ ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  applydup eqh in sim as eqhyps.
  rw eq_hyps_app in eqhyps; exrepnd; subst; allrw length_snoc.
  rw eq_hyps_snoc in eqhyps5; exrepnd; subst; allsimpl; allrw length_snoc; cpx.
  lsubst_tac.

  dup sim as sim'.
  rw similarity_app in sim'; simpl in sim'; exrepnd; cpx.
  apply app_split in sim'0;
    try (complete (allapply similarity_length; allrw length_snoc; repnd; allrw; sp));
    repnd; subst; cpx.
  apply app_split in sim'2;
    try (complete (allapply similarity_length; allrw length_snoc; repnd; allrw; sp));
    repnd; subst; cpx.
  rw similarity_snoc in sim'5; simpl in sim'5; exrepnd; cpx.
  proof_irr; GC.

  assert (disjoint (free_vars (sqper_rel v1 v2 R)) (vars_hyps J)) as disjper.
  (* begin proof of assert *)
  clear_dependencies p.
  rw cover_vars_pertype in p.
  apply subvars_if_cover_vars_eq_hyps with (s2 := s2a) (H := H) in p; auto.
  rw subvars_prop in p.
  introv i.
  apply p in i.
  apply disjHJ in i; auto.
  (* end proof of assert *)

  assert (!LIn x (free_vars (sqper_rel v1 v2 R))) as nifper.
  (* begin proof of assert *)
  clear_dependencies p.
  rw cover_vars_pertype in p; repnd.
  intro i.
  apply subvars_if_cover_vars_eq_hyps with (s2 := s2a) (H := H) in p; auto.
  rw subvars_prop in p.
  apply p in i; auto.
  (* end proof of assert *)

  lsubst_tac.
  rw tequality_mkc_pertype in eqhyps0; repnd.

  allunfold sqper_rel.

  lsubst_tac.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).

  apply tequality_erase; dands.

  rw equality_in_mkc_pertype in sim'2; repnd.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).

  unfold is_per_type in sim'3.
  destruct sim'3 as [sym trans].

  generalize (sym t0 t3); clear sym; intro sym.
  autodimp sym hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).

  generalize (trans t0 t3 t0); intro trans1.
  autodimp trans1 hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  autodimp trans1 hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).

  generalize (trans t3 t0 t3); intro trans2.
  autodimp trans2 hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  autodimp trans2 hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).

  split; intro k; auto.

  generalize (eqhyps7 t3 t3); intro i.
  destruct i as [i1 i2]; clear i2.
  autodimp i1 hyp.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw inhabited_type_erasec in i1; auto.
  rw inhabited_type_erasec in trans1; auto.

  generalize (eqhyps2 t0 t0); clear eqhyps0; intro ty1.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw type_erase in ty1; auto.

  generalize (eqhyps5 t3 t3); clear eqhyps5; intro ty2.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw type_erase in ty2; auto.
Qed.






(**

  This is the kind of subgoal we get from using [rule_pertype_elimination_t]:
<<
     H, x : t1 = t2 in pertype(sqper_rel v1 v2 R), J |- R t1 t2 is a type
>>

 *)
Definition rule_sqper_type2
           (t1 t2 R : NTerm)
           (x v1 v2 : NVar)
           (H J : barehypotheses) :=
  mk_rule
    (mk_bseq (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype (sqper_rel v1 v2 R)))) ++ J)
             (mk_concl_t (mk_apply2 (sqper_rel v1 v2 R) t1 t2)))
    [ ]
    [ ].

Lemma rule_sqper_type2_true :
  forall t1 t2 R : NTerm,
  forall x v1 v2 : NVar,
  forall H J : barehypotheses,
    rule_true (rule_sqper_type2
                 t1 t2 R
                 x v1 v2
                 H J).
Proof.
  unfold rule_sqper_type2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  clear hyps.
  unfold closed_extract; simpl.
  exists (@eq_refl bool true).

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
           # !LIn x (vars_hyps J)
           # !LIn x (free_vars t1)
           # !LIn x (free_vars t2)
           # disjoint (free_vars t1) (vars_hyps J)
           # disjoint (free_vars t2) (vars_hyps J)
           # disjoint (vars_hyps H) (vars_hyps J)) as vhyps.

  dwfseq.
  sp;
    try (complete (unfold disjoint; unfold disjoint in wg8; introv k l; discover;
                   repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]);
                   sp)).

  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nixJ vhyps ].
  destruct vhyps as [ nixt1 vhyps ].
  destruct vhyps as [ nixt2 vhyps ].
  destruct vhyps as [ disjt1J vhyps ].
  destruct vhyps as [ disjt2J disjHJ ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  applydup eqh in sim as eqhyps.
  rw eq_hyps_app in eqhyps; exrepnd; subst; allrw length_snoc.
  rw eq_hyps_snoc in eqhyps5; exrepnd; subst; allsimpl; allrw length_snoc; cpx.
  lsubst_tac.

  dup sim as sim'.
  rw similarity_app in sim'; simpl in sim'; exrepnd; cpx.
  apply app_split in sim'0;
    try (complete (allapply similarity_length; allrw length_snoc; repnd; allrw; sp));
    repnd; subst; cpx.
  apply app_split in sim'2;
    try (complete (allapply similarity_length; allrw length_snoc; repnd; allrw; sp));
    repnd; subst; cpx.
  rw similarity_snoc in sim'5; simpl in sim'5; exrepnd; cpx.
  proof_irr; GC.

  assert (disjoint (free_vars (sqper_rel v1 v2 R)) (vars_hyps J)) as disjper.
  (* begin proof of assert *)
  clear_dependencies p.
  rw cover_vars_equality in p; rw cover_vars_pertype in p; repnd.
  apply subvars_if_cover_vars_eq_hyps with (s2 := s2a) (H := H) in p; auto.
  rw subvars_prop in p.
  introv i.
  apply p in i.
  apply disjHJ in i; auto.
  (* end proof of assert *)

  assert (!LIn x (free_vars (sqper_rel v1 v2 R))) as nifper.
  (* begin proof of assert *)
  clear_dependencies p.
  rw cover_vars_equality in p; rw cover_vars_pertype in p; repnd.
  intro i.
  apply subvars_if_cover_vars_eq_hyps with (s2 := s2a) (H := H) in p; auto.
  rw subvars_prop in p.
  apply p in i; auto.
  (* end proof of assert *)

  lsubst_tac.
  rw tequality_mkc_equality in eqhyps0; repnd.
  rw tequality_mkc_pertype in eqhyps2; repnd.
  repeat (rw equality_in_mkc_pertype in eqhyps5).

  generalize (is_per_type_sqper_rel_change_subst
                v1 v2 R s1a s2a w0 c0 c5
                eqhyps10 eqhyps2); intro isper2.

  allunfold sqper_rel.

  lsubst_tac.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).

  apply tequality_erase; dands.

  split; intro k.

  destruct eqhyps5 as [i1 i2]; clear i2.
  autodimp i1 hyp; dands; auto.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
  rw inhabited_type_erasec; auto.
  repnd.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
  rw inhabited_type_erasec in i0; auto.

  destruct eqhyps5 as [i1 i2]; clear i1.
  autodimp i2 hyp; dands; auto.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
  rw inhabited_type_erasec; auto.
  repnd.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
  rw inhabited_type_erasec in i0; auto.

  generalize (eqhyps8 (lsubstc t1 w1 s1a c1) (lsubstc t2 w2 s1a c2));
    clear eqhyps8; intro ty1.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw type_erase in ty1; auto.

  generalize (eqhyps9 (lsubstc t1 w1 s2a c3) (lsubstc t2 w2 s2a c4));
    clear eqhyps9; intro ty2.
  repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac; auto).
  rw type_erase in ty2; auto.
Qed.


Definition rule_per_function_type
           (A B : NTerm)
           (f : NVar)
           (H J : barehypotheses) :=
  mk_rule
    (mk_bseq (snoc H (mk_hyp f (mk_per_function A B)) ++ J)
             (mk_concl_t (mk_apply2 (mk_per_function_rel A B) (mk_var f) (mk_var f))))
    [ ]
    [ ].

Lemma rule_per_function_type_true :
  forall A B : NTerm,
  forall f : NVar,
  forall H J : barehypotheses,
    rule_true (rule_per_function_type
                 A B
                 f
                 H J).
Proof.
  introv.
  unfold rule_per_function_type.
  unfold mk_per_function, mk_per_function_rel.
  remember (newvars5 [A,B]); repnd.
  generalize (rule_sqper_type_true
                (mk_per_function_base p3 p2 p1 p0 p A B)
                f p1 p0 H J); auto.
Qed.
