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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sovar_alpha.
Require Export atoms.


Definition matching_paramsb (p1 p2 : parameter) : bool :=
  match p1, p2 with
    | param pt_int _, param pt_int _ => true
    | param pt_level _, param pt_level _ => true
    | _, _ => false
  end.

Fixpoint matching_parametersb (ps1 ps2 : list parameter) : bool :=
  match ps1, ps2 with
    | [], [] => true
    | p1 :: ps1, p2 :: ps2 =>
      matching_paramsb p1 p2
      && matching_parametersb ps1 ps2
    | _, _ => false
  end.

Definition matching_parameters ps1 ps2 :=
  assert (matching_parametersb ps1 ps2).

(*

  we say that the parameters of the lhs of an abstraction are correct if they're
  variables

 *)
Definition correct_abs_param_b (p : parameter) : bool :=
  match p with
    | param pt_int (pv_int i) => false
    | param pt_level (pv_level l) => false
    | _ => false
  end.

Definition correct_abs_params_b (ps : list parameter) : bool :=
  ball (map correct_abs_param_b ps).

Definition correct_abs_params (ps : list parameter) :=
  correct_abs_params_b ps = true.

Lemma correct_abs_params_proof_irrelevance :
  forall ps : list parameter,
  forall x y : correct_abs_params ps,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : correct_abs_params ?ps , H2 : correct_abs_params ?ps |- _ ] =>
    pose proof (correct_abs_params_proof_irrelevance ps H2 H1) as h; subst
end : pi.

Definition socovered {o} (t : @SOTerm o) vars :=
  subsovars (so_free_vars t) vars.

Lemma socovered_proof_irrelevance {o} :
  forall t : @SOTerm o,
  forall vars : list sovar_sig,
  forall x y : socovered t vars,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : socovered ?t ?vs , H2 : socovered ?t ?vs |- _ ] =>
    pose proof (socovered_proof_irrelevance t vs H2 H1) as h; subst
end : pi.

Definition no_utokens {o} (t : @SOTerm o) :=
  get_utokens_so t = [].

Lemma no_utokens_proof_irrelevance {p} :
  forall t : @SOTerm p,
  forall x y : no_utokens t,
    x = y.
Proof.
  intros.
  apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : no_utokens ?t , H2 : no_utokens ?t |- _ ] =>
    pose proof (no_utokens_proof_irrelevance t H2 H1) as h; subst
end : pi.

Definition matching_sign (vars : list sovar_sig) (sign : opsign) : Prop :=
  map (fun v => snd v) vars = sign.

Lemma matching_sign_proof_irrelevance :
  forall vars sign (x y : matching_sign vars sign),
    x = y.
Proof.
  intros.
  apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : matching_sign ?vars ?sign , H2 : matching_sign ?vars ?sign |- _ ] =>
    pose proof (matching_sign_proof_irrelevance vars sign H2 H1) as h; subst
end : pi.

Definition matching_entry_sign oa1 oa2 :=
  opabs_name oa1 = opabs_name oa2
  # opabs_sign oa1 = opabs_sign oa2
  # matching_parameters (opabs_params oa1) (opabs_params oa2).

(* the variables can also be second-order variables *)
Definition correct_abs {o}
           (opabs : opabs)
           (vars  : list sovar_sig)
           (rhs   : @SOTerm o) :=
  wf_soterm rhs
  # socovered rhs vars
  # correct_abs_params (opabs_params opabs)
  # matching_sign vars (opabs_sign opabs)
  # no_utokens rhs.

Lemma correct_abs_proof_irrelevance {p} :
  forall opabs vars (rhs : @SOTerm p),
  forall x y : correct_abs opabs vars rhs,
    x = y.
Proof.
  intros.
  destruct x, y; repnd.
  eauto 6 with pi.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : correct_abs ?o ?v ?r , H2 : correct_abs ?o ?v ?r |- _ ] =>
    pose proof (correct_abs_proof_irrelevance o v r H2 H1) as h; subst
end : pi.

(*Coercion getCterm {o} : @CTerm o -> @NTerm o := get_cterm.*)

Definition ChoiceSeqVal {o} := @CTerm o.
Definition ChoiceSeqVals {o} := list (@ChoiceSeqVal o).

Definition CSVal2term {o} (v : @ChoiceSeqVal o) : NTerm := get_cterm v.

Inductive library_entry {o} :=
(* a choice sequence *)
| lib_cs
    (name : choice_sequence_name)
    (vals : @ChoiceSeqVals o)
(* a regular abstraction *)
| lib_abs
    (opabs : opabs)
    (vars  : list sovar_sig)
    (rhs   : @SOTerm o)
    (correct : correct_abs opabs vars rhs).

Definition pre_library {o} := list (@library_entry o).

Definition emlib {o} : @pre_library o := [].

Definition RestrictionPred {o} := nat -> @CTerm o -> Prop.

Definition RestrictionPredLibCond {o} (L : Type) :=
  nat -> @CTerm o -> L -> Prop.

(*Definition RestrictionPredLib {o} (Q : RestrictionPredLibCond) :=
  forall (n : nat) (v : @CTerm o), {lib : @pre_library o | Q n v lib}.*)

Inductive ChoiceSeqRestriction {o} (L : Type) :=
(* constrains the values of the sequence to have that type *)
(* [d] is a default value e*)
| csc_type (d : nat -> @ChoiceSeqVal o) (typ : @RestrictionPred o) (typd : forall n, typ n (d n))
(* constrains the values of the sequence to follow the law given by the function *)
| csc_coq_law (f : nat -> @CTerm o)
(* no default *)
| csc_res (Q : @RestrictionPredLibCond o L) (*(M : RestrictionPredLib Q)*).
Arguments csc_type    [o] [L] _ _ _.
Arguments csc_coq_law [o] [L] _.
Arguments csc_res     [o] [L] _.

(* no constraints *)
Definition csc_no {o} {L} : @ChoiceSeqRestriction o L :=
  csc_type (fun _ => mkc_zero) (fun _ _ => True) (fun _ => I).

(* A way to define a coq law using the type restriction *)
Definition csc_coq_law_as_type {o} {L} (f : nat -> @CTerm o) : @ChoiceSeqRestriction o L :=
  csc_type f (fun n v => v = f n) (fun _ => eq_refl).

Record restriction {o} L :=
  MkRes
    {
      res_name : choice_sequence_name;
      res_res  : @ChoiceSeqRestriction o L;
    }.
Arguments MkRes    [o] [L] _ _.
Arguments res_name [o] [L] _.
Arguments res_res  [o] [L] _.

Definition restrictions {o} L := list (@restriction o L).

Record libraryL {o} L :=
  MkLibraryL
    {
      lib_lib :> @pre_library o;
      lib_res : @restrictions o L;
    }.
Arguments MkLibraryL [o] [L] _ _.
Arguments lib_lib    [o] [L] _.
Arguments lib_res    [o] [L] _.

Fixpoint libraryn {o} (n : nat) : Type :=
  @libraryL o match n with
              | 0 => False
              | S n => @libraryn o n
              end.

Definition libraryn2list {o} {n} : @libraryn o n -> list library_entry :=
  match n with
  | 0 => fun lib => lib_lib lib
  | S _ => fun lib => lib_lib lib
  end.
Coercion libraryn2list : libraryn >-> list.

Record library {o} :=
  MkLibrary
    {
      lib_lvl  : nat;
      lib_libn :> @libraryn o lib_lvl;
    }.
Arguments MkLibrary [o] _ _.

Definition lib2list {o} (lib : @library o) : list library_entry := lib.
Coercion lib2list : library >-> list.

Ltac dlib lib :=
  let cond := fresh "cond" in
  destruct lib as [lib cond].

Definition matching_bterms {o} (vars : list sovar_sig) (bs : list (@BTerm o)) :=
  map (fun v => snd v) vars = map num_bvars bs.

Definition matching_entry {o} oa1 oa2 (vars : list sovar_sig) (bs : list (@BTerm o)) :=
  opabs_name oa1 = opabs_name oa2
  # opabs_sign oa1 = opabs_sign oa2
  # matching_parameters (opabs_params oa1) (opabs_params oa2)
  # matching_bterms vars bs.

Definition not_matching_entry {o} oa1 oa2 (vars : list sovar_sig) (bs : list (@BTerm o)) :=
  opabs_name oa1 <> opabs_name oa2
  [+] opabs_sign oa1 <> opabs_sign oa2
  [+] !matching_parameters (opabs_params oa1) (opabs_params oa2)
  [+] !matching_bterms vars bs.

Definition matching_entry_deq {o} oa1 oa2 (vars : list sovar_sig) (bs : list (@BTerm o)) :
  matching_entry oa1 oa2 vars bs
  + not_matching_entry oa1 oa2 vars bs.
Proof.
  unfold matching_entry, not_matching_entry.
  destruct (String.string_dec (opabs_name oa1) (opabs_name oa2));
  try (complete (right; auto));
  destruct (opsign_dec (opabs_sign oa1) (opabs_sign oa2));
  try (complete (right; auto));
  remember (matching_parametersb (opabs_params oa1) (opabs_params oa2)) as m;
  destruct m;
  try (complete (right; right; right; left; intro k;
                 unfold matching_parameters in k; rw <- Heqm in k; inversion k));
  destruct (opsign_dec (map (fun v => snd v) vars) (map num_bvars bs));
  try (complete (right; auto)).
  left; dands; auto.
  unfold matching_parameters.
  rewrite <- Heqm; sp.
Defined.

Fixpoint mk_abs_subst {o} (vs : list sovar_sig) (bs : list (@BTerm o)) : @SOSub o :=
  match vs, bs with
    | (v,n) :: vs, (bterm vars t) :: bs =>
      if deq_nat n (length vars)
      then (v, sosk vars t) :: mk_abs_subst vs bs
      else []
    | _, _ => []
  end.

Lemma mk_abs_subst_nil_r {o} :
  forall vars, @mk_abs_subst o vars [] = [].
Proof.
  induction vars; simpl; sp.
  dsovar_sigs; auto.
Qed.

Definition mk_instance {o}
           (vars : list sovar_sig)
           (bs   : list (@BTerm o))
           (rhs  : SOTerm) :=
  sosub (mk_abs_subst vars bs) rhs.

Definition unfold_abs_entry {o}
           (entry : @library_entry o)
           (opabs : opabs)
           (bs    : list (@BTerm o)): option (@NTerm o) :=
  match entry with
  | lib_cs _ _ => None
  | lib_abs oa vars rhs correct =>
    if matching_entry_deq opabs oa vars bs
    then
      Some (mk_instance vars bs rhs)
           (* we have to substitute the param vars too *)
    else None
  end.

Fixpoint find_cs {o} (lib : pre_library) name : option (@ChoiceSeqVals o) :=
  match lib with
  | [] => None
  | lib_cs name' e :: l =>
    if choice_sequence_name_deq name name' then Some e
    else find_cs l name
  | _ :: l => find_cs l name
  end.

Fixpoint find_value_of_cs_at {o} (L : @ChoiceSeqVals o) n : option ChoiceSeqVal :=
  match L, n with
  | [], _ => None
  | t :: _, 0 => Some t
  | _ :: l, S m => find_value_of_cs_at l m
  end.

Lemma find_value_of_cs_at_is_select {o} :
  forall n (L : @ChoiceSeqVals o),
    find_value_of_cs_at L n = select n L.
Proof.
  induction n; introv; simpl; destruct L; simpl; auto.
Qed.

Definition find_cs_value_at {o} (lib : pre_library) name n : option (@ChoiceSeqVal o) :=
  match find_cs lib name with
  | Some L => find_value_of_cs_at L n
  | None => None
  end.

Fixpoint find_entry {o} (lib : @pre_library o) oa0 (bs : list (@BTerm o)) : option (@library_entry o) :=
  match lib with
  | [] => None
  | lib_cs _ _ :: l => find_entry l oa0 bs
  | (lib_abs oa vars rhs correct as entry) :: l =>
    if matching_entry_deq oa0 oa vars bs
    then Some entry
    else find_entry l oa0 bs
  end.

Definition found_entry {o}
           (lib : @pre_library o) oa0 (bs : list (@BTerm o))
           oa vars rhs correct :=
  find_entry lib oa0 bs = Some (lib_abs oa vars rhs correct).

Lemma found_entry_implies_matching_entry {o} :
  forall (lib : @pre_library o) oa0 (bs : list (@BTerm o))
         oa vars rhs correct,
    found_entry lib oa0 bs oa vars rhs correct
    -> matching_entry oa0 oa vars bs.
Proof.
  introv f.
  unfold found_entry in f.
  induction lib; allsimpl; ginv.
  destruct a; tcsp;[].
  destruct (matching_entry_deq oa0 opabs vars0 bs); auto.
  inversion f; subst; auto.
Qed.

Fixpoint unfold_abs {o}
         (lib   : @pre_library o)
         (opabs : opabs)
         (bs    : list (@BTerm o)): option (@NTerm o) :=
  match lib with
    | [] => None
    | entry :: lib =>
      match unfold_abs_entry entry opabs bs with
        | Some t => Some t
        | None => unfold_abs lib opabs bs
      end
  end.

Definition unfold {o} (lib : @pre_library o) (t : @NTerm o) : option (@NTerm o) :=
  match t with
    | oterm (Abs opabs) bs => unfold_abs lib opabs bs
    | _ => None
  end.

Lemma mk_abs_subst_some_prop1 {o} :
  forall vars (bs : list (@BTerm o)) v vs t,
    LIn (v,sosk vs t) (mk_abs_subst vars bs)
    -> LIn (bterm vs t) bs.
Proof.
  induction vars; introv e; allsimpl; tcsp.
  destruct a.
  destruct bs; allsimpl; tcsp.
  destruct b; allsimpl; tcsp.
  boolvar; subst; allsimpl; tcsp.
  dorn e; cpx; ginv; tcsp.
  apply IHvars in e; tcsp.
Qed.

Lemma mk_abs_subst_some_prop2 {o} :
  forall (vars : list sovar_sig) (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> vars = sodom (mk_abs_subst vars bs).
Proof.
  unfold matching_bterms.
  induction vars; introv e; allsimpl; tcsp.
  destruct a; allsimpl.
  destruct bs; allsimpl; tcsp; cpx; clear e.
  destruct b; allunfold @num_bvars; simpl.
  boolvar; tcsp; GC.
  apply eq_cons; auto.
Qed.

Lemma mk_abs_subst_some_prop3 {o} :
  forall vars (bs : list (@BTerm o)),
    subsovars (sodom (mk_abs_subst vars bs)) vars.
Proof.
  induction vars; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  destruct bs; allsimpl; tcsp; cpx.
  destruct b; allsimpl; tcsp;
  try (complete (allunfold @num_bvars; allsimpl; cpx)).
  boolvar; subst; tcsp.
  apply subsovars_cons_lr; auto.
Qed.

Lemma sorange_mk_abs_subst {o} :
  forall (bs : list (@BTerm o)) vars,
    matching_bterms vars bs
    -> sorange (mk_abs_subst vars bs) = bs.
Proof.
  unfold matching_bterms.
  induction bs; simpl; introv m; destruct vars; allsimpl; cpx.
  destruct s; destruct a; boolvar; subst; allsimpl; subst.
  - apply eq_cons; auto.
  - allunfold @num_bvars; allsimpl; sp.
Qed.

Lemma isprogram_subst_lib {o} :
  forall oa0 oa vars rhs (lib : @pre_library o) bs correct,
    found_entry lib oa0 bs oa vars rhs correct
    -> (forall b, LIn b bs -> isprogram_bt b)
    -> isprogram (mk_instance vars bs rhs).
Proof.
  introv f i.
  unfold correct_abs in correct; repnd.
  apply isprogram_sosub; auto.
  - rw <- @mk_abs_subst_some_prop2; auto.
    apply found_entry_implies_matching_entry in f.
    unfold matching_entry in f; repnd; auto.
  - apply sosub_prog_prop1.
    introv k.
    rw @sorange_mk_abs_subst in k; auto.
    apply found_entry_implies_matching_entry in f.
    unfold matching_entry in f; repnd; auto.
Qed.

Lemma matching_entry_change_bs {o} :
  forall oa1 oa2 vars (bs bs2 : list (@BTerm o)),
    matching_entry oa1 oa2 vars bs
    -> map num_bvars bs = map num_bvars bs2
    -> matching_entry oa1 oa2 vars bs2.
Proof.
  introv m e; allunfold @matching_entry; repnd; dands; auto.
  unfold matching_bterms.
  rewrite <- e; auto.
Qed.

Lemma not_matching_entry_change_bs {o} :
  forall oa1 oa2 vars (bs bs2 : list (@BTerm o)),
    not_matching_entry oa1 oa2 vars bs
    -> map num_bvars bs = map num_bvars bs2
    -> not_matching_entry oa1 oa2 vars bs2.
Proof.
  introv m e; allunfold @not_matching_entry;
  repeat (dorn m; tcsp).
  right; right; right.
  unfold matching_bterms.
  rewrite <- e; auto.
Qed.

Lemma matching_parameters_proof_irrelevance :
  forall ps1 ps2,
  forall x y : matching_parameters ps1 ps2,
    x = y.
Proof.
  introv; introv.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : matching_parameters ?ps1 ?ps2 , H2 : matching_parameters ?ps1 ?ps2 |- _ ] =>
    pose proof (matching_parameters_proof_irrelevance ps1 ps2 H2 H1) as h; subst
end : pi.

Lemma decidable_eq_matching_parameters :
  forall oa1 oa2, decidable (matching_parameters (opabs_params oa1) (opabs_params oa2)).
Proof.
  introv.
  destruct oa1, oa2; simpl.
  unfold matching_parameters.
  pose proof (bool_dec true (matching_parametersb opabs_params opabs_params0)) as h;
    dorn h; try (rw <- h); try (complete (left; sp)).
  right; intro k; rw k in h; sp.
Qed.
Hint Immediate decidable_eq_matching_parameters.

Lemma not_matching_entry_iff {o} :
  forall oa1 oa2 vars (bs : list (@BTerm o)),
    not_matching_entry oa1 oa2 vars bs
    <=> !matching_entry oa1 oa2 vars bs.
Proof.
  introv; unfold matching_entry, not_matching_entry; split; intro k; repnd.
  - intro h; repnd.
    repeat (dorn k; tcsp).
  - apply not_over_and in k; auto.
    dorn k; tcsp.
    apply not_over_and in k; auto.
    dorn k; tcsp.
    apply not_over_and in k; auto.
Qed.

Lemma found_entry_change_bs {o} :
  forall oa0 oa vars rhs (lib : @pre_library o) bs correct bs2,
    found_entry lib oa0 bs oa vars rhs correct
    -> map num_bvars bs = map num_bvars bs2
    -> found_entry lib oa0 bs2 oa vars rhs correct.
Proof.
  induction lib; introv f e.
  - allunfold @found_entry; allsimpl; inversion f.
  - allunfold @found_entry; allsimpl.
    destruct a;[|].

    { eapply IHlib; eauto. }

    destruct (matching_entry_deq oa0 opabs vars0 bs).
    + pose proof (matching_entry_change_bs oa0 opabs vars0 bs bs2) as h; repeat (autodimp h hyp).
      destruct (matching_entry_deq oa0 opabs vars0 bs2); auto.
      apply not_matching_entry_iff in n; sp.
    + pose proof (not_matching_entry_change_bs oa0 opabs vars0 bs bs2) as h; repeat (autodimp h hyp).
      destruct (matching_entry_deq oa0 opabs vars0 bs2); auto.
      apply not_matching_entry_iff in h; sp.
      apply IHlib with (bs := bs); auto.
Qed.

Lemma unfold_abs_success_change_bs {o} :
  forall (lib : @pre_library o) oa1 oa2 bs1 bs2 vars rhs correct,
    map num_bvars bs1 = map num_bvars bs2
    -> found_entry lib oa1 bs1 oa2 vars rhs correct
    -> unfold_abs lib oa1 bs2 = Some (mk_instance vars bs2 rhs).
Proof.
  induction lib; introv e f; allsimpl.
  - unfold found_entry in f; simpl in f; inversion f.
  - unfold found_entry in f; simpl in f.
    destruct a;[|].

    { simpl; eapply IHlib; eauto. }

    unfold unfold_abs_entry.
    destruct (matching_entry_deq oa1 opabs vars0 bs1).
    + inversion f; subst; GC.
      assert (correct0 = correct) as h by (eauto with pi); subst; GC.
      apply (matching_entry_change_bs oa1 oa2 vars bs1 bs2) in m; auto.
      destruct (matching_entry_deq oa1 oa2 vars bs2); auto.
      apply not_matching_entry_iff in n; sp.
    + apply (not_matching_entry_change_bs oa1 opabs vars0 bs1 bs2) in n; auto.
      destruct (matching_entry_deq oa1 opabs vars0 bs2); auto.
      * apply not_matching_entry_iff in n; sp.
      * eapply IHlib; eauto.
Qed.

(*
Lemma matching_bterms_implies_b {o} :
  forall vars (bs : list (@BTerm o)) b,
    matching_bterms vars bs
    -> LIn b bs
    -> {t : NTerm & b = bterm [] t}.
Proof.
  unfold matching_bterms; introv m i.
  destruct b.
  exists n.
  assert (num_bvars (bterm l n) = 0) as h.
  - assert (LIn (num_bvars (bterm l n)) (map num_bvars bs)) as k.
    + rw in_map_iff.
      exists (bterm l n); auto.
    + rw <- m in k.
      rw in_map_iff in k; exrepnd; auto.
  - unfold num_bvars in h; simpl in h; destruct l; cpx.
Qed.
*)

(*
Lemma bterm_if_found_entry {o} :
  forall lib oa (bs : list (@BTerm o)) oa2 vars rhs correct,
    found_entry lib oa bs oa2 vars rhs correct
    -> forall b, LIn b bs -> {t : NTerm & b = bterm [] t}.
Proof.
  introv fe i.
  apply found_entry_implies_matching_entry in fe.
  unfold matching_entry in fe; repnd.
  eapply matching_bterms_implies_b in fe; eauto.
Qed.
*)

Lemma matching_bterms_cons {o} :
  forall vars (bs : list (@BTerm o)) v b,
    matching_bterms (v :: vars) (b :: bs)
    <=> (snd v = num_bvars b # matching_bterms vars bs).
Proof.
  unfold matching_bterms; split; introv m; repnd; allsimpl; cpx.
  allrw; auto.
Qed.

Lemma mk_abs_subst_as_combine {o} :
  forall vars (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> mk_abs_subst vars bs = combine (sovars2vars vars) (map bterm2sk bs).
Proof.
  induction vars; destruct bs; simpl; introv m; auto; destruct a; auto.
  destruct b; boolvar; allsimpl; subst.
  - apply eq_cons; auto.
    apply IHvars.
    apply matching_bterms_cons in m; sp.
  - provefalse.
    apply matching_bterms_cons in m; repnd; allsimpl.
    allunfold @num_bvars; allsimpl; sp.
Qed.

Definition bound_vars_entry {o} (entry : @library_entry o) : list sovar_sig :=
  match entry with
  | lib_cs _ e => vars2sovars (flat_map (fun t => bound_vars (CSVal2term t)) e)
  | lib_abs opabs vars rhs correct => vars ++ so_bound_vars rhs
  end.

Fixpoint bound_vars_lib {o} (lib : @pre_library o) : list sovar_sig :=
  match lib with
    | [] => []
    | entry :: entries => bound_vars_entry entry ++ bound_vars_lib entries
  end.

Lemma ni_bound_vars_if_found_entry {o} :
  forall (lib : @pre_library o) v oa1 bs oa2 vars rhs correct,
    !LIn v (bound_vars_lib lib)
    -> found_entry lib oa1 bs oa2 vars rhs correct
    -> !LIn v (so_bound_vars rhs).
Proof.
  unfold found_entry; induction lib; introv ni fe; simpl in fe.

  - inversion fe.

  - destruct a;[|].

    { simpl in *.
      allrw in_app_iff; allrw not_over_or; repnd.
      eapply IHlib; eauto. }

    destruct (matching_entry_deq oa1 opabs vars0 bs).
    + inversion fe; subst.
      allsimpl; allrw in_app_iff; allrw not_over_or; repnd; auto.
    + eapply IHlib in fe; eauto.
      allsimpl; allrw in_app_iff; allrw not_over_or; repnd; auto.
Qed.

(*
Lemma lubst_sub_mk_abs_subst {o} :
  forall (bs : list (@BTerm o)) vars sub,
    prog_sub sub
    -> mk_abs_subst vars (map (fun b => lsubst_bterm_aux b sub) bs)
       = lsubst_sub (mk_abs_subst vars bs) sub.
Proof.
  induction bs; simpl; introv ps; destruct vars; simpl; auto.
  destruct a; simpl.
  destruct l; simpl; auto.
  rw @sub_filter_nil_r.
  apply eq_cons; auto.
  change_to_lsubst_aux4; auto.
Qed.
*)

Lemma in_filter_out_fo_vars_iff :
  forall v n l,
    LIn (v, n) (filter_out_fo_vars l) <=> (n > 0 # LIn (v, n) l).
Proof.
  induction l; split; intro i; repnd; allsimpl; tcsp;
  destruct a; destruct n1; allsimpl; tcsp.
  - apply IHl in i; tcsp.
  - dorn i; cpx.
    + sp; omega.
    + apply IHl in i; repnd; tcsp.
  - dorn i; cpx.
    + provefalse; inversion i0.
    + apply IHl; sp.
  - dorn i; cpx.
    right; apply IHl; auto.
Qed.

Lemma socovered_implies_cover_so_vars {o} :
  forall (t : @SOTerm o) vars bs,
    socovered t vars
    -> matching_bterms vars bs
    -> cover_so_vars t (mk_abs_subst vars bs).
Proof.
  introv cov m.
  unfold socovered in cov.
  unfold cover_so_vars.
  allrw subsovars_prop; introv i.
  destruct x.
  allrw in_filter_out_fo_vars_iff; repnd; dands; auto.
  apply cov in i.
  rw <- @mk_abs_subst_some_prop2; auto.
Qed.

Lemma mk_instance_alpha_congr {p} :
  forall (rhs1 rhs2 : @SOTerm p) (vars : list sovar_sig) (bs1 bs2 : list BTerm),
    so_alphaeq rhs1 rhs2
    -> length vars = length bs1
    -> length vars = length bs2
    -> socovered rhs1 vars
    -> socovered rhs2 vars
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> bin_rel_bterm alphaeqbt bs1 bs2
    -> alphaeq (mk_instance vars bs1 rhs1) (mk_instance vars bs2 rhs2).
Proof.
  introv aeq len1 len2 cov1 cov2 m1 m2 aeqs.
  unfold mk_instance.
  applydup @mk_abs_subst_as_combine in m1 as e1.
  applydup @mk_abs_subst_as_combine in m2 as e2.
  rw e1; rw e2.

  pose proof (sosub_alpha_congr
                rhs1 rhs2
                (sovars2vars vars)
                (map bterm2sk bs1)
                (map bterm2sk bs2)) as h.
  apply h; auto; clear h.

  - unfold sovars2vars; allrw map_length; auto.

  - unfold sovars2vars; allrw map_length; auto.

  - rw <- e1; apply socovered_implies_cover_so_vars; auto.

  - rw <- e2; apply socovered_implies_cover_so_vars; auto.

  - unfold bin_rel_sk.
    unfold bin_rel_bterm in aeqs.
    allunfold @binrel_list.
    allrw map_length; repnd; dands; auto.
    introv i.
    applydup aeqs in i.

    assert (default_sk = bterm2sk (@default_bt p)) as e by auto.

    rw e; allrw map_nth.
    remember (nth n bs1 default_bt) as bt1; clear Heqbt1.
    remember (nth n bs2 default_bt) as bt2; clear Heqbt2.
    destruct bt1, bt2; simpl.
    apply alphaeq_sk_iff_alphaeq_bterm; auto.
Qed.
