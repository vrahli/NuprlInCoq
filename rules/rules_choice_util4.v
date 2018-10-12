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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)



Require Export rules_choice_util3.


Definition not_const {o} (n a k : NVar) : @NTerm o :=
  mk_function
    mk_tnat
    n
    (mk_function
       (mk_csname 0)
       a
       (mk_not
          (mk_function
             mk_tnat
             k
             (mk_equality
                (mk_apply (mk_var a) (mk_var k))
                (mk_var n)
                mk_tnat)))).

Definition not_const_extract {o} (n a : NVar) : @NTerm o :=
  mk_lam n (mk_lam a mk_axiom).

Definition not_const_c {o} (n a k : NVar) : @CTerm o :=
  mkc_function
    mkc_tnat
    n
    (mkcv_function
       _
       (mkcv_csname _ 0)
       a
       (mkcv_not
          _
          (mkcv_function
             _
             (mkcv_tnat _)
             k
             (mkcv_equality
                _
                (mkcv_apply
                   _
                   (mk_cv_app_r _ _ (mk_cv_app_l [k] _ (mkc_var a)))
                   (mk_cv_app_r _ _ (mkc_var k)))
                (mk_cv_app_l _ _ (mkc_var n))
                (mkcv_tnat _))))).

Definition not_const_extract_c {o} (n a : NVar) : @CTerm o :=
  mkc_lam n (mkcv_lam _ a (mkcv_ax _)).


Lemma lsubstc_not_const_eq {o} :
  forall n a k (w : @wf_term o (not_const n a k)) s c,
    lsubstc (not_const n a k) w s c = not_const_c n a k.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_not_const_eq : slow.

Lemma lsubstc_not_const_extract_eq {o} :
  forall n a (w : @wf_term o (not_const_extract n a)) s c,
    lsubstc (not_const_extract n a) w s c = not_const_extract_c n a.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_not_const_extract_eq : slow.

Lemma substc2_mkcv_function {o} :
  forall w v (t : @CTerm o) (a : CVTerm [w,v]) x (b : CVTerm [x,w,v]),
    v <> x
    -> substc2 w t v (mkcv_function [w,v] a x b)
       = mkcv_function _ (substc2 w t v a) x (substcv [x,w] t v b).
Proof.
  introv ni.
  apply cvterm_eq; simpl.
  destruct_cterms; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp.
Qed.

Lemma substcv_equality {o} :
  forall l x (w : @CTerm o) (a b c : CVTerm (l ++ [x])),
    substcv l w x (mkcv_equality _ a b c)
    = mkcv_equality _ (substcv l w x a) (substcv l w x b) (substcv l w x c).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substcv_equality : slow.

Lemma substcv_apply {o} :
  forall l x (w : @CTerm o) (a b : CVTerm (l ++ [x])),
    substcv l w x (mkcv_apply _ a b)
    = mkcv_apply _ (substcv l w x a) (substcv l w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substcv_apply : slow.

Lemma substcv_mk_cv_app_r1 {o} :
  forall l (u : @CTerm o) v t,
    !LIn v l
    -> substcv l u v (mk_cv_app_r [v] l t) = t.
Proof.
  introv ni.
  destruct_cterms; apply cvterm_eq; simpl.
  apply cl_subst_trivial; eauto 3 with slow.
  introv j.
  apply isprog_vars_eq in i0; repnd.
  allrw subvars_eq.
  apply i1 in j; tcsp.
Qed.

Lemma substcv_mk_cv_app_r2 {o} :
  forall k a (u : @CTerm o) n t,
    n <> k
    -> substcv ([k] ++ [a]) u n (mk_cv_app_r [a, n] [k] t)
       = mk_cv_app_r _ _ t.
Proof.
  introv ni.
  destruct_cterms; apply cvterm_eq; simpl.
  apply cl_subst_trivial; eauto 3 with slow.
  introv j.
  apply isprog_vars_eq in i0; repnd.
  allrw subvars_eq.
  apply i1 in j; tcsp; simpl in *; repndors; subst; tcsp.
Qed.

Lemma substcv_mk_cv_app_r3 {o} :
  forall k a (u : @CTerm o) n t,
    n <> k
    -> n <> a
    -> substcv ([k] ++ [a]) u n (mk_cv_app_r [n] ([k] ++ [a]) t)
       = mk_cv_app_r _ _ t.
Proof.
  introv ni1 ni2.
  destruct_cterms; apply cvterm_eq; simpl.
  apply cl_subst_trivial; eauto 3 with slow.
  introv j.
  apply isprog_vars_eq in i0; repnd.
  allrw subvars_eq.
  apply i1 in j; tcsp; simpl in *; repndors; subst; tcsp.
Qed.

Lemma substcv_mk_cv_app_l {o} :
  forall l (u : @CTerm o) v t,
    substcv l u v (mk_cv_app_l l [v] t) = mk_cv _ (substc u v t).
Proof.
  introv.
  destruct_cterms; apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substcv_mk_cv_app_l : slow.

Lemma substcv_mk_cv {o} :
  forall k (u : @CTerm o) n t,
    substcv [k] u n (mk_cv _ t)
    = mk_cv _ t.
Proof.
  introv.
  destruct_cterms; apply cvterm_eq; simpl.
  apply cl_subst_trivial; eauto 3 with slow.
  introv j.
  apply isprog_eq in i.
  destruct i as [cl wf].
  rewrite cl in j; simpl in *; tcsp.
Qed.
Hint Rewrite @substcv_mk_cv : slow.

Lemma substcv_mkcv_tnat {o} :
  forall l (t : @CTerm o) x,
    substcv l t x (mkcv_tnat _) = mkcv_tnat _.
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  apply subst_trivial; eauto 2 with slow.
Qed.
Hint Rewrite @substcv_mkcv_tnat : slow.

Lemma tequality_not_const_c {o} :
  forall (lib : @library o) n a k
         (safe : safe_library lib)
         (d1 : n <> a) (d2 : n <> k) (d3 : a <> k),
    tequality lib (not_const_c n a k) (not_const_c n a k).
Proof.
  introv safe d1 d2 d3.
  apply tequality_function; dands; eauto 3 with slow.
  introv xt ea.

  assert (safe_library lib') as safe' by eauto 3 with slow.

  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).
  autorewrite with slow.

  apply tequality_function; dands; eauto 3 with slow.

  introv xt ef.

  eapply equality_monotone in ea;[|eauto].

  assert (safe_library lib') as safe' by eauto 3 with slow.

  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  repeat rewrite substcv_as_substc2.
  repeat rewrite substc2_not.
  autorewrite with slow.

  apply tequality_not.

  repeat (rewrite substc2_mkcv_function; tcsp;[]).
  repeat (rewrite substc_mkcv_function; tcsp;[]).
  repeat (first [progress autorewrite with slow
                |rewrite substcv_mk_cv_app_r1; try (complete (simpl; tcsp));[]
                |rewrite substcv_mk_cv_app_r2; try (complete (simpl; tcsp));[]
                |rewrite substcv_mk_cv_app_r3; try (complete (simpl; tcsp));[]
         ]).

  apply tequality_function; dands; eauto 3 with slow.

  introv xt ecs.

  eapply equality_monotone in ea;[|eauto].
  eapply equality_monotone in ef;[|eauto].

  assert (safe_library lib') as safe' by eauto 3 with slow.

  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  autorewrite with slow.
  apply equality_in_csname_implies_equality_in_nat2nat in ef; auto.

  apply tequality_mkc_equality_if_equal; eauto 3 with slow.
  apply equality_nat2nat_apply; auto.
Qed.
Hint Resolve tequality_not_const_c : slow.

Lemma computes_to_valc_nat_implies_equality_in_nat {o} :
  forall (lib : @library o) t u k,
    computes_to_valc lib t (mkc_nat k)
    -> computes_to_valc lib u (mkc_nat k)
    -> equality lib t u mkc_tnat.
Proof.
  introv compa compb.
  apply equality_in_tnat.
  apply in_ext_implies_all_in_ex_bar; introv ext.
  exists k; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_nat_implies_equality_in_nat : slow.

Lemma computes_to_cs_implies_equality_in_nat2nat {o} :
  forall (lib : @library o) a b cs,
    safe_library lib
    -> compatible_choice_sequence_name 0 cs
    -> computes_to_valc lib a (mkc_choice_seq cs)
    -> computes_to_valc lib b (mkc_choice_seq cs)
    -> equality lib a b nat2nat.
Proof.
  introv safe compat compa compb.
  apply equality_in_csname_implies_equality_in_nat2nat; auto.
  apply equality_in_csname_iff.
  apply in_ext_implies_all_in_ex_bar; introv ext.
  exists cs; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve computes_to_cs_implies_equality_in_nat2nat : slow.

Fixpoint removen {A} n (l : list A) : list A :=
  match n with
  | 0 => l
  | S n =>
    match l with
    | [] => []
    | x :: xs => removen n xs
    end
  end.

Definition app_after {A} (l k : list A) : list A :=
  l ++ removen (length l) k.

Definition extend_choice_seq_entry_with {o}
           (name : choice_sequence_name)
           (e    : @ChoiceSeqEntry o)
           (k    : nat) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    match csn_kind name with
    | cs_kind_nat _ => MkChoiceSeqEntry _ (snoc vals (mkc_nat k)) restr
    | cs_kind_seq l =>
      MkChoiceSeqEntry _ (snoc (app_after vals (map mkc_nat l)) (mkc_nat k)) restr
    end
  end.

Definition choice_sequence_name2ext_cs_entry {o} (cs : choice_sequence_name) k : @ChoiceSeqEntry o :=
  extend_choice_seq_entry_with cs (choice_sequence_name2choice_seq_entry cs) k.

Fixpoint extend_choice_sequence_with {o}
         (lib : @library o)
         (cs  : choice_sequence_name)
         (k   : nat) : library :=
  match lib with
  | [] => [lib_cs cs (choice_sequence_name2ext_cs_entry cs k)]
  | lib_cs name cse as e :: entries =>
    if choice_sequence_name_deq name cs
    then lib_cs name (extend_choice_seq_entry_with name cse k) :: entries
    else e :: extend_choice_sequence_with entries cs k
  | e :: entries => e :: extend_choice_sequence_with entries cs k
  end.

Lemma entry_in_library_extends_choice_sequence_with_implies {o} :
  forall entry (lib : @library o) name k,
    entry_in_library entry (extend_choice_sequence_with lib name k)
    <->
    (
      (entry2name entry <> entry_name_cs name
       /\ entry_in_library entry lib)
      \/
      (exists e,
          entry = lib_cs name (extend_choice_seq_entry_with name e k)
          /\ find_cs lib name = Some e)
      \/
      (find_cs lib name = None
       /\ entry = lib_cs name (choice_sequence_name2ext_cs_entry name k))
    ).
Proof.
  induction lib; split; introv i; simpl in *; repndors; subst;
    simpl in *; tcsp;[| | |].

  { destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp;
      repndors; repnd; GC; subst; tcsp.

    { right; left; eauto. }

    { left; dands; tcsp.
      introv xx.
      destruct entry; simpl in *; ginv.
      unfold matching_entries in *; simpl in *; tcsp. }

    { left; dands; tcsp.
      introv xx; simpl in *; ginv; tcsp. }

    { applydup IHlib in i; repndors; exrepnd; subst; tcsp.
      right; left; eauto. }

    { simpl; left; dands; tcsp.
      introv xx; ginv. }

    { applydup IHlib in i; repndors; exrepnd; subst; tcsp.
      right; left; eauto. } }

  { repnd; repndors; subst; tcsp; destruct a; simpl in *; ginv; boolvar; subst;
      simpl in *; repnd; tcsp; right; dands; tcsp; apply IHlib; tcsp. }

  { exrepnd; subst; simpl in *; destruct a; simpl in *; boolvar; subst; GC;
      ginv; tcsp; simpl in *; tcsp;
        right; dands; tcsp; apply IHlib; tcsp; right; left; eauto. }

  { repnd; subst; simpl in *; destruct a; simpl in *; boolvar; subst; GC;
      ginv; tcsp; simpl in *; tcsp;
        right; dands; tcsp; apply IHlib; tcsp; right; left; eauto. }
Qed.

Lemma entry_in_library_implies_extends_choice_sequence_with {o} :
  forall entry (lib : @library o) name k,
    entry_in_library entry lib
    ->
    (entry2name entry <> entry_name_cs name
     /\ entry_in_library entry (extend_choice_sequence_with lib name k))
    \/
    (exists cse,
        entry = lib_cs name cse
        /\ entry_in_library
             (lib_cs name (extend_choice_seq_entry_with name cse k))
             (extend_choice_sequence_with lib name k)).
Proof.
  induction lib; introv i; simpl in *; tcsp; repndors; repnd; subst; simpl in *; tcsp;
    destruct a; simpl in *; boolvar; subst; simpl in *; tcsp.

  { right.
    eexists; eexists; dands; eauto. }

  { left; dands; tcsp.
    introv xx; ginv; tcsp. }

  { left; dands; tcsp.
    introv xx; ginv; tcsp. }

  { applydup (IHlib name k) in i; repndors; exrepnd; subst; tcsp.
    destruct i0; simpl; tcsp. }

  { applydup (IHlib name k) in i; repndors; exrepnd; subst; tcsp.
    right.
    eexists; dands; eauto. }

  { applydup (IHlib name k) in i; repndors; exrepnd; subst; tcsp.
    right.
    eexists; dands; eauto. }
Qed.

Lemma sublist_cterm_is_nth_implies {o} :
  forall (vals : @ChoiceSeqVals o) l,
    (forall n v, select n vals = Some v -> cterm_is_nth v n l)
    -> length vals <= length l
    -> exists l1 l2, l = l1 ++ l2 /\ vals = map mkc_nat l1.
Proof.
  induction vals; introv imp len; simpl in *.
  { exists ([] : list nat) l; simpl; tcsp. }

  destruct l; simpl in *; ginv; try omega; ginv.
  pose proof (IHvals l) as IHvals.
  repeat (autodimp IHvals hyp); try omega.
  { introv sel.
    pose proof (imp (S n0) v) as imp; simpl in *; tcsp. }
  exrepnd; subst.
  pose proof (imp 0 a) as imp; simpl in *; autodimp imp hyp.
  unfold cterm_is_nth in *; simpl in *; exrepnd; ginv.
  exists (i :: l1) l2; dands; simpl; tcsp.
Qed.

Lemma choice_sequence_entry_extend_extend_choice_seq_entry_with {o} :
  forall name k (cse : @ChoiceSeqEntry o),
    compatible_choice_sequence_name 0 name
    -> choice_sequence_entry_extend (extend_choice_seq_entry_with name cse k) cse.
Proof.
  introv comp.
  destruct cse as [vals restr]; simpl.
  destruct name as [name kind]; simpl.
  unfold compatible_choice_sequence_name in *; simpl in *; repnd.
  unfold correct_restriction in *; simpl in *.
  destruct kind; simpl; boolvar; simpl; tcsp;
    unfold choice_sequence_entry_extend; simpl; dands; subst;
      eauto 3 with slow;
      try (complete (exists [@mkc_nat o k]; rewrite snoc_as_append; auto));[].
  exists (snoc (removen (length vals) (map (@mkc_nat o) l)) (mkc_nat k)).
  unfold app_after.
  rewrite <- snoc_append_l; auto.
Qed.
Hint Resolve choice_sequence_entry_extend_extend_choice_seq_entry_with : slow.

Lemma lib_extends_entries_extend_choice_sequence_with {o} :
  forall (lib : @library o) name k,
    compatible_choice_sequence_name 0 name
    -> lib_extends_entries (extend_choice_sequence_with lib name k) lib.
Proof.
  introv comp i.
  apply (entry_in_library_implies_extends_choice_sequence_with _ _ name k) in i.
  repndors; exrepnd; subst; simpl; eauto 3 with slow;[].
  eapply entry_extends_preserves_entry_in_library_extends;
    [|apply entry_in_library_implies_entry_in_library_extends;eauto].
  simpl in *; dands; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_entries_extend_choice_sequence_with : slow.

Lemma choice_sequence_satisfies_restriction_snoc_nat {o} :
  forall k vals (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> choice_sequence_satisfies_restriction vals restr
    -> choice_sequence_satisfies_restriction (snoc vals (mkc_nat k)) restr.
Proof.
  introv comp sat.
  unfold is_nat_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; repnd; tcsp.
  introv i.
  rewrite select_snoc_eq in i; boolvar; ginv; tcsp.
  rewrite comp; eauto 3 with slow.
Qed.
Hint Resolve choice_sequence_satisfies_restriction_snoc_nat : slow.

Lemma length_removen :
  forall {A} n (l : list A),
    length (removen n l) = length l - n.
Proof.
  induction n; introv; simpl in *; autorewrite with nat; auto.
  destruct l; simpl in *; auto.
Qed.
Hint Rewrite @length_removen : list.

Lemma removen_all :
  forall {A} n (l : list A),
    length l <= n
    -> removen n l = [].
Proof.
  induction n; introv len; simpl in *; tcsp.
  { destruct l; simpl in *; try omega; auto. }

  destruct l; simpl in *; auto.
  apply IHn; auto; try omega.
Qed.

Lemma select_sub_removen :
  forall {A} m n (l : list A),
    m <= n
    -> select (n - m) (removen m l)
       = select n l.
Proof.
  induction m; introv len; simpl in *; autorewrite with nat; auto.
  destruct l; simpl; autorewrite with list; auto.
  destruct n; simpl; try omega.
  apply IHm; try omega.
Qed.

Lemma choice_sequence_satisfies_restriction_snoc_seq {o} :
  forall k l vals (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l restr
    -> choice_sequence_satisfies_restriction vals restr
    -> choice_sequence_satisfies_restriction
         (snoc (app_after vals (map mkc_nat l)) (mkc_nat k))
         restr.
Proof.
  introv comp sat.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; repnd; tcsp.
  introv i.
  unfold app_after in i.
  destruct (le_dec (length l) (length vals)) as [d1|d1].

  { rewrite removen_all in i; autorewrite with list in *; try omega.
    rewrite select_snoc_eq in i; boolvar; simpl in *; ginv; tcsp.
    apply comp; eauto 3 with slow; try omega. }

  { rewrite select_snoc_eq in i.
    autorewrite with list in *.
    rewrite le_plus_minus_r in i; try omega.
    boolvar; ginv.

    { destruct (lt_dec n (length vals)) as [d2|d2].

      { rewrite select_app_l in i; auto. }

      { rewrite select_app_r in i; try omega.
        rewrite select_sub_removen in i; try omega.
        rewrite select_map in i.
        remember (select n l) as sel; symmetry in Heqsel.
        destruct sel; simpl in *; ginv.
        apply comp2; auto.
        eexists; dands; eauto. } }

    { ginv; apply comp; eauto 3 with slow. } }
Qed.
Hint Resolve choice_sequence_satisfies_restriction_snoc_seq : slow.

Lemma safe_choice_sequence_entry_extend_choice_seq_entry_with {o} :
  forall name (e : @ChoiceSeqEntry o) k,
    compatible_choice_sequence_name 0 name
    -> safe_choice_sequence_entry name e
    -> safe_choice_sequence_entry name (extend_choice_seq_entry_with name e k).
Proof.
  introv comp safe.
  destruct e as [vals restr]; simpl in *; repnd.
  destruct name as [name kind]; simpl in *.
  unfold compatible_choice_sequence_name in *; simpl in *.
  unfold compatible_cs_kind in *; simpl in *.
  unfold correct_restriction in *; simpl in *.
  unfold safe_choice_sequence_entry.
  destruct kind; simpl in *; tcsp; subst; simpl in *; boolvar; simpl in *;
    GC; dands; eauto 3 with slow.
Qed.
Hint Resolve safe_choice_sequence_entry_extend_choice_seq_entry_with : slow.

Lemma safe_library_extend_choice_sequence_with {o} :
  forall (lib : @library o) name k,
    compatible_choice_sequence_name 0 name
    -> safe_library lib
    -> safe_library (extend_choice_sequence_with lib name k).
Proof.
  introv comp safe i.
  apply entry_in_library_extends_choice_sequence_with_implies in i.
  repndors; exrepnd; subst; tcsp.

  { apply find_cs_some_implies_entry_in_library in i0; apply safe in i0.
    simpl in *; eauto 3 with slow. }

  { simpl; dands; eauto 3 with slow.
    unfold choice_sequence_name2ext_cs_entry; simpl.
    unfold compatible_choice_sequence_name in comp.
    destruct name as [name kind]; simpl in *.
    unfold safe_choice_sequence_entry; simpl.
    destruct kind; subst; simpl in *; tcsp.

    { unfold correct_restriction; simpl; boolvar; subst; dands; eauto 3 with slow; tcsp.
      { unfold choice_sequence_name2restriction; simpl; dands; tcsp. }
      { unfold choice_sequence_name2restriction; simpl; dands; tcsp.
        introv i; repeat (destruct n; simpl in *; tcsp); ginv; eauto 3 with slow. } }

    { unfold compatible_cs_kind in comp; simpl in *; GC.
      unfold choice_sequence_name2restriction; simpl.
      unfold correct_restriction; simpl; dands; tcsp; eauto 3 with slow.
      introv i; eauto 3 with slow.
      unfold app_after in *; simpl in *.
      rewrite select_snoc_eq in i; allrw map_length; boolvar; simpl in *; tcsp.
      { rewrite select_map in i.
        unfold option_map in i.
        remember (select n l) as sel; destruct sel; ginv; symmetry in Heqsel.
        unfold natSeq2restrictionPred; allrw; auto. }
      { subst; ginv; eauto 3 with slow.
        unfold natSeq2restrictionPred.
        rewrite select_none; eauto 3 with slow. } } }
Qed.
Hint Resolve safe_library_extend_choice_sequence_with : slow.

Lemma subset_library_extend_choice_sequence_with {o} :
  forall (lib : @library o) name k,
    compatible_choice_sequence_name 0 name
    -> subset_library lib (extend_choice_sequence_with lib name k).
Proof.
  induction lib; introv comp i; simpl in *; tcsp; repndors; subst; tcsp.

  { destruct entry1; simpl in *; boolvar; subst; simpl; tcsp;
      eexists; dands; eauto; simpl; dands; eauto 3 with slow. }

  { applydup (IHlib name k) in i; auto; exrepnd.
    destruct a; simpl; boolvar; tcsp; subst; simpl in *; eauto.
    exists entry1; dands; tcsp; eauto 3 with slow. }
Qed.
Hint Resolve subset_library_extend_choice_sequence_with : slow.

Lemma lib_extends_extend_choice_sequence_with {o} :
  forall (lib : @library o) name k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> lib_extends (extend_choice_sequence_with lib name k) lib.
Proof.
  introv safe comp.
  split; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_extend_choice_sequence_with : slow.

Definition size_of_cs {o} (lib : @library o) (cs : choice_sequence_name) : nat :=
  match find_cs lib cs with
  | Some e => length (cse_vals e)
  | None => 0
  end.

Hint Rewrite length_snoc : list.

Lemma find_value_of_cs_at_extend_choice_seq_entry_with {o} :
  forall name (entry : @ChoiceSeqEntry o) k,
    find_value_of_cs_at
      (extend_choice_seq_entry_with name entry k)
      (Nat.pred (length (cse_vals (extend_choice_seq_entry_with name entry k))))
    = Some (mkc_nat k).
Proof.
  introv.
  destruct entry; simpl.
  destruct name as [name kind]; simpl.
  destruct kind; simpl; tcsp; autorewrite with list; simpl; tcsp;
    rewrite find_value_of_cs_at_is_select;
    rewrite select_snoc_eq; boolvar; tcsp; try omega.
Qed.


Lemma find_cs_value_at_in_extend_choice_sequence_with {o} :
  forall name k (lib : @library o),
    find_cs_value_at
      (extend_choice_sequence_with lib name k)
      name
      (Nat.pred (size_of_cs (extend_choice_sequence_with lib name k) name)) =
    Some (mkc_nat k).
Proof.
  induction lib; introv; simpl.

  { unfold find_cs_value_at; simpl; boolvar; tcsp; GC.
    unfold size_of_cs; simpl; boolvar; tcsp; GC.
    simpl.
    unfold choice_sequence_name2ext_cs_entry; simpl.
    destruct name as [name kind]; simpl.
    destruct kind; simpl; tcsp.
    unfold app_after; simpl.
    autorewrite with list; simpl.
    rewrite find_value_of_cs_at_is_select.
    rewrite select_snoc_eq; autorewrite with list; boolvar; try omega; auto. }

  destruct a; boolvar; subst; simpl in *; tcsp.

  { unfold find_cs_value_at; simpl; boolvar; tcsp; GC.
    unfold size_of_cs; simpl; boolvar; tcsp; GC.
    rewrite find_value_of_cs_at_extend_choice_seq_entry_with; auto. }

  { unfold find_cs_value_at in *; simpl; boolvar; tcsp.
    unfold size_of_cs in *; simpl in *; boolvar; tcsp. }
Qed.
