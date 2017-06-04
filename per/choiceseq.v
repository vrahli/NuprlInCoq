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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export nuprl.
Require Export nat_defs.


Definition memNat {o} : @Mem o :=
  fun c T => exists (n : nat), c = mkc_nat n.

Definition nmember {o} := @member o memNat.

Definition const0 {o} : nat -> @CTerm o := fun n => mkc_nat 0.

Definition seq0 : choice_sequence_name := "seq0".

Definition lib0 {o} : @library o :=
  [lib_cs seq0 (MkChoiceSeqEntry _ [] (csc_coq_law const0))].

Lemma isprog_mk_choice_seq {o} :
  forall (n : choice_sequence_name), @isprog o (mk_choice_seq n).
Proof.
  introv; apply isprog_eq; apply isprogram_mk_choice_seq.
Qed.

Definition mkc_choice_seq {o} name : @CTerm o :=
  exist isprog (mk_choice_seq name) (isprog_mk_choice_seq name).

Definition Nat2Nat {o} : @CTerm o := mkc_fun mkc_Nat mkc_Nat.

Lemma iscvalue_mkc_Nat {o} : @iscvalue o mkc_Nat.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_Nat : slow.

Hint Rewrite @csubst_mk_cv : slow.

Lemma fresh_choice_sequence_name : FreshFun choice_sequence_name.
Proof.
  unfold FreshFun.
  introv.

  exists (String.append "x" (append_string_list l)).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].

  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list l))) as e.
  { rewrite k at 1; auto. }
  allrw string_length_append.
  omega.
Defined.

Fixpoint library2choice_sequence_names {o} (lib : @library o) : list choice_sequence_name :=
  match lib with
  | [] => []
  | lib_cs name _ :: entries => name :: library2choice_sequence_names entries
  | _ :: entries => library2choice_sequence_names entries
  end.

Lemma not_in_library2choice_sequence_names_iff_find_cs_none {o} :
  forall (lib : @library o) (name : choice_sequence_name),
    !LIn name (library2choice_sequence_names lib)
    <-> find_cs lib name = None.
Proof.
  induction lib; simpl; introv; split; intro h; tcsp; destruct a; simpl in *; tcsp.

  - allrw not_over_or; repnd.
    boolvar; subst; tcsp.
    apply IHlib; auto.

  - apply IHlib; auto.

  - boolvar; tcsp.
    allrw not_over_or; dands; tcsp.
    apply IHlib; auto.

  - apply IHlib; auto.
Qed.

Lemma fresh_choice_seq_name_in_library {o} :
  forall (lib : @library o),
  exists (name : choice_sequence_name),
    find_cs lib name = None.
Proof.
  introv.
  pose proof (fresh_choice_sequence_name (library2choice_sequence_names lib)) as q.
  exrepnd.
  exists x.
  apply not_in_library2choice_sequence_names_iff_find_cs_none; auto.
Qed.

Definition library2infinite {o} (lib : @library o) (d : library_entry) : inf_library :=
  fun n => nth n lib d.

Definition simple_choice_seq {o} (name : choice_sequence_name) : @library_entry o :=
  lib_cs name (MkChoiceSeqEntry _ [] csc_no).

Lemma shift_inf_lib_library2infinite_cons {o} :
  forall entry (lib : @library o) d,
    shift_inf_lib (library2infinite (entry :: lib) d)
    = library2infinite lib d.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold shift_inf_lib; simpl; auto.
Qed.

Lemma entry_not_in_lib_cons_implies_entry_not_in_lib {o} :
  forall d entry (lib : @library o),
    entry_not_in_lib d (entry :: lib)
    -> entry_not_in_lib d lib.
Proof.
  introv e i.
  apply e; simpl; clear e.
  unfold in_lib in *; simpl.
  exrepnd.
  exists e; tcsp.
Qed.

Lemma inf_lib_extends_library2infinite {o} :
  forall (lib : @library o) d,
    inf_lib_extends (library2infinite lib d) lib.
Proof.
  induction lib; introv; simpl in *; auto.
  dands; auto.
  rewrite shift_inf_lib_library2infinite_cons.
  apply IHlib.
Qed.
Hint Resolve inf_lib_extends_library2infinite : slow.

Lemma bar_non_empty {o} :
  forall {M} {lib} (bar : @BarLib o M lib),
  exists (lib' : library),
    List.In lib' (bar_lib_bar bar).
Proof.
  introv.
  destruct bar as [bar cond].
  destruct bar as [|lib' bar]; simpl in *;[|exists lib'; tcsp].
  assert False; tcsp.
  unfold BarLibCond in cond.

  pose proof (fresh_choice_seq_name_in_library lib) as h; exrepnd.

  pose proof (cond (library2infinite lib (simple_choice_seq name))) as q; clear cond.
  autodimp q hyp; eauto 2 with slow.

  exrepnd; simpl in *; tcsp.
Qed.

Lemma safe_library_lib0 {o} : forall M, @safe_library o M lib0.
Proof.
  introv i.
  unfold lib0 in i; simpl in i; repndors; tcsp; subst.
  simpl; introv k; omega.
Qed.

Definition entry2restriction {o} (e : @ChoiceSeqEntry o) : ChoiceSeqRestriction :=
  match e with
  | MkChoiceSeqEntry _ vals restriction => restriction
  end.

Lemma exists_bar {o} :
  forall (M    : Mem)
         (lib  : @library o)
         (name : choice_sequence_name)
         (e    : ChoiceSeqEntry)
         (n    : nat)
         (f    : nat -> CTerm),
    safe_library M lib
    -> find_cs lib name = Some e
    -> entry2restriction e = csc_coq_law f
    -> exists (bar : BarLib M lib),
      forall (lib' : library),
        List.In lib' (bar_lib_bar bar)
        -> find_cs_value_at lib' name n = Some (f n).
Proof.
  introv safe find law.

Qed.

Lemma seq0_in_nat2nat {o} :
  @nmember o lib0 (mkc_choice_seq seq0) Nat2Nat.
Proof.
  unfold Nat2Nat, nmember, member, equality.
  eexists; dands.

  {
    apply CL_func.
    unfold per_func_ext.
    eexists; eexists.
    dands;[|apply eq_term_equals_refl].

    unfold type_family_ext.
    allrw <- @fold_mkc_fun.
    eexists; eexists; eexists; eexists; eexists; eexists.
    dands.

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      apply CL_nat.
      unfold per_nat_bar.
      dands.

      {
        assert (BarLib memNat lib') as bar.
        {
          exists [lib'].
          unfold BarLibCond.
          introv j.
          exists lib'; simpl; dands; tcsp.
          eauto 2 with slow.
        }
        exists bar.
        dands; auto.

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }
      }

      {
        apply eq_term_equals_refl.
      }
    }

    {
      introv i; introv.
      autorewrite with slow.
      apply CL_nat.
      unfold per_nat_bar.
      dands.

      {
        assert (BarLib memNat lib') as bar.
        {
          exists [lib'].
          unfold BarLibCond.
          introv j.
          exists lib'; simpl; dands; tcsp.
          eauto 2 with slow.
        }
        exists bar.
        dands; auto.

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }
      }

      {
        apply eq_term_equals_refl.
      }
    }
  }

  {
    unfold per_func_eq.
    introv i e.
    unfold equality_of_nat_bar in *; exrepnd.

    pose proof (bar_non_empty bar) as q; exrepnd.
    applydup e0 in q0; exrepnd; clear e0; spcast.

    match goal with
    | [ H : lib_extends _ _ _ |- _ ] =>
      dup H as safe; apply lib_extends_preserves_safe in safe;[|apply safe_library_lib0]
    end.

  }

Qed.