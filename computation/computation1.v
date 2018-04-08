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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export substitution.
Require Export library.
Require Export terms_pk.
Require Export terms_choice.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)

(* begin hide *)

Definition compute_step_apply_not_well_formed := "lambda or apply not well-formed".
(*Definition compute_step_apseq_not_well_formed := "apseq not well-formed".*)
Definition bad_first_arg := "bad first arg".
Definition fix_not_well_formed := "fix not well-formed".
Definition spread_or_pair_not_well_formed := "spread or pair not well-formed".
Definition bad_first_arg_to_spread := "bad first arg to spread".
Definition sup_or_dsup_not_well_formed := "sup or dsup not well-formed".
Definition bad_first_arg_to_dsup := "bad first arg to dsup".
Definition injection_or_decide_not_well_formed := "injection or decide not well-formed".
Definition bad_args_to_decide := "bad args to decide".
Definition callbyvalue_not_well_formed := "callbyvalue not well-formed".
Definition inappropriate_args_to_try := "inappropriate args to try".
Definition inappropriate_args_to_catch := "inappropriate args to catch".
Definition canonical_form_test_not_well_formed := "canonical form test not well-formed".
Definition arithmetic_operation_not_well_formed := "arithmetic operation not well-formed".
Definition too_few_args_to_arith_op := "too few args to arith op".
Definition cop_not_a_closed_term := "cop: not a closed term".
Definition cop_malformed_2nd_arg := "cop: malformed 2nd arg".
Definition bad_args := "bad args".
Definition too_few_args_to_comparison_op := "too few args to comparison op".
Definition sleep_not_well_formed := "sleep not well-formed".
Definition tuni_not_well_formed := "tuni not well-formed".
Definition minus_not_well_formed := "minus not well-formed".
Definition compute_step_error_not_closed := "not closed".
Definition compute_step_error_abs := "abstraction".
Definition too_few_args_to_parallel := "too few args to parallel".
Definition parallel_malformed_2nd_arg := "parallel: malformed 2nd arg".


Inductive Comput_Result {p} : tuniv :=
| csuccess   : @NTerm p -> Comput_Result
| cfailure   : String.string-> @NTerm p -> Comput_Result.


Definition on_success {p} (c : @Comput_Result p) (f : NTerm -> NTerm) :=
  match c with
    | csuccess t => csuccess (f t)
    | cfailure s t => cfailure s t
  end.

(* end hide *)

(*
    To understand where the arguments to these
    definitions come from, we will present them in the
    context of the [t], original term that we
    are computing with when these functions are invoked.
    We will also remind the reader of the
    binding structure of the
    noncanonical [Opid].
*)

(** %\noindent \\*%
  Now we define the functions -- compute_step_apply, compute_step_fix, etc. --
  that perform a computation step on each of the noncanonicals forms.
  We preface each with a reminder of the operator's binding structure and
  the structure of [t], the original term we were computing with when the
  function was called.

  These definitions are
  used above in the pattern matching(on [ncr]) that is nested inside
  in the definition of [compute_step] above. So, while
  defining these functions, we know that
  the first argument of the head [Opid]
  of the original term is already canonical.

** [NApply]

    %\noindent% We begin with [NApply].


    %\noindent% [OpBindings (NCan NApply) = [0,0]]


    %\noindent% [t = oterm (NCan NApply) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)

Definition compute_step_apply {p}
           (arg1c:@CanonicalOp p)
           (t:@NTerm p)
           (arg1bts btsr: list BTerm) :=
  match arg1c with
    | NLambda =>
      match arg1bts, btsr with
        | [bterm [v] b], [bterm [] arg] =>
          csuccess (apply_bterm (bterm [v] b) [arg])
        | _,_ => cfailure compute_step_apply_not_well_formed t
      end
    | Ncseq name =>
      match arg1bts, btsr with
        | [], [bterm [] arg] => csuccess (mk_eapply (mk_choice_seq name) arg)
        | _,_ => cfailure compute_step_apply_not_well_formed t
      end
    | _ => cfailure bad_first_arg t
  end.

(*
Definition compute_step_apseq {o}
           (f     : nseq)
           (arg1c : @CanonicalOp o)
           (t     : @NTerm o)
           (arg1bts btsr : list (@BTerm o)) :=
  match arg1c with
    | Nint z =>
      match arg1bts, btsr with
        | [],[] =>
          if Z_le_gt_dec 0 z
          then csuccess (mk_nat (f (Z.to_nat z)))
          else cfailure compute_step_apseq_not_well_formed t
        | _,_ => cfailure compute_step_apseq_not_well_formed t
      end
    | _ => cfailure bad_first_arg t
  end.
*)

Definition compute_step_eapply2 {o}
           lib
           (t arg1 arg2 : @NTerm o)
           (bs : list (@BTerm o)) :=
  match bs with
  | [] =>
    match arg1 with
    | oterm (Can NLambda) [bterm [v] b] => csuccess (apply_bterm (bterm [v] b) [arg2])
    | oterm (Can (Ncseq name)) [] =>
      match arg2 with
      | oterm (Can (Nint z)) [] =>
        if Z_le_gt_dec 0 z
        then
          match find_cs_value_at lib name (Z.to_nat z) with
          | Some u => csuccess (CSVal2term u)
          | None => cfailure bad_args t
          end
        else cfailure bad_args t
      | _ => cfailure bad_args t
      end
    | _ => cfailure bad_args t
    end
  | _ => cfailure bad_args t
  end.

Definition compute_step_eapply1 {o}
           lib
           (bs    : list BTerm)
           (t     : @NTerm o)
           (cstep : Comput_Result)
           (arg1  : NTerm)
           (ncr   : NonCanonicalOp) :=
  match bs with
  | [] => cfailure bad_args t
  | bterm (_ :: _) _ :: _ => cfailure bad_args t
  | bterm [] (vterm _) :: _ => cfailure bad_args t
  | bterm [] (oterm (Can _) _ as arg2) :: bs2 =>
    compute_step_eapply2 lib t arg1 arg2 bs2
  | bterm [] (oterm Exc _ as arg2) :: _ => csuccess arg2
  | bterm [] (oterm _ _) :: bs2 => (* ncan/abs *)
    on_success cstep (fun f => oterm (NCan ncr) (nobnd arg1 :: nobnd f :: bs2))
  end.

Definition eapply_wf {o} (t : @NTerm o) :=
  match t with
    | oterm (Can (Ncseq _)) [] => true
    | oterm (Can NLambda) [bterm [_] _] => true
    | _ => false
  end.

Definition eapply_wf_def {o} (t : @NTerm o) :=
  {name : choice_sequence_name & t = mk_choice_seq name}
  [+] {v : NVar & {b : NTerm & t = mk_lam v b}}.

Lemma eapply_wf_dec {o} :
  forall (t : @NTerm o), decidable (eapply_wf_def t).
Proof.
  introv.
  destruct t as [v|op bs]; allsimpl; tcsp;
  try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
  destruct op; allsimpl; tcsp;
    try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
    destruct c; allsimpl; tcsp;
    try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
    { destruct bs as [|b bs]; allsimpl; tcsp;
      try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
      destruct bs as [|? bs]; allsimpl; tcsp;
      try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
      destruct b as [l t].
      destruct l as [|v l]; allsimpl; tcsp;
      try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
      destruct l as [|? l]; allsimpl; tcsp;
      try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
      left; right; eexists; eexists; unfold mk_lam; dands; eauto. }
    { destruct bs as [|b bs]; allsimpl; tcsp;
      try (complete (right;unfold eapply_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv)).
      left; left; eexists; unfold mk_choice_seq; eauto. }
Qed.

Definition compute_step_eapply {o}
           lib
           (bs    : list BTerm)
           (t     : @NTerm o)
           (cstep : Comput_Result)
           (arg1  : NTerm)
           (ncr   : NonCanonicalOp) :=
  if eapply_wf arg1
  then compute_step_eapply1 lib bs t cstep arg1 ncr
  else cfailure bad_args t.



(** ** [NFix] %\label{sec:comp:step:NFix}%
 %\noindent% [NFix] that behaves very much
    like the Y combinator.
    Note that because of the way [compute_step] was defined,
    the following [compute_step_fix] gets invoked
    only when the only argument to [NFix] is in
    canonical form.
    This informally means that
    $fix(f)$ reduces to $f \; (fix f)$ only when
    $f$ is already in canonical (normal) form.
    Otherwise a step of computation will
    only evaluate $f$ further.
    This is unlike the way Crary defined it in
    %\cite{Crary:1998}%, where
    $fix(f)$ always reduces to $f \; (fix f)$
    (even if $f$ is not in canonical form).
    Our change was mainly motivated by
    the simplicity of [compute_step] definition
    when the first argument of all noncanonical
    operators is principal.
    Our change was mainly motivated by noting that
    the definition of [compute_step] is simpler if
    the first argument of all noncanonical operators is
    principal. One could also argue that our new definition
    avoids the duplication of computation that results from
    having to reduce f to canonical form after each unfolding of fix.



    It turned out (later) that some Crary's proofs
    domain theoretic properties of  $fix$ critically
    dependend on $fix(f)$ always reducing to $f \; (fix f)$.
    With some non-trivial effort, we were able to
    restore these properties even for our new
    operational semantics of [NFix].
    We will describe
    these new proofs later in this chapter.


    %\noindent% [OpBindings (NCan NFix) = [0]]


    %\noindent% [t = oterm (NCan NFix) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)

Definition compute_step_fix {p}
           (t arg1 : @NTerm p)
           (bs : list (@BTerm p)) :=
  match bs with
    | [] => csuccess (mk_apply arg1 t)
    | _ => cfailure fix_not_well_formed t
  end.


(** ** [NSpread]
%\noindent% [NSpread] is the elimination
    form for [NPair].

    %\noindent% [OpBindings (NCan NSpread) = [0,2]]


    %\noindent% [t = oterm (NCan NSpread) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]


 *)

Definition compute_step_spread {p}
           (arg1c:@CanonicalOp p)
           (t:NTerm)
           (arg1bts btsr: list (@BTerm p)) :=
  match arg1c with
    | NPair =>
      match (arg1bts, btsr) with
        | ([bterm [] a, bterm [] b], [bterm [va,vb] t]) =>
          csuccess (apply_bterm (bterm [va,vb] t) [a,b])
        | _ => cfailure spread_or_pair_not_well_formed t
      end
    | _ => cfailure bad_first_arg_to_spread t
  end.

(** ** [NDsup]
%\noindent % [NDsup] behaves exactly like [NSpread]
    on [NSup] which is exactly like [NPair].

    %\noindent% [OpBindings (NCan NDsup) = [0,2]]


    %\noindent% [t = oterm (NCan NDsup) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)

Definition compute_step_dsup {p}
           (arg1c:@CanonicalOp p)
           (t:NTerm)
           (arg1bts btsr: list (@BTerm p)) :=
  match arg1c with
    | NSup =>
      match (arg1bts, btsr) with
        | ([bterm [] a, bterm [] b], [bterm [va,vb] t]) =>
          csuccess (apply_bterm (bterm [va,vb] t) [a,b])
        | _ => cfailure sup_or_dsup_not_well_formed t
      end
    | _ => cfailure bad_first_arg_to_dsup t
  end.


(** ** [NDecide]
%\noindent% [NDecide] is the elimination
    form for [NInl] and [NInr].

    %\noindent% [OpBindings (NCan NDecide) = [0,1,1]]

    %\noindent% [t = oterm (NCan NDecide) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)

Definition compute_step_decide {p}
           (arg1c:@CanonicalOp p)
           (t:NTerm)
           (arg1bts btsr: list (@BTerm p)) :=
  match arg1c with
    | NInj ni =>
      match arg1bts, btsr with
        | [bterm [] u] , [bterm [v1] t1, bterm [v2] t2] =>
          match ni with
            | NInl => csuccess (apply_bterm (bterm [v1] t1) [u])
            | NInr => csuccess (apply_bterm (bterm [v2] t2) [u])
          end
        | _, _ => cfailure injection_or_decide_not_well_formed t
      end
    | _ => cfailure bad_args_to_decide t
  end.

(** ** [NCbv]
  %\noindent% [NCbv] that is the call-by-value form
    of application.

    %\noindent% [OpBindings (NCan NCbv) = [0,1]]

    %\noindent% [t = oterm (NCan NCbv) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)

Definition compute_step_cbv {p}
           (t arg1 :NTerm)
           (btsr : list (@BTerm p)) :=
  match btsr with
    | [bterm [vs] t] => csuccess (apply_bterm (bterm [vs] t) [arg1])
    | _ => cfailure callbyvalue_not_well_formed t
  end.


(** ** [NTryCatch]
  %\noindent% [NTryCatch] is a feature still under development.
  If the first argument of [NTryCatch] is a value then we simply return it.

*)

Definition compute_step_try {p}
           (t arg1 : NTerm)
           (btsr : list (@BTerm p)) :=
  match btsr with
    | [bterm [] a, bterm [_] _] =>
      csuccess (mk_atom_eq a a arg1 mk_bot)
    | _ => cfailure inappropriate_args_to_try t
  end.

Definition compute_step_catch {p}
           (nc : NonCanonicalOp)
           (t : @NTerm p)
           (arg1bts btsr : list BTerm) :=
  match nc with
    | NTryCatch =>
      match (btsr, arg1bts) with
        | ([bterm [] a, bterm [v] b], [bterm [] a', bterm [] e]) =>
          csuccess (mk_atom_eq a a' (subst b v e) (oterm Exc arg1bts))
        | _ => cfailure inappropriate_args_to_catch t
      end
    | _ => csuccess (oterm Exc arg1bts)
  end.


(** ** [NCanTest _]
  %\noindent% [NCanTest] was recently introduced in
    %\cite{Rahli+Bickford+Anand:2013}%. We first define the following
    helper function:

*)

Definition canonical_form_test_for {p} (test : CanonicalTest) (op : @CanonicalOp p) : bool :=
  match test, op with
    | CanIspair,   NPair     => true
    | CanIssup,    NSup      => true
    | CanIsaxiom,  NAxiom    => true
    | CanIslambda, NLambda   => true
    | CanIsint,    Nint _    => true
    | CanIsinl,    NInj NInl => true
    | CanIsinr,    NInj NInr => true
    | CanIsatom,   NTok _    => true
    | CanIsuatom,  NUTok _   => true
    | _, _ => false
  end.


(**

    %\noindent% [OpBindings (NCan (NCanTest _)) = [0,0,0]]

    %\noindent% [t = oterm (NCan (NCanTest _)) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

 *)


Definition compute_step_can_test {p}
           top
           (arg1c:@CanonicalOp p)
           (t:NTerm)
           (arg1bts btsr: list (@BTerm p)) :=
  match btsr with
    | [bterm [] arg2nt, bterm [] arg3nt] =>
      csuccess (if canonical_form_test_for top arg1c
                then arg2nt
                else arg3nt)
    | _ => cfailure canonical_form_test_not_well_formed t
  end.



(** ** [NArithOp _] and  [NCompOp _]
  %\noindent% The remaining two [NonCanonicalOp]s have the first two
    arguments as pricipal, instead of just the first one.
    Hence their definitions are a little more complicated
    as they might need to recursively evaluate their
    second argument if it is not canonical.

    To avoid confusing the termination analysis for these recursive calls,
    we define these as notations ([ca] and [co]). As evident
    from their use in [compute_step], the [cstep] argument in
    these notations represents the (recursive use of) [compute_step].

    The [NonCanonicalOp]s that represent arithmetic operations just
    call the corresponding coq functions and repackage the result
    into the corresponding Nuprl [Nint].
    [get_int_from_cop] below will
    be used to extract the corresponding
    Coq numbers out
    terms that represent Nuprl numbers.
*)


Definition is_comp_op {o} (op : ComparisonOp) (c : @CanonicalOp o) :=
  match op, c with
    | CompOpLess, Nint _  => True
    | CompOpEq,   Nint _  => True
    | CompOpEq,   NTok _  => True
    | CompOpEq,   NUTok _ => True
    | CompOpEq,   Ncseq _ => True
    | _,_ => False
  end.

(** [get_arith_op] returns the corresponding
    arithmetic operation of Coq. *)

Definition get_arith_op (a :ArithOp) : (Z->Z->Z) :=
  match a with
    | ArithOpAdd => Z.add
    | ArithOpMul => Z.mul
    | ArithOpSub => Z.sub
    | ArithOpDiv => Z.div
    | ArithOpRem => Z.rem
  end.


(* Atoms *)
Definition bare_atom_sub {o} := list (NVar # get_patom_set o).

Definition mematom {o} := memberb (get_patom_deq o).

Lemma assert_mematom {o} :
  forall (a : get_patom_set o) l,
    assert (mematom a l) <=> LIn a l.
Proof.
  introv; unfold mematom.
  rw @assert_memberb; sp.
Qed.

Definition bare_atom_sub_range {o} (s : @bare_atom_sub o) : list (get_patom_set o) :=
  map (fun x => snd x) s.

Definition bare_atom_sub_dom {o} (s : @bare_atom_sub o) : list NVar :=
  map (fun x => fst x) s.

Fixpoint wf_bare_atom_sub_b {o} (l : @bare_atom_sub o) : bool :=
  match l with
    | [] => true
    | (v,a) :: l =>
      negb (mematom a (bare_atom_sub_range l))
           && wf_bare_atom_sub_b l
  end.

Definition wf_bare_atom_sub {o} (s : @bare_atom_sub o) :=
  wf_bare_atom_sub_b s = true.

Lemma wf_bare_atom_sub_cons {o} :
  forall v a (s : @bare_atom_sub o),
    wf_bare_atom_sub ((v,a) :: s)
    <=> (!LIn a (bare_atom_sub_range s) # wf_bare_atom_sub s).
Proof.
  introv.
  unfold wf_bare_atom_sub; simpl.
  allrw andb_eq_true.
  rw negb_eq_true.
  rw @assert_mematom; sp.
Qed.

Lemma wf_bare_atom_sub_iff {o} :
  forall (s : @bare_atom_sub o),
    wf_bare_atom_sub s <=> no_repeats (bare_atom_sub_range s).
Proof.
  induction s; simpl; split; introv k; tcsp.
  - apply no_repeats_cons.
    destruct a; allsimpl.
    rw @wf_bare_atom_sub_cons in k; repnd.
    rw <- IHs; sp.
  - apply no_repeats_cons in k.
    destruct a; allsimpl.
    rw @wf_bare_atom_sub_cons; repnd.
    rw IHs; sp.
Qed.

Lemma wf_bare_atom_sub_proof_irrelevance {o} :
  forall (s : @bare_atom_sub o),
  forall x y : wf_bare_atom_sub s,
    x = y.
Proof.
  sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_bare_atom_sub ?s , H2 : wf_bare_atom_sub ?s |- _ ] =>
    pose proof (wf_bare_atom_sub_proof_irrelevance s H2 H1) as h; subst
end : pi.

(*
Definition atom_sub {o} :=
  {s : @bare_atom_sub o & wf_bare_atom_sub s}.
*)

(*
Definition in_atom_sub {o} v a (s : @atom_sub o) :=
  LIn (v,a) (projT1 s).

Definition atom_sub_dom {o} (s : @atom_sub o) : list NVar :=
  bare_atom_sub_dom (projT1 s).

Definition atom_sub_range {o} (s : @atom_sub o) : list (get_patom_set o) :=
  bare_atom_sub_range (projT1 s).

Definition is_fresh_atom {o} (s : @atom_sub o) (a : get_patom_set o) :=
  !LIn a (atom_sub_range s).

Lemma implies_wf_bare_atom_sub_cons {o} :
  forall v a (s : @bare_atom_sub o) (w : wf_bare_atom_sub s),
    is_fresh_atom (existT _ s w) a
    -> wf_bare_atom_sub ((v,a) :: s).
Proof.
  introv f.
  unfold is_fresh_atom in f; allsimpl.
  unfold atom_sub_range in f; allsimpl.
  apply wf_bare_atom_sub_cons; sp.
Qed.

Definition add_atom_sub {o}
           (s : @atom_sub o)
           (v : NVar)
           (a : get_patom_set o) : is_fresh_atom s a -> atom_sub :=
  match s with
    | existT l w => fun p => existT _ ((v,a) :: l) (implies_wf_bare_atom_sub_cons v a l w p)
  end.
*)

Definition atom_sub {o} := list (NVar # get_patom_set o).

Definition atom_sub_range {o} (s : @atom_sub o) : list (get_patom_set o) :=
  map (fun x => snd x) s.

Definition atom_sub_dom {o} (s : @atom_sub o) : list NVar :=
  map (fun x => fst x) s.

(* a better definition would say that ce_atom_sub does not contain atoms from
   either the library or the term we're computing.
   But then the definition will become messier.
 *)
Record compenv {o} :=
  {
    ce_library : @library o;
    ce_atom_sub : @atom_sub o
  }.

Definition add_atom_sub {o}
           (ce : @compenv o)
           (v : NVar)
           (a : get_patom_set o) : compenv :=
  {|
    ce_atom_sub := (v,a) :: ce_atom_sub ce;
    ce_library := ce_library ce
  |}.

(*
Definition ce_is_fresh_atom {o} (ce : @compenv o) (a : get_patom_set o) :=
  is_fresh_atom (ce_atom_sub ce) a.

Definition ce_add_atom {o}
           (ce : @compenv o)
           (v : NVar)
           (a : get_patom_set o)
           (p : ce_is_fresh_atom ce a) : compenv :=
  {|
    ce_atom_sub := add_atom_sub (ce_atom_sub ce) v a p;
    ce_library := ce_library ce
  |}.

Fixpoint find_bare_atom {o} (s : @bare_atom_sub o) (var : NVar) : option (get_patom_set o) :=
  match s with
    | nil => None
    | (v, t) :: xs => if beq_var v var then Some t else find_bare_atom xs var
  end.

Definition find_atom {o} (s : @atom_sub o) (v : NVar) :=
  find_bare_atom (projT1 s) v.
*)

Fixpoint find_atom {o} (s : @atom_sub o) (var : NVar) : option (get_patom_set o) :=
  match s with
    | nil => None
    | (v, t) :: xs => if beq_var v var then Some t else find_atom xs var
  end.

Definition compute_var {o} (v : NVar) (ce : @compenv o) (f : get_patom_set o -> @Comput_Result o) : Comput_Result :=
  match find_atom (ce_atom_sub ce) v with
    | None => cfailure compute_step_error_not_closed (vterm v)
    | Some a => f a
  end.


(* if we match on arg1c,arg2c instead, we get 22*22 cases when coq
       compiles it to simple match statements. *)

(** %\noindent% Here is the function that does one step of computation for
  [NArithOp] assuming both the principal arguments are canonical

    %\noindent% [OpBindings (NCan NArithOp _) = [0,0]]

[[

    t = oterm (NCan (NArithOp op)) ((bterm [] (oterm (Can arg1c) arg1bts))
                                 ::((bterm [] (oterm (Can arg2c) arg2bts)
                                 ::btsr)))

]]

*)

Definition compute_step_arith {p}
           (op : ArithOp)
           (arg1c arg2c: @CanonicalOp p)
           (arg1bts arg2bts btsr : list (@BTerm p))
           (t: @NTerm p) :=
  match arg1bts,arg2bts,btsr with
    | [],[],[] =>
      match get_param_from_cop arg1c , get_param_from_cop arg2c with
        | Some (PKi n1), Some (PKi n2) =>
          csuccess (oterm (Can (Nint ((get_arith_op op) n1 n2))) [])
        | _,_ => cfailure bad_args t
      end
    | _,_,_ => cfailure arithmetic_operation_not_well_formed t
  end.

(** %\noindent% Finally, here is the notation that uses the above function if the second argument
    is also canonical, and evaluates it for one step instead if it was non-canonical.
    In this notation, [cstep] refers to [compute_step].

    %\noindent% [t = oterm (NCan (NArithOp op)) ((bterm  [] (oterm (Can arg1c) arg1bts))::btsr)]

*)

Definition ca_aux {o} btsr (t : @NTerm o) arg1bts arg1c op cstep arg1 ncr :=
  match btsr with
    | []  => cfailure too_few_args_to_arith_op t
    | bterm (_ :: _) _ :: _ => cfailure cop_malformed_2nd_arg t
    | bterm [] (vterm v) :: btsr3 => cfailure compute_step_error_not_closed t
    | (bterm [] (oterm (Can arg2c) arg2bts)::btsr3) =>
      compute_step_arith op arg1c arg2c arg1bts arg2bts btsr3 t
    | bterm [] (oterm Exc _ as arg2nt) :: _ => csuccess arg2nt
    | bterm [] (oterm _ _) :: btsr3 => (* ncan/abs *)
      on_success cstep (fun f => oterm (NCan ncr) (bterm [] arg1::bterm [] f::btsr3))
  end.

Definition ca_wf {o} (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)) :=
  match arg1c, arg1bts with
    | Nint _, [] => true
    | _, _ => false
  end.

Definition ca_wf_def {o} (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)) :=
  {i : Z & arg1c = Nint i # arg1bts = []}.

Lemma ca_wf_dec {o} :
  forall (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)),
    decidable (ca_wf_def arg1c arg1bts).
Proof.
  introv.
  destruct arg1c; simpl; tcsp;
  try (complete (right;unfold ca_wf_def;intro x; exrepnd; ginv)).
  destruct arg1bts; tcsp;
  try (complete (right;unfold ca_wf_def;intro x; exrepnd; ginv)).
  left.
  unfold ca_wf_def.
  exists z; dands; auto.
Qed.

Definition ca {o} btsr (t : @NTerm o) arg1bts arg1c op cstep arg1 ncr :=
  if ca_wf arg1c arg1bts
  then ca_aux btsr t arg1bts arg1c op cstep arg1 ncr
  else cfailure bad_args t.


(** %\noindent% Finally, we define the case for [NCompOp]
    in a similar way as [NArithOp].

*)

(** %\noindent% [OpBindings (NCan NCompOp _) = [0,0,0,0]]

[[

t = oterm (NCan (NCompOp op)) ((bterm [] (oterm (Can arg1c) arg1bts))
                            ::((bterm [] (oterm (Can arg2c) arg2bts)
                            ::btsr)))

]]

*)

Definition compute_step_comp {p}
           (op : ComparisonOp)
           (arg1c arg2c: @CanonicalOp p)
           (arg1bts arg2bts btsr : list (@BTerm p))
           (t: NTerm) :=
  match (arg1bts,arg2bts,btsr) with
    | ([],[], [bterm [] arg3nt, bterm [] arg4nt]) =>
      match op with
        | CompOpLess =>
          match get_param_from_cop arg1c, get_param_from_cop arg2c with
            | Some (PKi n1), Some (PKi n2) => csuccess (if Z_lt_le_dec n1 n2 then arg3nt else arg4nt)
            | _, _ => cfailure bad_args t
          end
        | CompOpEq =>
          match get_param_from_cop arg1c, get_param_from_cop arg2c with
            | Some pk1, Some pk2 => csuccess (if param_kind_deq pk1 pk2 then arg3nt else arg4nt)
            | _, _ => cfailure bad_args t
          end
      end
    | _ => cfailure bad_args t
  end.




(**

    %\noindent% [t = oterm (NCan (NCompOp op)) ((bterm [] (oterm (Can arg1c) arg1bts))::btsr)]

*)


Definition co_aux {o} btsr (t : @NTerm o) arg1bts arg1c op cstep arg1 ncr :=
  match btsr with
    | [] => cfailure too_few_args_to_comparison_op t
    | bterm (_ :: _) _ :: _ => cfailure cop_malformed_2nd_arg t
    | bterm [] (vterm v) :: btsr3 => cfailure compute_step_error_not_closed t
    | bterm [] (oterm (Can arg2c) arg2bts) :: btsr3 =>
      compute_step_comp op arg1c arg2c arg1bts arg2bts btsr3 t
    | bterm [] (oterm Exc _ as arg2nt) :: _ => csuccess arg2nt
    | bterm [] (oterm _ _) :: btsr3 => (* ncan/abs *)
      on_success cstep (fun f => oterm (NCan ncr) (bterm [] arg1::bterm [] f::btsr3))
  end.

Definition co_wf {o} op (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)) :=
  match get_param_from_cop arg1c, arg1bts with
    | Some pk, [] =>
      match op, pk with
        | CompOpEq, _ => true
        | CompOpLess, PKi _ => true
        | CompOpLess, _ => false
      end
    | _, _ => false
  end.

Definition co_wf_def {o} op (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)) :=
  {pk : param_kind
   & get_param_from_cop arg1c = Some pk
   # arg1bts = []
   # (op = CompOpEq
      [+] {i : Z & op = CompOpLess # pk = PKi i})}.

Lemma co_wf_dec {o} :
  forall op (arg1c : @CanonicalOp o) (arg1bts : list (@BTerm o)),
    decidable (co_wf_def op arg1c arg1bts).
Proof.
  introv.
  destruct arg1c; simpl; tcsp;
    try (complete (right;unfold co_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv));
    destruct arg1bts; tcsp;
      try (complete (right;unfold co_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv));
      destruct op; tcsp;
        try (complete (right;unfold co_wf_def;intro x; exrepnd; ginv; repndors; exrepnd; ginv));
        try (complete (left; unfold co_wf_def; exists (@PKi o z); dands; tcsp));
        try (complete (left; unfold co_wf_def; exists (@PKs o s); dands; tcsp));
        try (complete (left; unfold co_wf_def; exists (@PKa o g); dands; tcsp));
        try (complete (left; unfold co_wf_def; exists (@PKc o c); dands; tcsp)).
  left; unfold co_wf_def.
  exists (@PKi o z); dands; tcsp.
  right.
  exists z; dands; auto.
Qed.

Definition co {o} btsr (t : @NTerm o) arg1bts arg1c op cstep arg1 ncr :=
  if co_wf op arg1c arg1bts
  then co_aux btsr (t : @NTerm o) arg1bts arg1c op cstep arg1 ncr
  else cfailure bad_args t.


(** ** [NSleep]
  %\noindent% [NSleep] is a feature still under development.
  [NSleep] calls on the sleep system function.

*)


Definition compute_step_sleep {p}
           (arg1c : @CanonicalOp p)
           (t : @NTerm p)
           (arg1bts btsr : list (@BTerm p)) :=
  match (arg1bts, btsr, get_param_from_cop arg1c) with
    | ([],[],Some (PKi n)) =>
      (* sleep for n milliseconds *)
      csuccess mk_axiom
    | _ => cfailure sleep_not_well_formed t
  end.



(** ** [NTUni]
  %\noindent% [NTUni] compute to regular universes.

*)


Definition compute_step_tuni {p}
           (arg1c : @CanonicalOp p)
           (t : @NTerm p)
           (arg1bts btsr : list (@BTerm p)) :=
  match (arg1bts, btsr, get_param_from_cop arg1c) with
    | ([],[],Some (PKi n)) =>
      if Z_le_gt_dec 0 n
      then csuccess (mk_uni (Z.to_nat n))
      else cfailure tuni_not_well_formed t
    | _ => cfailure tuni_not_well_formed t
  end.

(** ** [NMinus]
  %\noindent% [NMinus] is the regular minus unary operator.

*)


Definition compute_step_minus {p}
           (arg1c : @CanonicalOp p)
           (t : @NTerm p)
           (arg1bts btsr : list (@BTerm p)) :=
  match (arg1bts, btsr, get_param_from_cop arg1c) with
    | ([],[],Some (PKi n)) => csuccess (mk_integer (- n))
    | _ => cfailure minus_not_well_formed t
  end.


(*
CoInductive atom_stream {o} :=
| atom_stream_cons : get_patom_set o -> atom_stream -> atom_stream.

Record ComputationContext {o} :=
  {
    lib : @library o;
    freshAtoms : list (get_patom_set o)
  }.
*)

Definition compute_step_lib {o}
           (lib : @library o)
           (opabs : opabs)
           (bs : list (@BTerm o)) :=
  match unfold_abs lib opabs bs with
    | Some u => csuccess u
    | None => cfailure compute_step_error_abs (oterm (Abs opabs) bs)
  end.

Definition utok_sub {o} := list (get_patom_set o # @NTerm o).

Fixpoint utok_sub_find {o} (sub : @utok_sub o) (a : get_patom_set o) : option NTerm :=
  match sub with
    | nil => None
    | (x,t) :: xs =>
      if get_patom_deq o x a
      then Some t
      else utok_sub_find xs a
  end.

Definition subst_utok {o} (a : @get_patom_set o) (bs : list BTerm) (sub : utok_sub) : NTerm :=
  match utok_sub_find sub a with
    | None => oterm (Can (NUTok a)) bs
    | Some t => t
  end.

Fixpoint subst_utokens_aux {o} (t : @NTerm o) (sub : utok_sub) : NTerm :=
  match t with
    | vterm v => t
    | oterm op bs =>
      match op with
        | Can (NUTok a) => subst_utok a (map (fun b => subst_utokens_aux_b b sub) bs) sub
        | _ => oterm op (map (fun b => subst_utokens_aux_b b sub) bs)
      end
  end
with subst_utokens_aux_b {o} (b : @BTerm o) (sub : utok_sub) : BTerm :=
       match b with
         | bterm vs t =>
           bterm vs (subst_utokens_aux t sub)
       end.

Fixpoint free_vars_utok_sub {o} (sub : @utok_sub o) :=
  match sub with
    | [] => []
    | (_,t) :: s => free_vars t ++ free_vars_utok_sub s
  end.

Definition subst_utokens {p} (t : @NTerm p) (sub : utok_sub) : NTerm :=
  let sfr := free_vars_utok_sub sub in
  if dec_disjointv (bound_vars t) sfr
  then subst_utokens_aux t sub
  else subst_utokens_aux (change_bvars_alpha sfr t) sub.


Definition get_utokens_library_entry {p} (entry : @library_entry p) : list (get_patom_set p) :=
  match entry with
  | lib_cs _ e => flat_map getc_utokens (cse_vals e)
  | lib_ref _ e => getc_utokens e
  | lib_abs opabs vars rhs correct => get_utokens_so rhs
  end.

Definition get_utokens_library {p} (lib : @library p) : list (get_patom_set p) :=
  flat_map get_utokens_library_entry lib.

Definition get_utokens_ce {o} (ce : @compenv o) : list (get_patom_set o) :=
  get_utokens_library (ce_library ce)
  ++ atom_sub_range (ce_atom_sub ce).

Definition valid_atom_sub {o} (sub : @atom_sub o) (ce : @compenv o) (t : @NTerm o) :=
  disjoint (atom_sub_range sub)
           (get_utokens_library (ce_library ce) ++ get_utokens t)
  # atom_sub_dom sub = atom_sub_dom (ce_atom_sub ce).

Definition mk_ce {o} (lib : @library o) (sub : @atom_sub o) : compenv :=
  {| ce_library := lib; ce_atom_sub := sub |}.

Definition ce_change_atom_sub {o} (ce : @compenv o) (sub : @atom_sub o) : compenv :=
  mk_ce (ce_library ce) sub.

(* maps the atoms from [ce] to the atoms in [sub] *)
Definition mk_utok_sub {o} (sub : @atom_sub o) (ce : @compenv o) : @utok_sub o :=
  combine (atom_sub_range (ce_atom_sub ce))
          (map mk_utoken (atom_sub_range sub)).

(*
Lemma find_bare_atom_some_eq_doms {o} :
  forall (s1 s2 : @bare_atom_sub o) v a,
    find_bare_atom s1 v = Some a
    -> bare_atom_sub_dom s1 = bare_atom_sub_dom s2
    -> {a' : get_patom_set o & find_bare_atom s2 v = Some a'}.
Proof.
  induction s1; destruct s2; introv fa e; allsimpl; ginv.
  destruct a; destruct p; allsimpl.
  boolvar; ginv; cpx.
  - eexists; eauto.
  - eapply IHs1 in fa; eauto.
Qed.

Lemma find_atom_some_eq_doms {o} :
  forall (s1 s2 : @atom_sub o) v a,
    find_atom s1 v = Some a
    -> atom_sub_dom s1 = atom_sub_dom s2
    -> {a' : get_patom_set o & find_atom s2 v = Some a'}.
Proof.
  introv.
  destruct s1 as [s1 w1].
  destruct s2 as [s2 w2].
  unfold find_atom; simpl.
  unfold atom_sub_dom; simpl.
  apply find_bare_atom_some_eq_doms.
Qed.

Lemma find_bare_atom_some {o} :
  forall (s : @bare_atom_sub o) v a,
    find_bare_atom s v = Some a
    -> LIn (v,a) s.
Proof.
  induction s; introv e; allsimpl; tcsp.
  destruct a; boolvar; ginv; tcsp.
Qed.

Lemma find_atom_some {o} :
  forall (s : @atom_sub o) v a,
    find_atom s v = Some a
    -> in_atom_sub v a s.
Proof.
  introv fa.
  destruct s.
  unfold find_atom in fa; unfold in_atom_sub; allsimpl.
  apply find_bare_atom_some in fa; auto.
Qed.
*)

Lemma find_atom_some {o} :
  forall (s : @atom_sub o) v a,
    find_atom s v = Some a
    -> LIn (v,a) s.
Proof.
  induction s; introv e; allsimpl; tcsp.
  destruct a; boolvar; ginv; tcsp.
Qed.

(*
Lemma implies_bare_atom_sub_range {o} :
  forall (s : @bare_atom_sub o) v a,
    LIn (v,a) s -> LIn a (bare_atom_sub_range s).
Proof.
  induction s; introv i; allsimpl; tcsp.
  repndors; subst; tcsp.
  destruct a; allsimpl; tcsp.
  apply IHs in i; sp.
Qed.

Lemma implies_atom_sub_range {o} :
  forall (s : @atom_sub o) v a,
    in_atom_sub v a s -> LIn a (atom_sub_range s).
Proof.
  introv i.
  destruct s.
  unfold in_atom_sub in i; unfold atom_sub_range; allsimpl.
  apply implies_bare_atom_sub_range in i; auto.
Qed.
*)

Lemma implies_atom_sub_range {o} :
  forall (s : @atom_sub o) v a,
    LIn (v,a) s -> LIn a (atom_sub_range s).
Proof.
  induction s; introv i; allsimpl; tcsp.
  repndors; subst; tcsp.
  destruct a; allsimpl; tcsp.
  apply IHs in i; sp.
Qed.

(*
Lemma utok_sub_find_if_find_bare_atom {o} :
  forall (s1 s2 : @bare_atom_sub o) v a1 a2,
    find_bare_atom s1 v = Some a1
    -> find_bare_atom s2 v = Some a2
    -> wf_bare_atom_sub s1
    -> wf_bare_atom_sub s2
    -> bare_atom_sub_dom s1 = bare_atom_sub_dom s2
    -> utok_sub_find (combine (bare_atom_sub_range s1) (map mk_utoken (bare_atom_sub_range s2))) a1
       = Some (mk_utoken a2).
Proof.
  induction s1; destruct s2; introv fa1 fa2 w1 w2 e; allsimpl; tcsp.
  destruct a, p; allsimpl.
  allrw @wf_bare_atom_sub_cons; repnd.
  boolvar; allsimpl; cpx.
  - provefalse.
    apply find_bare_atom_some in fa1.
    apply implies_bare_atom_sub_range in fa1; sp.
  - eapply IHs1; eauto.
Qed.

Lemma utok_sub_find_if_find_atom {o} :
  forall (s1 s2 : @atom_sub o) v a1 a2,
    find_atom s1 v = Some a1
    -> find_atom s2 v = Some a2
    -> atom_sub_dom s1 = atom_sub_dom s2
    -> utok_sub_find (combine (atom_sub_range s1) (map mk_utoken (atom_sub_range s2))) a1
       = Some (mk_utoken a2).
Proof.
  introv fa1 fa2 e.
  destruct s1 as [s1 w1].
  destruct s2 as [s2 w2].
  allunfold @find_atom; allsimpl.
  allunfold @atom_sub_dom; allsimpl.
  allunfold @atom_sub_range; allsimpl.
  eapply utok_sub_find_if_find_bare_atom; eauto.
Qed.

Lemma find_atom_if_valid {o} :
  forall ce s (t : @NTerm o) v a,
    find_atom (ce_atom_sub ce) v = Some a
    -> valid_atom_sub s ce t
    -> {a' : get_patom_set o
        & find_atom s v = Some a'
        # !LIn a' (get_utokens t ++ get_utokens_library (ce_library ce))
        # (forall bs, subst_utok a bs (mk_utok_sub s ce) = mk_utoken a') }.
Proof.
  introv fa val.
  unfold valid_atom_sub in val.
  destruct ce; allsimpl; repnd.
  symmetry in val.
  dup fa as f.
  eapply @find_atom_some_eq_doms in fa;[|eauto].
  exrepnd.
  dup fa0 as f'.
  apply find_atom_some in fa0.
  apply implies_atom_sub_range in fa0.
  apply val0 in fa0.
  allrw in_app_iff; allrw not_over_or; repnd.
  exists a'; dands; auto; tcsp.
  - allrw in_app_iff; tcsp.
  - introv.
    unfold subst_utok, mk_utok_sub; simpl.
    rw (utok_sub_find_if_find_atom ce_atom_sub0 s v a a'); auto.
Qed.
*)

(* similar to get_utokens but designed to handle things like:
       [mk_fresh v (mk_apply (sterm (fun _ => mk_utoken a)) mk_zero)]
   The issue is that if we don't look inside sequences, we could
   pick the atom [a] to replace [v], and the application
       [mk_apply (sterm (fun _ => mk_utoken a)) mk_zero]
   would then reduce to [mk_utoken a], and we would then rebind the
   variable by replacing [a] by [v] and forming [mk_fresh v v].
   However, the two [a]'s are supposed to be different.

   Therefore, because a new fresh atom is picked at each step, we could
   also make sure that the one we pick is different from ones that
   become ``visible`` after a computation step.  We say that atoms in
   sequences are not ``visible`` because they cannot be substituted and
   [get_utokens] doesn't collect them.
*)

Fixpoint get_utokens_step_seq {o} (t : @NTerm o) : list (get_patom_set o) :=
  match t with
    | vterm _ => []
    | oterm op bs =>
      (get_utokens_o op)
        ++ (flat_map get_utokens_step_seq_b bs)
  end
with get_utokens_step_seq_b {o} (bt : @BTerm o) : list (get_patom_set o) :=
       match bt with
         | bterm _ t => get_utokens_step_seq t
       end.

Lemma subset_get_utokens_get_utokens_step_seq {o} :
  forall (t : @NTerm o),
    subset (get_utokens t) (get_utokens_step_seq t).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; simpl; eauto 3 with slow.
Qed.

Lemma osubset_get_utokens_step_seq_get_cutokens {o} :
  forall (t : @NTerm o),
    subseto (get_utokens_step_seq t) (get_cutokens t).
Proof.
  nterm_ind1s t as [v|op bs ind] Case;
  simpl; eauto 3 with slow.
  Case "oterm".
  allrw @subseto_app_l.
  dands.

  - eapply subseto_oeqset;[|apply oeqset_sym;apply oeqset_oappl_OLL].
    apply implies_subseto_app_r; left; apply subseto_refl.

  - eapply subseto_oeqset;[|apply oeqset_sym;apply oeqset_oappl_OLL].
    apply implies_subseto_app_r; right.
    apply subseto_flat_map2; introv i.

    destruct x as [l t]; simpl.
    eapply ind; eauto 3 with slow.
Qed.

Definition get_utokens_lib {o} lib (t : @NTerm o) :=
  get_utokens t ++ get_utokens_library lib.

Definition get_fresh_atom {o} lib (t : @NTerm o) : get_patom_set o :=
  projT1 (fresh_atom o (get_utokens_lib lib t)).

Lemma get_fresh_atom_prop {o} :
  forall lib (t : @NTerm o),
    !LIn (get_fresh_atom lib t) (get_utokens t).
Proof.
  introv i.
  unfold get_fresh_atom in i.
  match goal with
  | [ H : context[fresh_atom ?a ?b] |- _ ] =>
    destruct (fresh_atom a b); allsimpl; tcsp
  end.
  allrw in_app_iff; allrw not_over_or; tcsp.
Qed.

Lemma get_fresh_atom_prop_lib {o} :
  forall lib (t : @NTerm o),
    !LIn (get_fresh_atom lib t) (get_utokens_library lib).
Proof.
  introv i.
  unfold get_fresh_atom in i.
  match goal with
  | [ H : context[fresh_atom ?a ?b] |- _ ] =>
    destruct (fresh_atom a b); allsimpl; tcsp
  end.
  allrw in_app_iff; allrw not_over_or; tcsp.
Qed.

Lemma get_fresh_atom_prop2 {o} :
  forall lib (t : @NTerm o),
    !LIn (get_fresh_atom lib t) (get_utokens t).
Proof.
  introv i.
(*  apply subset_get_utokens_get_utokens_step_seq in i.*)
  apply get_fresh_atom_prop in i; auto.
Qed.

Lemma eq_fresh_atom {o} :
  forall lib (t1 t2 : @NTerm o),
    get_utokens t1 = get_utokens t2
    -> get_fresh_atom lib t1 = get_fresh_atom lib t2.
Proof.
  introv e.
  unfold get_fresh_atom, get_utokens_lib.
  rw e; auto.
Qed.

(*
Lemma implies_ce_is_fresh_atom {o} :
  forall (ce : @compenv o) (t : @NTerm o) a,
    !LIn a (get_utoks_norep ce t)
    -> ce_is_fresh_atom ce a.
Proof.
  introv ni.
  unfold ce_is_fresh_atom, is_fresh_atom.
  unfold get_utoks_norep in ni.
  unfold get_utokens_ce in ni.
  allrw in_remove_repeats.
  allrw in_app_iff; allrw not_over_or; repnd; auto.
Qed.

Definition ce_add_fresh_atom {o}
           (ce : @compenv o)
           (v : NVar)
           (a : get_patom_set o)
           (t : @NTerm o)
           (p : !LIn a (get_utoks_norep ce t)) : compenv :=
  ce_add_atom ce v a (implies_ce_is_fresh_atom ce t a p).
*)

Definition maybe_new_var {o} (v : NVar) (vs : list NVar) (t : @NTerm o) :=
  if memvar v vs then newvar t else v.

(* We could do better by not generating a [mk_fresh] term when [v] is in [vs]
  but that messes up [implies_alpha_eq_pushdown_fresh] *)
Definition mk_fresh_bterm {o} (v : NVar) (b : @BTerm o) :=
  match b with
    | bterm vs t => bterm vs (mk_fresh (maybe_new_var v vs t) t)
  end.

Definition mk_fresh_bterms {o} (v : NVar) (bs : list (@BTerm o)) :=
  map (mk_fresh_bterm v) bs.

Definition pushdown_fresh {o} (v : NVar) (t : @NTerm o) :=
  match t with
    | vterm x => mk_fresh v t
    | oterm op bs => oterm op (mk_fresh_bterms v bs)
  end.

Definition compute_step_fresh {o}
           (lib : @library o)
           (ncan : NonCanonicalOp)
           (t : @NTerm o)
           (v : NVar)
           (vs : list NVar)
           (u : NTerm)
           (bs : list (@BTerm o))
           (comp : Comput_Result)
           (a : get_patom_set o) :=
  match ncan, vs, bs with
    | NFresh,[],[] =>
      match u with
        | vterm x =>
          if deq_nvar v x
          then csuccess t
          else cfailure compute_step_error_not_closed t
        | oterm (Can _) _ => csuccess (pushdown_fresh v u)
        | oterm Exc _ => csuccess (pushdown_fresh v u)
        | oterm (Abs  _) _ => on_success comp (fun r => mk_fresh v (subst_utokens r [(a,mk_var v)]))
        | oterm (NCan _) _ => on_success comp (fun r => mk_fresh v (subst_utokens r [(a,mk_var v)]))
      end
    | _,_,_ => cfailure "check 1st arg" t
  end.

(* begin hide *)


Definition not_int_cop {p} (c: @CanonicalOp p) :=
 match c with
 | Nint _ => false
 | _ => true
 end.

Lemma compute_comp_test_testcase1 {p} :
  compute_step_comp  CompOpLess (Nint (Z.of_nat 1)) (Nint (Z.of_nat 2))
 [] [] [bterm [] (vterm nvarx) , bterm [] (vterm nvary)] (vterm nvarx)=
   csuccess (@vterm p nvarx).
Proof. reflexivity. Qed.

Lemma compute_comp_test_testcase2 {p} :
  compute_step_comp  CompOpLess (Nint (Z.of_nat 3)) (Nint (Z.of_nat 2))
 [] [] [bterm [] (vterm nvarx) , bterm [] (vterm nvary)] (vterm nvarx)=
   csuccess (@vterm p nvary).
Proof. reflexivity. Qed.

Definition compute_step_canonical_form_test {p}
           (test : CanonicalTest)
           (cop  : @CanonicalOp p)
           (b c : @NTerm p) : NTerm :=
if canonical_form_test_for test cop
then b
else c.

Definition compute_step_parallel {o}
           (arg1c   : @CanonicalOp o)
           (t       : @NTerm o)
           (arg1bts : list (@BTerm o))
           (btsr    : list (@BTerm o)) : @Comput_Result o :=
  csuccess mk_axiom.
(* This is a stub for what should really come here.

   I'll make the parallel return its principal argument if its canonical
   otherwise it will make step of computation on its principal argument
   and then rotate its subterms.

   This means, I'll have to change the way computation on non-canonical
   terms and abstractions work :(
 *)
