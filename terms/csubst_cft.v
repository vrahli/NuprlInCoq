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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export csubst.

Lemma cover_vars_can_test {o} :
  forall test (a b c : @NTerm o) sub,
    cover_vars (mk_can_test test a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_isinl {o} :
  forall (a b c : @NTerm o) sub,
    cover_vars (mk_isinl a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  introv; rw @cover_vars_can_test; sp.
Qed.

Lemma cover_vars_isinr {o} :
  forall (a b c : @NTerm o) sub,
    cover_vars (mk_isinr a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  introv; rw @cover_vars_can_test; sp.
Qed.

Lemma cover_vars_isaxiom {o} :
  forall (a b c : @NTerm o) sub,
    cover_vars (mk_isaxiom a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  introv; rw @cover_vars_can_test; sp.
Qed.

Lemma cover_vars_islambda {o} :
  forall (a b c : @NTerm o) sub,
    cover_vars (mk_islambda a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  introv; rw @cover_vars_can_test; sp.
Qed.

Lemma lsubstc_mk_isinl_ex {o} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_isinl o t1 t2 t3),
  forall c  : cover_vars (mk_isinl t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_isinl t1 t2 t3) w sub c
           = mkc_isinl (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  introv.
  dup w as w'.
  apply @wf_isinl_iff in w'; repnd.
  dup c as c'.
  apply @cover_vars_isinl in c'; repnd.
  pose proof (lsubstc_mk_can_test CanIsinl t1 t2 t3 sub w'0 w'1 w' w c'0 c'1 c' c) as h.
  inversion h as [e]; clear h; allsimpl.
  exists w'0 w'1 w' c'0 c'1 c'.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_isinr_ex {o} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_isinr o t1 t2 t3),
  forall c  : cover_vars (mk_isinr t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_isinr t1 t2 t3) w sub c
           = mkc_isinr (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  introv.
  dup w as w'.
  apply @wf_isinr_iff in w'; repnd.
  dup c as c'.
  apply @cover_vars_isinr in c'; repnd.
  pose proof (lsubstc_mk_can_test CanIsinr t1 t2 t3 sub w'0 w'1 w' w c'0 c'1 c' c) as h.
  inversion h as [e]; clear h; allsimpl.
  exists w'0 w'1 w' c'0 c'1 c'.
  apply cterm_eq; simpl; auto.
Qed.


(* There is another Lemma lsubstc_mk_isaxiom_ex  in subst_per.v
   but it isn't the one we need for lsubst_tac  ??  *)
Lemma lsubstc_mk_isaxiom_ex2 {o} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_isaxiom o t1 t2 t3),
  forall c  : cover_vars (mk_isaxiom t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_isaxiom t1 t2 t3) w sub c
           = mkc_isaxiom (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  introv.
  dup w as w'.
  apply @wf_isaxiom in w'; repnd.
  dup c as c'.
  apply @cover_vars_isaxiom in c'; repnd.
  pose proof (lsubstc_mk_can_test CanIsaxiom t1 t2 t3 sub w'0 w'1 w' w c'0 c'1 c' c) as h.
  inversion h as [e]; clear h; allsimpl.
  exists w'0 w'1 w' c'0 c'1 c'.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_islambda_ex {o} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_islambda o t1 t2 t3),
  forall c  : cover_vars (mk_islambda t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_islambda t1 t2 t3) w sub c
           = mkc_islambda (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  introv.
  dup w as w'.
  rw <- @wf_islambda_iff in w'; repnd.
  dup c as c'.
  apply @cover_vars_islambda in c'; repnd.
  pose proof (lsubstc_mk_can_test CanIslambda t1 t2 t3 sub w'0 w'1 w' w c'0 c'1 c' c) as h.
  inversion h as [e]; clear h; allsimpl.
  exists w'0 w'1 w' c'0 c'1 c'.
  apply cterm_eq; simpl; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)

