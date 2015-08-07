(*

  Copyright 2014 Cornell University

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


Require Export sequents_tacs.
Require Export Classical_Prop.
Require Export per_props_equality.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(* begin hide *)


(* end hide*)

(* consistent spread sequence:
     - R is the spread
     - s a sequence
     - T its type
 *)
Definition mk_cons_spread_seq {o} (R : @NTerm o) s T x :=
  mk_all T
         x
         (mk_apply3 R (mk_var x) (mk_var s) (mk_apply (mk_var s) (mk_var x))).

Definition mk_spread_seq_ext {o} s n t m :=
  @mk_lam o m (mk_int_eq (mk_var m) n t (mk_apply s (mk_var m))).


(**

  Bar induction, where
    T is a type
    R is the spread law
    B is the bar
    con stands for consistent with the spread law
    ext(s,n,t) = \m. if m=n then t else s m
<<
   H |- f 0 c in X 0 c

     By strong_bar_induction T R B i a s con x m n t

     H |- T in Type(i)
     H, n:nat, s: nat_n -> T, t: T |- R n s t in Type(i)                                      // R is a well-formed spread law
     H, n:nat, s: nat_n -> T, con: (forall x: nat_n. R x s (s x)) |- (B n s) \/ not(B n s)    // B is decidable on consistent sequences in the spread
     H, a: nat -> T, con: (forall x: nat, R x a (a x)) |- squash(exists n:nat. B n a)         // B is a bar
     H, n:nat, s: nat_n -> T, con: (forall x: nat_n. R x s (s x)), m: B n s |- f n s in X n s // Base case: the conclusion is true at the bar
     H, n:nat, s: nat_n -> T, con: (forall x: nat_n. R x s (s x)),
        x: (forall t: {t:T | R n s t}.
              (f (n + 1) (ext(s,n,t))) in X (n + 1) (ext(s,n,t)))
        |- f n s in X n s
        // induction case
>>

*)

Definition rule_strong_bar_induction {o}
           (f X c T R B d : @NTerm o)
           (n s t con x a m : NVar)
           (i : nat)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_member (mk_apply2 f mk_zero c)
                                      (mk_apply2 X mk_zero c))))
    [ mk_bseq H (mk_conclax (mk_member T (mk_uni i))),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_fun (mk_nat_sub (mk_var n)) T)))
                    (mk_hyp t T))
              (mk_conclax (mk_member (mk_apply3 R (mk_var n) (mk_var s) (mk_var t))
                                     (mk_uni i))),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_fun (mk_nat_sub (mk_var n)) T)))
                    (mk_hyp con (mk_cons_spread_seq R s (mk_nat_sub (mk_var n)) x)))
              (mk_concl (mk_dec (mk_apply2 B (mk_var n) (mk_var s))) d),
      mk_bseq (snoc (snoc H (mk_hyp a (mk_fun mk_tnat T)))
                    (mk_hyp con (mk_cons_spread_seq R s mk_tnat x)))
              (mk_conclax (mk_squash
                             (mk_exists mk_tnat
                                        n
                                        (mk_apply2 B (mk_var n) (mk_var a))))),
      mk_bseq (snoc (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                                (mk_hyp s (mk_fun (mk_nat_sub (mk_var n)) T)))
                          (mk_hyp t T))
                    (mk_hyp m (mk_apply2 B (mk_var n) (mk_var s))))
              (mk_conclax (mk_member (mk_apply2 f (mk_var n) (mk_var s))
                                     (mk_apply2 X (mk_var n) (mk_var s)))),
      mk_bseq (snoc (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                                (mk_hyp s (mk_fun (mk_nat_sub (mk_var n)) T)))
                          (mk_hyp t T))
                    (mk_hyp x (mk_all (mk_set T t (mk_apply3 R (mk_var n) (mk_var s) (mk_var t)))
                                      t
                                      (mk_member (mk_apply2 f (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m))
                                                 (mk_apply2 X (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m))))))
              (mk_conclax (mk_member (mk_apply2 f (mk_var n) (mk_var s))
                                     (mk_apply2 X (mk_var n) (mk_var s))))
    ]
    [].

Lemma rule_strong_bar_induction_true {o} :
  forall lib (f X c T R B d : NTerm)
         (n s t con x a m : NVar)
         (i : nat)
         (H : @barehypotheses o),
    rule_true lib (rule_strong_bar_induction f X c T R B d n s t con x a m i H).
Proof.
  unfold rule_strong_bar_induction, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destruct Hyp2 as [wf4 hyp4].
  destruct Hyp3 as [wf5 hyp5].
  destruct Hyp4 as [wf6 hyp6].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.

(*
  generalize (teq_and_member_if_member
                (mk_apply2 X mk_zero c) (mk_apply2 f mk_zero c) s1 s2 H
                wT wt ct5 ct6 cT cT0 eqh sim); intro k.
  autodimp k hyp.

  admit.

  autodimp k hyp.

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
*)

(*
  assert (forall (n1 n2 s1 s2 con1 con2 : CTerm),
            equal n1 n2 mk_tnat
            -> equal s1 s2 (mk_fun (mk_nat_sub (mk_var n)) T)
            -> equal con1 con2 (mk_cons_spread_seq R s mk_tnat x)
            -> !(tequality
                   (mkc_member
                      (mkc_apply2 (lsubstc f w1 s1 c1) mkc_zero (lsubstc c w3 s1 c3))
                      (mkc_apply2 (lsubstc X w0 s1 c0) mkc_zero (lsubstc c w3 s1 c3)))
                   (mkc_member
                      (mkc_apply2 (lsubstc f w1 s2 c4) mkc_zero (lsubstc c w3 s2 c6))
                      (mkc_apply2 (lsubstc X w0 s2 c7) mkc_zero (lsubstc c w3 s2 c6)))
                # member (mkc_apply2 (lsubstc f w1 s1 c1) mkc_zero (lsubstc c w3 s1 c3))
                        (mkc_apply2 (lsubstc X w0 s1 c0) mkc_zero (lsubstc c w3 s1 c3)))
            -> {t : CTerm
                , !(tequality
                      (mkc_member
                         (mk_apply2 f (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m))
                         (mk_apply2 X (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m)))
                      (mk_member
                         (mk_apply2 f (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m))
                         (mk_apply2 X (mk_plus1 (mk_var n)) (mk_spread_seq_ext (mk_var s) (mk_var n) (mk_var t) m)))
                   # member (mkc_apply2 (lsubstc f w1 s1 c1) mkc_zero (lsubstc c w3 s1 c3))
                              (mkc_apply2 (lsubstc X w0 s1 c0) mkc_zero (lsubstc c w3 s1 c3)))})

  lsubst_tac; auto.
*)

Abort.