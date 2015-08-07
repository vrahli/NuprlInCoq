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


Require Export sequents_atom.



Ltac foldseq_one_step :=
  match goal with
    | [ |- context[{| hyps := ?hs; concl := ?c|}] ] =>
      fold (mk_baresequent hs c)

    | [ |- context[concl_ext ?t ?e] ] =>
      fold (mk_concl t e)

    | [ |- context[mk_concl ?t mk_axiom] ] =>
      fold (mk_conclax t)

    | [ H : context[{| hyps := ?hs; concl := ?c|}] |- _ ] =>
      fold (mk_baresequent hs c) in H

    | [ H : context[concl_ext ?t ?e] |- _ ] =>
      fold (mk_concl t e) in H

    | [ H : context[mk_concl ?t mk_axiom] |- _ ] =>
      fold (mk_conclax t) in H
  end.

Ltac foldseq := repeat foldseq_one_step.

Definition folded_dset_member {p} (x : get_patom_set p) l := dset_member x l.

Lemma folded_dset_member_fold {p} :
  forall (x : get_patom_set p) l,
    dset_member x l = folded_dset_member x l.
Proof. sp. Qed.

Ltac fold_dset_member_step :=
  match goal with
    | [ H : dset_member ?x ?l |- _ ] => fold (folded_dset_member x l) in H
  end.

Ltac gen_s2s_step :=
  match goal with
    | [ x : get_patom_set (s2s _) |- ?C ] =>
      match C with
        | context[existT _ x ?y] =>
          match type of y with
            | folded_dset_member _ _ => fail 1
            | _ =>
              remember y;
                clears_last;
                repeat fold_dset_member_step
          end
      end
  end.

Ltac gen_s2s := repeat gen_s2s_step; allunfold @folded_dset_member.


Definition eq_utok_ren_cseq_ctseq {p d}
           (s : ctsequent)
           (q : closed_extract_ctsequent s)
           (f : @utok_ren_ctseq p d s)
           (r : @utok_ren_cseq p d (exI(s,q))) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_ctseq s)),
    f(exI(x,m)) = r(exI(x,m)).

Lemma utok_ren_cseq_2ctseq_prop {p d} :
  forall (s : ctsequent)
         (q : closed_extract_ctsequent s)
         (r : @utok_ren_cseq p d (exI(s,q))),
    eq_utok_ren_cseq_ctseq s q (utok_ren_cseq_2ctseq s q r) r.
Proof. unfold eq_utok_ren_cseq_ctseq; auto. Qed.

Lemma utok_ren_ctseq_2seq_prop {p d} :
  forall (s : sequent)
         (q : closed_type_sequent s)
         (r : @utok_ren_ctseq p d (exI(s,q)))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_seq s)),
    utok_ren_ctseq_2seq s q r (exI(x,m)) = r(exI(x,m)).
Proof. auto. Qed.

Definition eq_utok_ren_ctseq_seq {p d}
           (s : sequent)
           (q : closed_type_sequent s)
           (f : @utok_ren_seq p d s)
           (r : @utok_ren_ctseq p d (exI(s,q))) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_seq s)),
    f(exI(x,m)) = r(exI(x,m)).

Lemma utok_ren_seq_2bseq_prop {p d} :
  forall (s : baresequent)
         (w : wf_sequent s)
         (r : @utok_ren_seq p d (exI(s,w)))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_bseq s)),
    utok_ren_seq_2bseq s w r (exI(x,m)) = r(exI(x,m)).
Proof. auto. Qed.

Definition eq_utok_ren_seq_bseq {p d}
           (s : baresequent)
           (w : wf_sequent s)
           (f : @utok_ren_bseq p d s)
           (r : @utok_ren_seq p d (exI(s,w))) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_bseq s)),
    f(exI(x,m)) = r(exI(x,m)).

Lemma utok_ren_bseq_2h_prop {p d} :
  forall (s : baresequent)
         (r : @utok_ren_bseq p d s)
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_bhyps (hyps s))),
    utok_ren_bseq_2h s r (exI(x,m)) = r(exI(x,in_utok_bseq_if_bhyps x s m)).
Proof. auto. Qed.

Definition eq_utok_ren_bseq_bhyps {p d}
           (s : baresequent)
           (f : @utok_ren_bhyps p d (hyps s))
           (r : @utok_ren_bseq p d s) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_bhyps (hyps s))),
    f(exI(x,m)) = r(exI(x,in_utok_bseq_if_bhyps x s m)).

Lemma utok_ren_bseq_2c_prop {p d} :
  forall (s : baresequent)
         (r : @utok_ren_bseq p d s)
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_concl (concl s))),
    utok_ren_bseq_2c s r (exI(x,m)) = r(exI(x,in_utok_bseq_if_concl x s m)).
Proof. auto. Qed.

Definition eq_utok_ren_bseq_concl {p d}
           (s : baresequent)
           (f : @utok_ren_concl p d (concl s))
           (r : @utok_ren_bseq p d s) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_concl (concl s))),
    f(exI(x,m)) = r(exI(x,in_utok_bseq_if_concl x s m)).

Lemma utok_ren_concle_2t_prop {p d} :
  forall (t e : NTerm)
         (r : @utok_ren_concl p d (concl_ext t e))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens t)),
    utok_ren_concle_2t t e r (exI(x,m)) = r(exI(x,in_utok_concl_ext_if_ctype x t e m)).
Proof. auto. Qed.

Definition eq_utok_ren_concle_t {p d}
           (t e : NTerm)
           (f : @utok_ren p d t)
           (r : @utok_ren_concl p d (concl_ext t e)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens t)),
    f(exI(x,m)) = r(exI(x,in_utok_concl_ext_if_ctype x t e m)).

Lemma utok_ren_concle_2e_prop {p d} :
  forall (t e : NTerm)
         (r : @utok_ren_concl p d (concl_ext t e))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens e)),
    utok_ren_concle_2e t e r (exI(x,m)) = r(exI(x,in_utok_concl_ext_if_extract x t e m)).
Proof. auto. Qed.

Definition eq_utok_ren_concle_e {p d}
           (t e : NTerm)
           (f : @utok_ren p d e)
           (r : @utok_ren_concl p d (concl_ext t e)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens e)),
    f(exI(x,m)) = r(exI(x,in_utok_concl_ext_if_extract x t e m)).

Lemma utok_ren_2bs_prop {p d} :
  forall (o : Opid)
         (bs : list BTerm)
         (r : @utok_ren p d (oterm o bs))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_bs bs)),
    utok_ren_2bs o bs r (exI(x,m)) = r(exI(x,in_utok_if_bts x o bs m)).
Proof. auto. Qed.

Definition eq_utok_ren_t_bs {p d}
           (o : Opid)
           (bs : list BTerm)
           (f : @utok_ren_bs p d bs)
           (r : @utok_ren p d (oterm o bs)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_bs bs)),
    f(exI(x,m)) = r(exI(x,in_utok_if_bts x o bs m)).

Lemma utok_ren_bs_2bs_prop {p d} :
  forall (b : BTerm)
         (bs : list BTerm)
         (r : @utok_ren_bs p d (b :: bs))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_bs bs)),
    utok_ren_bs_2bs b bs r (exI(x,m)) = r(exI(x,in_utok_bs_if_bs x b bs m)).
Proof. auto. Qed.

Definition eq_utok_ren_bs_bs {p d}
           (b : BTerm)
           (bs : list BTerm)
           (f : @utok_ren_bs p d bs)
           (r : @utok_ren_bs p d (b :: bs)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_bs bs)),
    f(exI(x,m)) = r(exI(x,in_utok_bs_if_bs x b bs m)).

Lemma utok_ren_bs_2b_prop {p d} :
  forall (b : BTerm)
         (bs : list BTerm)
         (r : @utok_ren_bs p d (b :: bs))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_b b)),
    utok_ren_bs_2b b bs r (exI(x,m)) = r(exI(x,in_utok_bs_if_b x b bs m)).
Proof. auto. Qed.

Definition eq_utok_ren_bs_b {p d}
           (b : BTerm)
           (bs : list BTerm)
           (f : @utok_ren_b p d b)
           (r : @utok_ren_bs p d (b :: bs)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_b b)),
    f(exI(x,m)) = r(exI(x,in_utok_bs_if_b x b bs m)).

Lemma utok_ren_b_2t_prop {p d} :
  forall (vs : list NVar)
         (t : NTerm)
         (r : @utok_ren_b p d (bterm vs t))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens t)),
    utok_ren_b_2t vs t r (exI(x,m)) = r(exI(x,in_utok_b_if_t x vs t m)).
Proof. auto. Qed.

Definition eq_utok_ren_b_t {p d}
           (vs : list NVar)
           (t : NTerm)
           (f : @utok_ren p d t)
           (r : @utok_ren_b p d (bterm vs t)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens t)),
    f(exI(x,m)) = r(exI(x,in_utok_b_if_t x vs t m)).

Lemma utok_ren_2o_prop {p d} :
  forall (o : Opid)
         (bs : list BTerm)
         (r : @utok_ren p d (oterm o bs))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_o o)),
    utok_ren_2o o bs r (exI(x,m)) = r(exI(x,in_utok_if_o x o bs m)).
Proof. auto. Qed.

Definition eq_utok_ren_t_o {p d}
           (o : Opid)
           (bs : list BTerm)
           (f : @utok_ren_o p d o)
           (r : @utok_ren p d (oterm o bs)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_o o)),
    f(exI(x,m)) = r(exI(x,in_utok_if_o x o bs m)).

Lemma utok_ren_o2c_prop {p d} :
  forall (c : CanonicalOp)
         (r : @utok_ren_o p d (Can c))
         (x : get_patom_set p)
         (m : dset_member x (get_utokens_c c)),
    utok_ren_o2c c r (exI(x,m)) = r(exI(x,m)).
Proof. auto. Qed.

Definition eq_utok_ren_o_c {p d}
           (c : CanonicalOp)
           (f : @utok_ren_c p d c)
           (r : @utok_ren_o p d (Can c)) :=
  forall (x : get_patom_set p)
         (m : dset_member x (get_utokens_c c)),
    f(exI(x,m)) = r(exI(x,m)).

Ltac gen_utok_ren :=
  let h := fresh "h" in
  let f := fresh "f" in
  match goal with
    (* cseq 2 ctesq *)

    | [ H : context[utok_ren_cseq_2ctseq ?s ?q ?r] |- _ ] =>
      pose proof (utok_ren_cseq_2ctseq_prop s q r) as h;
        remember (utok_ren_cseq_2ctseq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_cseq_ctseq s q f r) in h

    | [ |- context[utok_ren_cseq_2ctseq ?s ?q ?r] ] =>
      pose proof (utok_ren_cseq_2ctseq_prop s q r) as h;
        remember (utok_ren_cseq_2ctseq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_cseq_ctseq s q f r) in h

    (* ctseq 2 seq *)

    | [ H : context[utok_ren_ctseq_2seq ?s ?q ?r] |- _ ] =>
      pose proof (utok_ren_ctseq_2seq_prop s q r) as h;
        remember (utok_ren_ctseq_2seq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_ctseq_seq s q f r) in h

    | [ |- context[utok_ren_ctseq_2seq ?s ?q ?r] ] =>
      pose proof (utok_ren_ctseq_2seq_prop s q r) as h;
        remember (utok_ren_ctseq_2seq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_ctseq_seq s q f r) in h

    (* seq 2 bseq *)

    | [ H : context[utok_ren_seq_2bseq ?s ?q ?r] |- _ ] =>
      pose proof (utok_ren_seq_2bseq_prop s q r) as h;
        remember (utok_ren_seq_2bseq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_seq_bseq s q f r) in h

    | [ |- context[utok_ren_seq_2bseq ?s ?q ?r] ] =>
      pose proof (utok_ren_seq_2bseq_prop s q r) as h;
        remember (utok_ren_seq_2bseq s q r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_seq_bseq s q f r) in h

    (* bseq 2 hyps *)

    | [ H : context[utok_ren_bseq_2h ?s ?r] |- _ ] =>
      pose proof (utok_ren_bseq_2h_prop s r) as h;
        remember (utok_ren_bseq_2h s r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bseq_bhyps s f r) in h

    | [ |- context[utok_ren_bseq_2h ?s ?r] ] =>
      pose proof (utok_ren_bseq_2h_prop s r) as h;
        remember (utok_ren_bseq_2h s r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bseq_bhyps s f r) in h

    (* bseq 2 concl *)

    | [ H : context[utok_ren_bseq_2c ?s ?r] |- _ ] =>
      pose proof (utok_ren_bseq_2c_prop s r) as h;
        remember (utok_ren_bseq_2c s r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bseq_concl s f r) in h

    | [ |- context[utok_ren_bseq_2c ?s ?r] ] =>
      pose proof (utok_ren_bseq_2c_prop s r) as h;
        remember (utok_ren_bseq_2c s r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bseq_concl s f r) in h

    (* concle 2 ctype *)

    | [ H : context[utok_ren_concle_2t ?t ?e ?r] |- _ ] =>
      pose proof (utok_ren_concle_2t_prop t e r) as h;
        remember (utok_ren_concle_2t t e r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_concle_t t e f r) in h

    | [ |- context[utok_ren_concle_2t ?t ?e ?r] ] =>
      pose proof (utok_ren_concle_2t_prop t e r) as h;
        remember (utok_ren_concle_2t t e r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_concle_t t e f r) in h

    (* concle 2 extract *)

    | [ H : context[utok_ren_concle_2e ?t ?e ?r] |- _ ] =>
      pose proof (utok_ren_concle_2e_prop t e r) as h;
        remember (utok_ren_concle_2e t e r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_concle_e t e f r) in h

    | [ |- context[utok_ren_concle_2e ?t ?e ?r] ] =>
      pose proof (utok_ren_concle_2e_prop t e r) as h;
        remember (utok_ren_concle_2e t e r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_concle_e t e f r) in h

    (* term 2 bterms *)

    | [ H : context[utok_ren_2bs ?o ?bs ?r] |- _ ] =>
      pose proof (utok_ren_2bs_prop o bs r) as h;
        remember (utok_ren_2bs o bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_t_bs o bs f r) in h

    | [ |- context[utok_ren_2bs ?o ?bs ?r] ] =>
      pose proof (utok_ren_2bs_prop o bs r) as h;
        remember (utok_ren_2bs o bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_t_bs o bs f r) in h

    (* bterms 2 bterms *)

    | [ H : context[utok_ren_bs_2bs ?b ?bs ?r] |- _ ] =>
      pose proof (utok_ren_bs_2bs_prop b bs r) as h;
        remember (utok_ren_bs_2bs b bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bs_bs b bs f r) in h

    | [ |- context[utok_ren_bs_2bs ?b ?bs ?r] ] =>
      pose proof (utok_ren_bs_2bs_prop b bs r) as h;
        remember (utok_ren_bs_2bs b bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bs_bs b bs f r) in h

    (* bterms 2 bterm *)

    | [ H : context[utok_ren_bs_2b ?b ?bs ?r] |- _ ] =>
      pose proof (utok_ren_bs_2b_prop b bs r) as h;
        remember (utok_ren_bs_2b b bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bs_b b bs f r) in h

    | [ |- context[utok_ren_bs_2b ?b ?bs ?r] ] =>
      pose proof (utok_ren_bs_2b_prop b bs r) as h;
        remember (utok_ren_bs_2b b bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_bs_b b bs f r) in h

    (* bterm 2 term *)

    | [ H : context[utok_ren_b_2t ?vs ?t ?r] |- _ ] =>
      pose proof (utok_ren_b_2t_prop vs t r) as h;
        remember (utok_ren_b_2t vs t r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_b_t vs t f r) in h

    | [ |- context[utok_ren_b_2t ?vs ?t ?r] ] =>
      pose proof (utok_ren_b_2t_prop vs t r) as h;
        remember (utok_ren_b_2t vs t r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_b_t vs t f r) in h

    (* term 2 opid *)

    | [ H : context[utok_ren_2o ?o ?bs ?r] |- _ ] =>
      pose proof (utok_ren_2o_prop o bs r) as h;
        remember (utok_ren_2o o bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_t_o o bs f r) in h

    | [ |- context[utok_ren_2o ?o ?bs ?r] ] =>
      pose proof (utok_ren_2o_prop o bs r) as h;
        remember (utok_ren_2o o bs r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_t_o o bs f r) in h

    (* opid 2 canonicalop *)

    | [ H : context[utok_ren_o2c ?c ?r] |- _ ] =>
      pose proof (utok_ren_o2c_prop c r) as h;
        remember (utok_ren_o2c c r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_o_c c f r) in h

    | [ |- context[utok_ren_o2c ?c ?r] ] =>
      pose proof (utok_ren_o2c_prop c r) as h;
        remember (utok_ren_o2c c r) as f;
        clear_eq_l f;
        fold (eq_utok_ren_o_c c f r) in h
  end.

Ltac foldall :=
  match goal with
    | [ |- context[@bterm ?o [] ?t] ] => fold (@nobnd o t)
    | [ |- context[@oterm ?o (Can NAxiom) nil] ] => fold (@mk_axiom o)
    | [ |- context[@oterm ?o (Can NUAtom) nil] ] => fold (@mk_uatom o)
    | [ |- context[@oterm ?o (Can (NUTok ?t)) nil] ] => fold (@mk_utoken o t)
    | [ |- context[@oterm ?o (Can NEquality) (nobnd ?a :: nobnd ?b :: nobnd ?c :: nil)] ] => fold (@mk_equality o a b c)

    | [ H : context[@bterm ?o [] ?t] |- _ ] => fold (@nobnd o t) in H
    | [ H : context[@oterm ?o (Can NAxiom) nil] |- _ ] => fold (@mk_axiom o) in H
    | [ H : context[@oterm ?o (Can NUAtom) nil] |- _ ] => fold (@mk_uatom o) in H
    | [ H : context[@oterm ?o (Can (NUTok ?t)) nil] |- _ ] => fold (@mk_utoken o t) in H
    | [ H : context[@oterm ?o (Can NEquality) (nobnd ?a :: nobnd ?b :: nobnd ?c :: nil)] |- _ ] => fold (@mk_equality o a b c) in H
  end.
