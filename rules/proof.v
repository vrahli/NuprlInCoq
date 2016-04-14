(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export rules_isect.
Require Export rules_squiggle.
Require Export rules_squiggle2.
Require Export rules_squiggle3.
Require Export rules_squiggle5.
Require Export rules_squiggle6.
Require Export rules_false.
Require Export rules_struct.


Inductive valid_rule {o} : @rule o -> Type :=
| valid_rule_isect_equality :
    forall a1 a2 b1 b2 x1 x2 y i H,
      !LIn y (vars_hyps H)
      -> valid_rule (rule_isect_equality a1 a2 b1 b2 x1 x2 y i H).

Inductive gen_proof {o} (G : @baresequent o) : Type :=
| gen_proof_cons :
    forall hyps args,
      valid_rule (mk_rule G hyps args)
      -> (forall h, LIn h hyps -> gen_proof h)
      -> gen_proof G.

(* [pwf_sequent] says that the hypotheses and conclusion are well-formed and
   the type is closed w.r.t. the hypotheses.
 *)
Lemma valid_gen_proof {o} :
  forall lib (seq : @baresequent o) (wf : pwf_sequent seq),
    gen_proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p as [? ? ? vr imp ih].
  inversion vr as [a1 a2 b1 b2 x1 x2 y i hs niy]; subst; allsimpl; clear vr.

  - apply (rule_isect_equality_true2 lib y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.
Qed.

Definition NVin v (vs : list NVar) := memvar v vs = false.

Definition Vin v (vs : list NVar) := memvar v vs = true.

Lemma NVin_iff :
  forall v vs, NVin v vs <=> !LIn v vs.
Proof.
  introv.
  unfold NVin.
  rw <- (@assert_memberb NVar eq_var_dec).
  rw <- not_of_assert; sp.
Qed.

Lemma Vin_iff :
  forall v vs, Vin v vs <=> LIn v vs.
Proof.
  introv.
  unfold Vin.
  rw <- (@assert_memberb NVar eq_var_dec); auto.
Qed.

Inductive Llist {A} (f : A -> Type) : list A -> Type :=
| lnil : Llist f []
| lcons : forall {h t}, (f h) -> Llist f t -> Llist f (h :: t).

Lemma in_Llist {A} :
  forall f (a : A) l,
    LIn a l -> Llist f l -> f a.
Proof.
  induction l; introv i h; allsimpl; tcsp.
  repndors; subst; auto.
  - inversion h; subst; auto.
  - apply IHl; auto.
    inversion h; subst; auto.
Qed.

Lemma Llist_implies_forall {A f} {l : list A} :
  Llist f l -> (forall v, LIn v l -> f v).
Proof.
  introv h i.
  eapply in_Llist in h;eauto.
Qed.

(* incomplete proof---bool is true if holes *)
Inductive iproof {o} (hole : bool) : @baresequent o -> Type :=
| iproof_hole : forall s, hole = true -> iproof hole s
| iproof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> iproof hole (rule_isect_equality_hyp1 a1 a2 i H)
      -> iproof hole (rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> iproof hole (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| iproof_approx_refl :
    forall a H,
      iproof hole (rule_approx_refl_concl a H)
| iproof_cequiv_approx :
    forall a b H,
      iproof hole (rule_cequiv_approx_hyp a b H)
      -> iproof hole (rule_cequiv_approx_hyp b a H)
      -> iproof hole (rule_cequiv_approx_concl a b H)
| iproof_approx_eq :
    forall a1 a2 b1 b2 i H,
      iproof hole (rule_eq_base_hyp a1 a2 H)
      -> iproof hole (rule_eq_base_hyp b1 b2 H)
      -> iproof hole (rule_approx_eq_concl a1 a2 b1 b2 i H)
| iproof_cequiv_eq :
    forall a1 a2 b1 b2 i H,
      iproof hole (rule_eq_base_hyp a1 a2 H)
      -> iproof hole (rule_eq_base_hyp b1 b2 H)
      -> iproof hole (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
| iproof_bottom_diverges :
    forall x H J,
      iproof hole (rule_bottom_diverges_concl x H J)
| iproof_cut :
    forall B C t u x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> iproof hole (rule_cut_hyp1 H B u)
      -> iproof hole (rule_cut_hyp2 H x B C t)
      -> iproof hole (rule_cut_concl H C t x u)
| iproof_equal_in_base :
    forall a b H,
      iproof hole (rule_equal_in_base_hyp1 a b H)
      -> (forall v, LIn v (free_vars a) -> iproof hole (rule_equal_in_base_hyp2 v H))
      -> iproof hole (rule_equal_in_base_concl a b H)
| iproof_hypothesis :
    forall x A G J,
      iproof hole (rule_hypothesis_concl G J A x)
| iproof_cequiv_subst_concl :
    forall C x a b t H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> iproof hole (rule_cequiv_subst_hyp1 H x C b t)
      -> iproof hole (rule_cequiv_subst_hyp2 H a b)
      -> iproof hole (rule_cequiv_subst_hyp1 H x C a t)
| iproof_approx_member_eq :
    forall a b H,
      iproof hole (rule_approx_member_eq_hyp a b H)
      -> iproof hole (rule_approx_member_eq_concl a b H).

Fixpoint map_option
         {T U : Type}
         (f : T -> option U)
         (l : list T) : option (list U) :=
  match l with
  | [] => Some []
  | t :: ts =>
    match f t, map_option f ts with
    | Some u, Some us => Some (u :: us)
    | _, _ => None
    end
  end.

Fixpoint map_option_in
         {T U : Type}
         (l : list T)
  : forall (f : forall (t : T) (i : LIn t l), option U), option (list U) :=
  match l with
  | [] => fun f => Some []
  | t :: ts =>
    fun f =>
      match f t (@inl (t = t) (LIn t ts) eq_refl), map_option_in ts (fun x i => f x (inr i)) with
      | Some u, Some us => Some (u :: us)
      | _, _ => None
      end
  end.

Fixpoint map_option_in_fun
         {T U}
         (l : list T)
  : (forall t, LIn t l -> option (U t)) -> option (forall t, LIn t l -> U t) :=
  match l with
  | [] => fun f => Some (fun t (i : LIn t []) => match i with end)
  | t :: ts =>
    fun (f : forall x, LIn x (t :: ts) -> option (U x)) =>
      match f t (@inl (t = t) (LIn t ts) eq_refl),
            map_option_in_fun ts (fun x i => f x (inr i)) with
      | Some u, Some g => Some (fun x (i : LIn x (t :: ts)) =>
                                   match i with
                                   | inl e => transport e u
                                   | inr j => g x j
                                   end)
      | _, _ => None
      end
  end.

Fixpoint finish_proof
         {o} {seq : @baresequent o} {h : bool}
         (prf: iproof h seq) : option (iproof false seq) :=
  match prf with
  | iproof_hole s e => None
  | iproof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match finish_proof pa, finish_proof pb with
    | Some p1, Some p2 => Some (iproof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end
  | iproof_approx_refl a H => Some (iproof_approx_refl _ a H)
  | iproof_cequiv_approx a b H p1 p2 =>
    match finish_proof p1, finish_proof p2 with
    | Some p1, Some p2 => Some (iproof_cequiv_approx _ a b H p1 p2)
    | _, _ => None
    end
  | iproof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_proof p1, finish_proof p2 with
    | Some p1, Some p2 => Some (iproof_approx_eq _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | iproof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_proof p1, finish_proof p2 with
    | Some p1, Some p2 => Some (iproof_cequiv_eq _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | iproof_bottom_diverges x H J => Some (iproof_bottom_diverges _ x H J)
  | iproof_cut B C t u x H wB cBH nixH pu pt =>
    match finish_proof pu, finish_proof pt with
    | Some p1, Some p2 => Some (iproof_cut _ B C t u x H wB cBH nixH p1 p2)
    | _, _ => None
    end
  | iproof_equal_in_base a b H p1 pl =>
    let op := map_option_in_fun (free_vars a) (fun v i => finish_proof (pl v i)) in
    match finish_proof p1, op with
    | Some p1, Some g => Some (iproof_equal_in_base _ a b H p1 g)
    | _, _ => None
    end
  | iproof_hypothesis x A G J => Some (iproof_hypothesis _ x A G J)
  | iproof_cequiv_subst_concl C x a b t H wa wb ca cb p1 p2 =>
    match finish_proof p1, finish_proof p2 with
    | Some p1, Some p2 => Some (iproof_cequiv_subst_concl _ C x a b t H wa wb ca cb p1 p2)
    | _, _ => None
    end
  | iproof_approx_member_eq a b H p1 =>
    match finish_proof p1 with
    | Some p1 => Some (iproof_approx_member_eq _ a b H p1)
    | _ => None
    end
  end.

Definition address := list nat.

Fixpoint get_sequent_at_address {o}
           {ib   : bool}
           {seq  : @baresequent o}
           (prf  : iproof ib seq)
           (addr : address) : option baresequent :=
  match prf with
  | iproof_hole s e =>
    match addr with
    | [] => Some s
    | _ => None
    end
  | iproof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match addr with
    | [] => Some (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    | 1 :: addr => get_sequent_at_address pa addr
    | 2 :: addr => get_sequent_at_address pb addr
    | _ => None
    end
  | iproof_approx_refl a H =>
    match addr with
    | [] => Some (rule_approx_refl_concl a H)
    | _ => None
    end
  | iproof_cequiv_approx a b H p1 p2 =>
    match addr with
    | [] => Some (rule_cequiv_approx_concl a b H)
    | 1 :: addr => get_sequent_at_address p1 addr
    | 2 :: addr => get_sequent_at_address p2 addr
    | _ => None
    end
  | iproof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match addr with
    | [] => Some (rule_approx_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr => get_sequent_at_address p1 addr
    | 2 :: addr => get_sequent_at_address p2 addr
    | _ => None
    end
  | iproof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match addr with
    | [] => Some (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr => get_sequent_at_address p1 addr
    | 2 :: addr => get_sequent_at_address p2 addr
    | _ => None
    end
  | iproof_bottom_diverges x H J =>
    match addr with
    | [] => Some (rule_bottom_diverges_concl x H J)
    | _ => None
    end
  | iproof_cut B C t u x H wB cBH nixH pu pt =>
    match addr with
    | [] => Some (rule_cut_concl H C t x u)
    | 1 :: addr => get_sequent_at_address pu addr
    | 2 :: addr => get_sequent_at_address pt addr
    | _ => None
    end
  | iproof_equal_in_base a b H p1 pl =>
    match addr with
    | [] => Some (rule_equal_in_base_concl a b H)
    | 1 :: addr => get_sequent_at_address p1 addr
    | _ => None (* TODO *)
    end
  | iproof_hypothesis x A G J =>
    match addr with
    | [] => Some (rule_hypothesis_concl G J A x)
    | _ => None
    end
  | iproof_cequiv_subst_concl C x a b t H wa wb ca cb p1 p2 =>
    match addr with
    | [] => Some (rule_cequiv_subst_hyp1 H x C a t)
    | 1 :: addr => get_sequent_at_address p1 addr
    | 2 :: addr => get_sequent_at_address p2 addr
    | _ => None
    end
  | iproof_approx_member_eq a b H p1 =>
    match addr with
    | [] => Some (rule_approx_member_eq_concl a b H)
    | 1 :: addr => get_sequent_at_address p1 addr
    | _ => None
    end
  end.


(*
Inductive test : nat -> Type :=
| Foo : test 1
| Bar : test 0.

(* works *)
Definition xxx {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => Bar
  end.

(* works *)
Definition yyy {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | x => x
  end.

(* works *)
Definition www {n : nat} (t : test n) : option (test n) :=
  match t with
  | Foo => Some Foo
  | Bar => None
  end.

(* doesn't work *)
Definition zzz {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => t
  end.
*)

Definition proof_update_fun {o} (hole : bool) (s seq : @baresequent o) :=
  iproof hole s -> iproof hole seq.

Definition proof_update {o} (hole : bool) (seq : @baresequent o) :=
  {s : @baresequent o & proof_update_fun hole s seq}.

Definition ProofUpdate {o} (hole : bool) (seq : @baresequent o) :=
  option (proof_update hole seq).

Definition retProofUpd
           {o} {hole : bool} {seq : @baresequent o}
           (s : @baresequent o)
           (f : iproof hole s -> iproof hole seq)
  : ProofUpdate hole seq :=
  Some (existT _ s f).

Definition idProofUpd
           {o} {hole : bool}
           (seq : @baresequent o)
  : ProofUpdate hole seq :=
  retProofUpd seq (fun p => p).

Definition noProofUpd {o} {hole : bool} {seq : @baresequent o}
  : ProofUpdate hole seq :=
  None.

Definition bindProofUpd
           {o} {hole : bool} {seq1 seq2 : @baresequent o}
           (pu  : ProofUpdate hole seq1)
           (puf : iproof hole seq1 -> iproof hole seq2)
  : ProofUpdate hole seq2 :=
  match pu with
  | Some (existT s f) => retProofUpd s (fun p => puf (f p))
  | None => None
  end.

Fixpoint get_sequent_fun_at_address {o}
           {hole : bool}
           {seq  : @baresequent o}
           (prf  : iproof hole seq)
           (addr : address) : ProofUpdate hole seq :=
  match prf with
  | iproof_hole s e =>
    match addr with
    | [] => idProofUpd s
    | _ => noProofUpd
    end
  | iproof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match addr with
    | [] => idProofUpd (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pa addr)
        (fun x => iproof_isect_eq hole a1 a2 b1 b2 x1 x2 y i H niyH x pb)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pb addr)
        (fun x => iproof_isect_eq hole a1 a2 b1 b2 x1 x2 y i H niyH pa x)
    | _ => noProofUpd
    end
  | iproof_approx_refl a H =>
    match addr with
    | [] => idProofUpd (rule_approx_refl_concl a H)
    | _ => noProofUpd
    end
  | iproof_cequiv_approx a b H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_approx_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => iproof_cequiv_approx _ a b H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => iproof_cequiv_approx _ a b H p1 x)
    | _ => noProofUpd
    end
  | iproof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_approx_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => iproof_approx_eq _ a1 a2 b1 b2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => iproof_approx_eq _ a1 a2 b1 b2 i H p1 x)
    | _ => noProofUpd
    end
  | iproof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => iproof_cequiv_eq _ a1 a2 b1 b2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => iproof_cequiv_eq _ a1 a2 b1 b2 i H p1 x)
    | _ => noProofUpd
    end
  | iproof_bottom_diverges x H J =>
    match addr with
    | [] => idProofUpd (rule_bottom_diverges_concl x H J)
    | _ => noProofUpd
    end
  | iproof_cut B C t u x H wB cBH nixH pu pt =>
    match addr with
    | [] => idProofUpd (rule_cut_concl H C t x u)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pu addr)
        (fun z => iproof_cut _ B C t u x H wB cBH nixH z pt)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pt addr)
        (fun z => iproof_cut _ B C t u x H wB cBH nixH pu z)
    | _ => noProofUpd
    end
  | iproof_equal_in_base a b H p1 pl =>
    match addr with
    | [] => idProofUpd (rule_equal_in_base_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => iproof_equal_in_base _ a b H z pl)
    | _ => noProofUpd (* TODO *)
    end
  | iproof_hypothesis x A G J =>
    match addr with
    | [] => idProofUpd (rule_hypothesis_concl G J A x)
    | _ => noProofUpd
    end
  | iproof_cequiv_subst_concl C x a b t H wa wb ca cb p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_subst_hyp1 H x C a t)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => iproof_cequiv_subst_concl _ C x a b t H wa wb ca cb z p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun z => iproof_cequiv_subst_concl _ C x a b t H wa wb ca cb p1 z)
    | _ => noProofUpd
    end
  | iproof_approx_member_eq a b H p1 =>
    match addr with
    | [] => idProofUpd (rule_approx_member_eq_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => iproof_approx_member_eq _ a b H z)
    | _ => noProofUpd
    end
  end.

Definition FHole : bool := false.

Definition proof {o} (s : @baresequent o) : Type := iproof FHole s.

Definition proof_isect_eq           {o} := @iproof_isect_eq           o FHole.
Definition proof_approx_refl        {o} := @iproof_approx_refl        o FHole.
Definition proof_cequiv_approx      {o} := @iproof_cequiv_approx      o FHole.
Definition proof_approx_eq          {o} := @iproof_approx_eq          o FHole.
Definition proof_cequiv_eq          {o} := @iproof_cequiv_eq          o FHole.
Definition proof_bottom_diverges    {o} := @iproof_bottom_diverges    o FHole.
Definition proof_cut                {o} := @iproof_cut                o FHole.
Definition proof_equal_in_base      {o} := @iproof_equal_in_base      o FHole.
Definition proof_hypothesis         {o} := @iproof_hypothesis         o FHole.
Definition proof_cequiv_subst_concl {o} := @iproof_cequiv_subst_concl o FHole.
Definition proof_approx_member_eq   {o} := @iproof_approx_member_eq   o FHole.

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall lib (seq : @baresequent o) (wf : wf_bseq seq),
    proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p
    as [ (* hole               *) s f
       | (* isect_eq           *) a1 a2 b1 b2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl        *) a hs
       | (* cequiv_approx      *) a b hs p1 ih1 p2 ih2
       | (* approx_eq          *) a1 a2 b1 b2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq          *) a1 a2 b1 b2 i hs p1 ih1 p2 ih2
       | (* bottom_diverges    *) x hs js
       | (* cut                *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base      *) a b H p1 ih1 ps ihs
       | (* hypothesis         *) x A G J
       | (* cequiv_subst_concl *) C x a b t H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq   *) a b H p ih
       ];
    allsimpl;
    allrw NVin_iff.

  - inversion f.

  - apply (rule_isect_equality_true3 lib a1 a2 b1 b2 x1 x2 y i hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality_wf2 y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality_wf2 y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

  - apply (rule_approx_refl_true3 lib hs a); simpl; tcsp.

  - apply (rule_cequiv_approx_true3 lib hs a b); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx_wf2 a b hs); simpl; tcsp.

  - apply (rule_approx_eq_true3 lib a1 a2 b1 b2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_approx_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_approx_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

  - apply (rule_cequiv_eq_true3 lib a1 a2 b1 b2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_cequiv_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_cequiv_eq_wf2 a1 a2 b1 b2 i hs); simpl; tcsp.

  - apply (rule_bottom_diverges_true3 lib x hs js); simpl; tcsp.

  - apply (rule_cut_true3 lib hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

  - apply (rule_equal_in_base_true3 lib); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base_rest in xx; rw in_map_iff in xx; exrepnd; subst.
    applydup Vin_iff in xx1.
    pose proof (ihs a0) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base_wf2 H a b) as w.
    apply w; simpl; tcsp.
    right.
    rw in_map_iff; eexists; dands; eauto.

  - apply (rule_hypothesis_true3 lib); simpl; tcsp.

  - apply (rule_cequiv_subst_concl_true3 lib H x C a b t); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply ih1.
      apply (rule_cequiv_subst_concl_wf2 H x C a b t); simpl; tcsp.

    + apply ih2.
      apply (rule_cequiv_subst_concl_wf2 H x C a b t); simpl; tcsp.

  - apply (rule_approx_member_eq_true3 lib); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq_wf2 a b H); simpl; tcsp.
Qed.

Lemma test {o} :
  @sequent_true2 o emlib (mk_baresequent [] (mk_conclax ((mk_member mk_axiom mk_unit)))).
Proof.
  apply valid_proof;
  [ exact (eq_refl, (eq_refl, eq_refl))
  | exact (proof_approx_member_eq (mk_axiom) (mk_axiom) (nil) (proof_approx_refl (mk_axiom) (nil)))
          (* This last bit was generated by JonPRL; I've got to generate the whole thing now *)
  ].
Qed.

Definition list1 {T} : forall a : T, LIn a [a].
Proof.
  tcsp.
Qed.

Check (iproof_approx_member_eq
         true
         mk_axiom
         mk_axiom
         nil
         (iproof_hole
            true
            (rule_approx_refl_concl mk_axiom [])
            eq_refl)).


(* Looking at how we can define a Nuprl process *)

Lemma eq_opabs_implies :
  forall x y : opabs,
    x = y -> (opabs_name x = opabs_name y
              # opabs_params x = opabs_params y
              # opabs_sign x = opabs_sign y).
Proof.
  introv xx; subst; auto.
Qed.

Lemma opabs_deq : Deq opabs.
Proof.
  introv.
  destruct (decidable_eq_opabs_name x y);
    destruct (decidable_eq_opabs_sign x y);
    destruct (parameters_dec (opabs_params x) (opabs_params y));
    destruct x, y; simpl in *; subst; tcsp;
    try (complete (right; intro xx; apply eq_opabs_implies in xx; tcsp)).
Qed.

Lemma sovar_sig_deq : Deq sovar_sig.
Proof.
  introv.
  destruct x, y.
  destruct (deq_nat n0 n2); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
  destruct (deq_nvar n n1); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
Qed.

Definition same_lib_abs : Deq (opabs # list sovar_sig) :=
  deq_prod _ _ opabs_deq (deq_list sovar_sig_deq).

Definition abs_in_lib {o} opabs1 vars1 (lib : @library o) : bool :=
  existsb
    (fun e =>
       match e with
       | lib_abs opabs vars rhs correct =>
         if same_lib_abs (opabs, vars) (opabs1, vars1)
         then true
         else false
       end)
    lib.

Definition proof_name := String.string.

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def :
    forall (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : @SOTerm o)
           (correct : correct_abs opabs vars rhs),
      command
(* tries to complete a proof if it has no holes *)
| COM_finish_proof :
    proof_name -> command
(* focuses to a node in a proof *)
| COM_focus_proof :
    proof_name -> address -> command.

Record proof_library_entry {o} :=
  MkProofLibEntry
    {
      proof_library_entry_name  : proof_name;
      proof_library_entry_seq   : @baresequent o;
      proof_library_entry_hole  : bool;
      proof_library_entry_proof : iproof proof_library_entry_hole proof_library_entry_seq
    }.

Definition proof_library_entry_upd_proof {o}
           (e : @proof_library_entry o)
           {h : bool}
           (p : iproof h (proof_library_entry_seq e))
  : proof_library_entry :=
  MkProofLibEntry
    o
    (proof_library_entry_name e)
    (proof_library_entry_seq e)
    h
    p.

Definition proof_library {o} := list (@proof_library_entry o).

Record proof_update_seq {o} :=
  MkProofUpdateSeq
    {
      PUS_name  : proof_name;
      PUS_hole  : bool;
      PUS_seq   : @baresequent o;
      PUS_focus : baresequent;
      PUS_upd   : proof_update_fun PUS_hole PUS_focus PUS_seq
    }.

Definition ProofUpdateSeq {o} :=
  option (@proof_update_seq o).

Record NuprlState {o} :=
  MkNuprlState
    {
      NuprlState_def_library   : @library o;
      NuprlState_proof_library : @proof_library o;
      NuprlState_focus         : @ProofUpdateSeq o
    }.

Definition NuprlState_upd_def_lib {o}
           (state : @NuprlState o)
           (lib   : @library o) : NuprlState :=
  @MkNuprlState
    o
    lib
    (NuprlState_proof_library state)
    (NuprlState_focus state).

Definition NuprlState_upd_proof_lib {o}
           (state : @NuprlState o)
           (lib   : @proof_library o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    lib
    (NuprlState_focus state).

Definition NuprlState_upd_focus {o}
           (state : @NuprlState o)
           (upd   : @ProofUpdateSeq o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    (NuprlState_proof_library state)
    upd.

Fixpoint finish_proof_in_library {o}
           (lib : @proof_library o)
           (name : proof_name) : proof_library :=
  match lib with
  | [] => []
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then if proof_library_entry_hole p (* no need to finish the proof if it is already finished *)
         then let p' := option_with_default
                          (option_map (fun p' => proof_library_entry_upd_proof p p')
                                      (finish_proof (proof_library_entry_proof p)))
                          p
              in p' :: ps
         else p :: ps
    else p :: finish_proof_in_library ps name
  end.

Fixpoint focus_proof_in_library {o}
           (lib : @proof_library o)
           (name : proof_name)
           (addr : address) : ProofUpdateSeq :=
  match lib with
  | [] => None
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then match get_sequent_fun_at_address (proof_library_entry_proof p) addr with
         | Some (existT s f) =>
           Some (MkProofUpdateSeq
                   o
                   name
                   (proof_library_entry_hole p)
                   (proof_library_entry_seq p)
                   s
                   f)
         | None => None
         end
    else focus_proof_in_library ps name addr
  end.

Definition update {o}
           (state : @NuprlState o)
           (com   : command) : NuprlState :=
  match com with
  | COM_add_def opabs vars rhs correct =>
    let lib := NuprlState_def_library state in
    if abs_in_lib opabs vars lib
    then state
    else NuprlState_upd_def_lib state (lib_abs opabs vars rhs correct :: lib)
  | COM_finish_proof name =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_proof_lib state (finish_proof_in_library lib name)
  | COM_focus_proof name addr =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_focus state (focus_proof_in_library lib name addr)
  end.

CoInductive Loop {o} : Type :=
| proc : (@command o -> Loop) -> Loop.

CoFixpoint loop {o} (state : @NuprlState o) : Loop :=
  proc (fun c => loop (update state c)).


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)
