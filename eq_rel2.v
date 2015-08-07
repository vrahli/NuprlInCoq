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


Notation "! x" := (notT x)%type (at level 75, right associativity).
Notation "T # U" := (T * U)%type (at level 80, right associativity).
Notation "T [+] U" := (T + U)%type (at level 80, right associativity).


(* ========= Here is a constuctive iff ======== *)

(*
Set Printing Universes.

Definition t_iff0 A B := (A -> B) # (B -> A).

Print t_iff0.
*)

Inductive t_iff A B :=
| t_iff_c : (A -> B) # (B -> A) -> t_iff A B.

Lemma t_iff_p1 :
  forall {A B}, t_iff A B -> (A -> B).
Proof.
  intros.
  inversion X.
  inversion X1; auto.
Qed.

Lemma t_iff_p2 :
  forall {A B}, t_iff A B -> (B -> A).
Proof.
  intros.
  inversion X.
  inversion X1; auto.
Qed.

Lemma test_t_iff_p :
  forall {A B}, t_iff A B -> A -> B.
Proof.
  intros.
  apply (t_iff_p1 X); auto.
Qed.

(*
Print t_iff.
*)

Notation "x <=> y" := (t_iff x y) (at level 95, no associativity).


Lemma combine_t_iff_proofs_imp :
  forall {A B A' B'},
    (A <=> A') -> (B <=> B') -> ((A -> B) <=> (A' -> B')).
Proof.
  intros.
  destruct X; destruct X0.
  destruct p; destruct p0.
  constructor; auto.
Qed.

Lemma combine_t_iff_proofs_t_iff :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A <=> B) <=> (A' <=> B')).
Proof.
  intros.
  destruct X; destruct X0.
  destruct p; destruct p0.
  repeat constructor; intro; inversion X; inversion X1; auto.
Qed.

Lemma combine_t_iff_proofs_prod :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A # B) <=> (A' # B')).
Proof.
  intros.
  destruct X; destruct X0.
  destruct p; destruct p0.
  repeat constructor; destruct X; auto.
Qed.

Lemma combine_t_iff_proofs_sum :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A + B) <=> (A' + B')).
Proof.
  intros.
  destruct X; destruct X0.
  destruct p; destruct p0.
  constructor; constructor; intro; destruct X; auto.
Qed.

Lemma combine_t_iff_proofs_not :
  forall {A A'},
    (A <=> A')
    -> (!A <=> !A').
Proof.
  intros.
  destruct X.
  destruct p.
  constructor; constructor; intros; intro; auto.
Qed.

Lemma t_iff_refl :
  forall A, A <=> A.
Proof.
  intros; constructor; auto.
Qed.

Lemma t_iff_sym :
  forall {A B}, (A <=> B) -> (B <=> A).
Proof.
  intros.
  destruct X.
  destruct p.
  constructor; auto.
Qed.

(* this build a proof object of T <=> T[b/a] where p is the proof of a<=>b.
*)
Ltac build_tiff_term T a b p :=
  match T with
    | a => p
    | ?x -> ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_imp l r)
    | ?x <=> ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_t_iff l r)
    | ?x # ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_prod l r)
    | ?x [+] ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_sum l r)
    | !?x =>
      let l := build_tiff_term x a b p in
      constr:(combine_t_iff_proofs_not l)
    | _ => constr:(t_iff_refl T)
  end.

Tactic Notation "thin_last" :=
  match goal with H: ?T |- _ => clear H end.

Ltac apply' H1 H2 :=
  let H3 := fresh in (
    (pose proof (H1 H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (H1 _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (H1 _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (H1 _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (H1 _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3)).

Ltac build_and_rewrite H :=
  let T := type of H in
  match goal with
    | [ |- ?C ] =>
      match T with
        | ?A <=> ?B =>
          let d := build_tiff_term C A B H in
          let name := fresh H in
          remember d as name;
            thin_last;
            (apply (t_iff_p1 name) || apply (t_iff_p2 name));
            clear name
      end
  end.

Ltac build_and_rewrite_hyp H H2 :=
  let T := type of H in
  let C := type of H2 in
  match T with
    | ?A <=> ?B =>
      let d := build_tiff_term C A B H in
      let name := fresh H in
      remember d as name;
        thin_last;
        (apply' (t_iff_p1 name) H2 || apply' (t_iff_p2 name) H2);
        clear name
  end.

Ltac build_and_rewrite_rev H :=
  let T := type of H in
  match goal with
    | [ |- ?C ] =>
      match T with
        | ?A <=> ?B =>
          let d := build_tiff_term C B A (t_iff_sym H) in
          let name := fresh H in
          remember d as name;
            thin_last;
            (apply (t_iff_p1 name) || apply (t_iff_p2 name));
            clear name
      end
  end.

Ltac build_and_rewrite_hyp_rev H H2 :=
  let T := type of H in
  let C := type of H2 in
  match T with
    | ?A <=> ?B =>
      let d := build_tiff_term C B A (t_iff_sym H) in
      let name := fresh H in
      remember d as name;
        thin_last;
        (apply' (t_iff_p1 name) H2 || apply' (t_iff_p2 name) H2);
        clear name
  end.

Tactic Notation "trewrite" ident(H) :=
       build_and_rewrite H.


Tactic Notation "trewrite" ident(H) "in" ident (H') :=
       build_and_rewrite_hyp H H'.


Tactic Notation "trewrite" "<-" ident(H) :=
       build_and_rewrite_rev H.


Tactic Notation "trewrite" "<-" ident(H) "in" ident(H') :=
       build_and_rewrite_hyp_rev H H'.




Ltac get_instance_of T H Hn :=
  match H with
    | _ =>
     let name:= fresh "Htemp" in
      (* idtac "trying gio" H;*)
     progress (
        (pose proof (fun h:H => (t_iff_p1 T) h) as name)||
        (pose proof (fun h:H => (t_iff_p1 (T _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p1 (T _ _ _ _ _ _ _ _)) h) as name)
      ); (* idtac "succeded" H; *)
     let H2 := type of name in
         match H2 with
         | ?H -> ?H2 =>
                clear name;
                assert (H <=> H2) as Hn by (apply T)
                (*; idtac "really succeded" H *)
         end

    | ?Hl <=> ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | ?Hl # ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | ?Hl [+] ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | !?Hl => get_instance_of T Hl Hn
    | ?Hl -> ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
  end.

Ltac get_instance_of_rev  T  H Hn :=
  match H with
    | _ =>
     let name:= fresh "Htemp" in
      (* idtac "trying gio" H;*)
     progress (
        (pose proof (fun h:H => (t_iff_p2 T) h) as name)||
        (pose proof (fun h:H => (t_iff_p2 (T _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (t_iff_p2 (T _ _ _ _ _ _ _ _)) h) as name) 
      ); (* idtac "succeded" H;*)
     let H2 := type of name in
         match H2 with
         | ?H -> ?H2 => 
                clear name;
                assert (H2 <=> H) as Hn by (apply T) 
                (** H2 in LHS; apply does not automatically take care
                    of symmetry *)
                (*; idtac "really succeded" H*)
         end

    | ?Hl <=> ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | ?Hl # ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | ?Hl [+] ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | !?Hl => get_instance_of_rev T Hl Hn
    | ?Hl -> ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
  end.

(** rewrite using a universally quantified t_iff relation T  in the conclusion *)
Ltac trw T :=
  match goal with
      [  |- ?C ] =>
      let name:= fresh "Hget_instance_of_in_concl" in
      get_instance_of T C name; 
        build_and_rewrite name; clear name
  end.

Ltac trw_rev  T :=
  match goal with
      [  |- ?C ] =>
      let name:= fresh "Hget_instance_of_in_concl" in
      get_instance_of_rev T C name;
        build_and_rewrite_rev name ; clear name
  end.


Ltac trw_h T h :=
  let C := type of h in
  let name:= fresh "Hget_instance_of_in_concl" in
  get_instance_of T C name;  
    build_and_rewrite_hyp name h; clear name.


Ltac trw_rev_h T h :=
  let C := type of h in
  let name:= fresh "Hget_instance_of_in_concl" in
  get_instance_of_rev T C name;
    build_and_rewrite_hyp_rev name h; clear name.



(* Some general notation to use the above tactics *)

Tactic Notation "rw" constr(T) :=
  trw T || rewrite T.
Tactic Notation "rw" "<-" constr(T) :=
  trw_rev T || rewrite <- T.
Tactic Notation "rw" constr(T) "in" ident(H) :=
  trw_h T H || rewrite T in H.
Tactic Notation "rw" "<-" constr(T) "in" ident(H) :=
  trw_rev_h T H || rewrite <- T in H.

Tactic Notation "allrw" :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (trw H || rewrite H)
          end.

Tactic Notation "allrw" "<-" :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (trw_rev H || rewrite <- H)
          end.

Tactic Notation "allrw" constr(T) :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
          end.

Tactic Notation "allrw" "<-" constr(T) :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (trw_rev_h T H || trw_rev T || rewrite <- T in H || rewrite <- T)
          end.

(* ------------------------ *)



Theorem trw_demo: forall (P Q: nat -> Type),
 (forall n, P n <=> Q n )
  -> ((P 1 * False -> False ) <=> (Q 1 * False -> False )).
Proof.
  intros ? ?  Hiff.
  assert (P 1) by admit.
  trw_h Hiff  X.
  trw Hiff .  apply t_iff_refl.
Qed.


Theorem trw_demo2: forall (P Q: nat -> Type),
 (forall n, P n <=> forall m, Q m )
  -> ((P 1 * False -> False ) <=> ((forall m, Q m) * False -> False )).
Proof.
intros ? ?  Hiff. trw Hiff. apply t_iff_refl.
Qed.


(**  --- setoid stuff -- delete? *)

Require Export Coq.Setoids.Setoid.
Inductive Cast : Type -> Prop :=
| cast : forall t : Type, t -> Cast t.

Inductive Cast2 : Prop -> Type :=
| cast2 : forall p : Prop, p -> Cast2 p.

Hint Constructors Cast.
Hint Constructors Cast2.

Definition c_t_iff : relation Type :=
  fun A B : Type => Cast (t_iff A B).

Notation "x <==> y" := (c_t_iff x y) (at level 95, no associativity).

Definition t_c_iff : relation Type :=
  fun A B : Type => Cast (A -> B) /\ Cast (B -> A).

Notation "x <~> y" := (t_c_iff x y) (at level 95, no associativity).

Lemma CType_S : Setoid_Theory Type c_t_iff.
Proof.
  split.

  repeat constructor; auto.

  unfold Symmetric; intros.
  inversion H; subst.
  destruct X; destruct p.
  repeat constructor; auto.

  unfold Transitive; intros.
  inversion H; inversion H0; subst.
  destruct X; destruct X0; destruct p; destruct p0.
  repeat constructor; auto.
Qed.

Lemma TypeC_S : Setoid_Theory Type t_c_iff.
Proof.
  split.

  repeat constructor; auto.

  unfold Symmetric; intros.
  destruct H.
  inversion H; subst.
  inversion H0; subst.
  repeat constructor; auto.

  unfold Transitive; intros.
  destruct H; destruct H0.
  inversion H; inversion H0; inversion H1; inversion H2; subst.
  repeat constructor; auto.
Qed.

Add Setoid Type c_t_iff CType_S as Type_iff_reg.
Add Setoid Type t_c_iff TypeC_S as Type_iff_reg2.

Hint Resolve (Seq_refl  Type c_t_iff CType_S): setoid.
Hint Resolve (Seq_sym   Type c_t_iff CType_S): setoid.
Hint Resolve (Seq_trans Type c_t_iff CType_S): setoid.

Hint Resolve (Seq_refl  Type t_c_iff TypeC_S): setoid.
Hint Resolve (Seq_sym   Type t_c_iff TypeC_S): setoid.
Hint Resolve (Seq_trans Type t_c_iff TypeC_S): setoid.

(* ============================================== *)

(*
Lemma test :
  forall a b (*c f*), (a <=> b) -> Cast a. (*.  # { x : c | f x }.*)
Proof.
  intros.
  rewrite X.
Qed.
*)

(** should not be required anymore? *)

Tactic Notation "trewrite" "<-" ident(H) ident(p1) :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_rev name;
    clear name.

Tactic Notation "trewrite" "<-" ident(H) ident(p1) ident(p2) :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_rev name;
    clear name.
Tactic Notation "trewrite" ident(H) ident(p1) :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite name;
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) ident(p2) :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite name;
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) "in" ident (H') :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_hyp name H';
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) ident(p2) "in" ident (H') :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_hyp name H';
    clear name.
Tactic Notation "trewrite" "<-" ident(H) ident(p1) "in" ident(H') :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_hyp_rev name H';
    clear name.

Tactic Notation "trewrite" "<-" ident(H) ident(p1) ident(p2) "in" ident(H') :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_hyp_rev name H';
    clear name.


Theorem dont_touch_forall: forall (P Q: nat -> Type),
 (forall n, (P n <=> (forall m, Q (m+n))) ) 
  -> (P 1) -> forall m, Q (m+1).
Proof. 
 intros ? ?  Hif Hp1.
  trw_h Hif Hp1; trivial.
Qed. 


Theorem dont_touch_forall2: forall (P Q: nat -> Type),
 (forall n, (P n <=> (forall m, Q (m+n))) ) 
  -> (P 1) -> forall m, Q (m+1).
Proof. 
intros ? ?  Hif Hp1. 
  trw_rev Hif. trivial.
Qed. 

Theorem dont_touch_forall3: forall (P Q: nat -> Type),
 (forall n, (P n <=> (forall m, Q (m+n))) ) 
  ->  (forall m, Q (m+1) )-> (P 1) .
Proof. 
intros ? ?  Hif Hq . 
trw_rev_h Hif Hq. trivial. 
Qed. 
