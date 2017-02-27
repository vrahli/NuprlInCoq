(*From http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue-to-brouwer.html*)

Inductive dialogue : Type :=
| dialogue_leaf (n : nat)
| dialogue_node (f : nat -> dialogue) (n : nat).

Definition baire : Type := nat -> nat.

Fixpoint dialogue_eval (d : dialogue) (a : baire) : nat :=
  match d with
  | dialogue_leaf n => n
  | dialogue_node f n => dialogue_eval (f (a n)) a
  end.

Inductive brouwer_tree : Type :=
| brouwer_tree_leaf (n : nat)
| brouwer_tree_node (f : nat -> brouwer_tree).

Fixpoint brouwer_tree_eval (b : brouwer_tree) (a : baire) : nat :=
  match b with
  | brouwer_tree_leaf n => n
  | brouwer_tree_node f => brouwer_tree_eval (f (a 0)) (fun n => a (S n))
  end.

Definition follow (n : nat) (b : brouwer_tree) : brouwer_tree :=
  match b with
  | brouwer_tree_leaf k => b
  | brouwer_tree_node f => f n
  end.

Fixpoint simulate (f : nat -> brouwer_tree) (n : nat) : brouwer_tree :=
  match n with
  | 0 => brouwer_tree_node (fun i => follow i (f i))
  | S k => brouwer_tree_node (fun i => simulate (fun j => follow i (f j)) k)
  end.

Fixpoint convert (d : dialogue) : brouwer_tree :=
  match d with
  | dialogue_leaf n => brouwer_tree_leaf n
  | dialogue_node f n => simulate (fun i => convert (f i)) n
  end.

Lemma follow_correct :
  forall (b : brouwer_tree) (a : baire),
    brouwer_tree_eval b a
    = brouwer_tree_eval (follow (a 0) b) (fun i => a (S i)).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma simulate_correct :
  forall (n : nat) (f : nat -> brouwer_tree) (a : baire),
    brouwer_tree_eval (f (a n)) a
    = brouwer_tree_eval (simulate f n) a.
Proof.
  induction n; intros f a; simpl.
  - apply follow_correct.
  - rewrite <- IHn.
    apply follow_correct.
Qed.

Lemma convert_correct :
  forall (d : dialogue) (a : baire),
    dialogue_eval d a
    = brouwer_tree_eval (convert d) a.
Proof.
  induction d as [|? ind]; intro a; simpl; auto.
  rewrite ind.
  rewrite <- simulate_correct; auto.
Qed.
