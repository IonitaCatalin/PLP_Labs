Inductive List :=
|nil : List
|cons : nat -> List -> List.

Print List_ind.

Fixpoint append (l1 l2 : List) : List :=
  match l1 with
  | nil => l2
  | cons n l => cons n (append l l2)
end.

Definition list1 := (cons 3 (cons 2 nil)).
Definition list2 := (cons 4 (cons 7 nil)).

Compute (append list1 list2).
Compute (append list2 list1).

Lemma append_nil_left:
  forall l, append nil l = l.
Proof.
  trivial.
Qed.

Lemma append_nil_right:
  forall l, append l nil = l.
Proof.
  induction l.
  - trivial.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma append_assoc :
  forall l1 l2 l3,
    append l1 (append l2 l3) = append (append l1 l2) l3.
Proof.
  induction l1.
  - trivial.
  - intros l2 l3.
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Fixpoint reverse(l : List) : List :=
  match l with
  |nil => nil
  |(cons n l1) => append (reverse l1) (cons n nil)
end.

Lemma helper:
  forall l l2,
     reverse ( append l l2) = 
     append (reverse l2) (reverse l).
Proof.
  induction l.
  - intros. simpl.
    rewrite append_nil_right.
    reflexivity.
  - intros.
    simpl.
    rewrite IHl.
    rewrite append_assoc.
    reflexivity.
Qed.

Lemma involutive_reverse:
  forall l, reverse (reverse l) = l.
Proof.
  induction l.
  - trivial.
  - simpl.
    rewrite helper.
    rewrite IHl.
    simpl.
    reflexivity.
Qed. 








