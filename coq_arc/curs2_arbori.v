Inductive BinTree :=
|leaf : BinTree
|node : nat -> BinTree -> BinTree -> BinTree.

Print BinTree_ind.

Require Import Nat.
Require Import List.
Import ListNotations.

Fixpoint preorder (b : BinTree) : list nat :=
  match b with
  | leaf => []
  | node n ltree rtree => n::(preorder ltree)++(preorder rtree)
  end.

Definition one := (node 1 leaf leaf).
Definition two := (node 2 leaf leaf).
Definition three := (node 3 one two).

Compute (preorder one).
Compute (preorder leaf).
Compute (preorder three).

Fixpoint search (b : BinTree) (x : nat) : bool :=
  match b with
  | leaf => false
  | node n ltree rtree => if (n =? x) then true
                           else orb (search ltree x)(search rtree x)
  end.

Compute (search three 0).
Compute (search three 1).

Lemma search_correct:
  forall b x, In x (preorder b) -> search b x = true.
Proof.
  induction b. 
  - intros.
    simpl.
    simpl in H.
    contradiction.
  - intros.
    simpl in H.
    destruct H as [H | H].
    + rewrite H.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      trivial.
    + simpl in H.
      SearchPattern (In _ (_ ++ _) <-> _).
      rewrite in_app_iff in H.
      destruct H as [H | H].
      * simpl.
        case_eq (Nat.eqb n x).
        ** intros H1. trivial.
        ** intros H1.
           apply IHb1 in H.
           rewrite H.
           trivial.
      * simpl.
        case_eq (Nat.eqb n x).
        ** intros H1. reflexivity.
        ** intros H1.
           apply IHb2 in H.
           rewrite H.
           simpl.
           rewrite Bool.orb_true_r.
           trivial.
Qed.
        

