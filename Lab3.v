Require Import PeanoNat.
Local Open Scope nat_scope.

Require Import List.
Import ListNotations.

Inductive btree : Type :=
  | empty : btree 
  | node : btree->nat->btree->btree.

Definition tree :=node (node empty 7 (node empty 2 empty)) 1 (node(node empty 10 empty)8 (node empty 3 empty)).

Print List.
(*[] == nli*)
Check [].
(*cons pentru a adauga in lista*)
Check (cons 4 []).
Check (cons 5 nil).
Check [4;5].

Definition myList := [4;5].

Compute 6 :: myList.
 (*Concatenarea a doua liste*)
Compute myList++myList.

Fixpoint returnNodeValue(t :btree):nat :=
  match t with
  |empty=>0
  |node l v r =>v  
end.

Fixpoint preorderCrossing(b:btree):list nat :=
  match b with
  | empty => []
  | node l n r => 
    n :: (preorderCrossing l) ++ (preorderCrossing r)
end.

Compute (preorderCrossing tree).
(*Parcurgerea inordine*)

(*Exercitiu 1*)
Fixpoint inorderCrossing(t:btree):list nat :=
  match t with
  |empty => []
  | node l n r => 
    (inorderCrossing l)++[n]++(inorderCrossing r)
end.

Compute (inorderCrossing tree).

(*Exercitiul 2*)
Fixpoint sibling (t:btree) (a:nat):list nat :=
  match t with 
  | node l v r => if (returnNodeValue l) =? a
                  then [(returnNodeValue r)]
                  else if (returnNodeValue r)=? a
                        then [(returnNodeValue l)]
                          else (sibling l a)++(sibling r a)
  | empty => []
  
end.


Compute (sibling tree 8).
Fixpoint parent (t:btree) (a:nat) : list nat :=
  match t with
  | empty => []
  | node l v r => if orb ((returnNodeValue l) =? a) ((returnNodeValue r)=?a)
                    then [v]
                     else (parent l a)++(parent r a)
end.

Fixpoint returnListValue (l:list nat) : nat :=
  match l with
  | [] => 0
  | cons v list => v
end.

Fixpoint isRoot(t:btree):bool :=
 match t with
  | empty => false
  | node l v r => true
end.

Compute parent tree 7.
Compute returnListValue myList.

Fixpoint degree (t original:btree) (a:nat) : list nat :=
  match t with
  | empty => []
  | node empty v empty => if negb( a =? v)
                          then []
                          else if length(parent original v)=? 0
                                then [0]
                                else [1]
  | node l v empty => if negb (a =? v)
                      then []++(degree l original a)
                      else if length(parent original v)=? 0
                            then [1]
                            else [2]

  | node empty v r => if negb ( a=? v)
                      then []++(degree r original a)
                      else if length(parent original v)=? 0
                            then [1]
                            else [2]
  
  | node l v r => if negb ( a =? v)
                    then (degree l original a)++(degree r original a)
                    else if length(parent original v) =? 0
                          then [2]
                          else [3]
end.
Compute length [2].
Compute degree tree tree 7.

Fixpoint findTheRighestNode (t:btree) : nat :=
  match t with
  | empty => 0
  | node l v empty => v
  | node l v r => findTheRighestNode r
end.

Fixpoint deleteTheRighestNode (t original:btree):btree :=
  match t with
  | empty => empty
  | node empty v empty => empty
  | node l v r => deleteTheRighestNode r original
  
end.

Compute deleteTheRighestNode tree tree.
Print tree.
