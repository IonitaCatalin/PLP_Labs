Require Import PeanoNat.
Require Import List.
Import ListNotations.
Local Open Scope nat_scope.

Inductive btree : Type :=
  | empty : btree
  | node : btree->nat->btree->btree.

Definition tree := node (node empty 1 empty)
                         2 
                        (node empty 4 empty).

Definition tree2 := node(node(node empty 3 empty) 1 (node empty 5 empty)) 2 (node empty 4 (node empty 7 empty)).

Fixpoint searchBT(t:btree) (value:nat) : bool :=
  match t with
    | empty => false
    | node l v r => if v =? value
                    then true
                    else orb (searchBT l value) (searchBT r value)
  end.

Compute (searchBT tree 10).
Compute (searchBT tree 34).

Print list.
Check(cons 4 nil).
Check [4;5].

Definition myList := [4;5].
Compute 6 :: myList.
Compute myList ++ myList.
Compute myList ++ [6].
Compute myList.

Fixpoint preOrder (b: btree) : list nat :=
  match b with
    | empty => []
    | node l v r => v::(preOrder l)++(preOrder r)
  end.


Fixpoint inOrder(t:btree) : list nat :=
  match t with
    |empty => []
    |node l v r =>  (inOrder l)++[v]++(inOrder r)
  end.

Fixpoint inOrderSearch (n:nat)(l:list nat) : bool :=
  match l with
    |[] => false
    |cons val list => if val=?n then true else inOrderSearch n list
  end.

Compute inOrderSearch 4 (inOrder tree2).

(**)
Lemma search_is_correct_n_in_list:
  if n exists in list,


Compute preOrder tree.
Compute inOrder tree.


Fixpoint valueOfBtNode(t:btree) : nat :=  
  match t with
    |empty => 0
    |node l v r => v
  end.

Fixpoint numberOfChildren(t:btree) : nat :=
  match t with
    |empty => 0
    |node empty v empty => 0
    |node empty v r => 1
    |node l v empty => 1
    |node l v r => 2
  end.

Fixpoint sibling(t:btree) (value:nat) :list nat:=
  match t with
    |empty => []
    |node l v r => if valueOfBtNode l =? value
                   then [valueOfBtNode r]
                   else if valueOfBtNode r =? value
                   then [valueOfBtNode l]
                   else (sibling l value) ++ (sibling r value)
  end.

Compute (sibling tree 3).

Fixpoint parent(t:btree) (value:nat) :list nat:=
  match t with
    |empty => []
    |node l v r => if orb (valueOfBtNode l =? value) (valueOfBtNode r =? value)
                   then [v]
                   else parent l value++parent r value 
  end.

Compute (parent tree 1).

Fixpoint degree(t:btree) (original:btree) (value:nat) :nat:=
   match t with
    |empty => 0
    |node empty v empty => if(v =? value) then 0+length (parent original v) else 0
    |node empty v r => if(v =? value) then 1 + length (parent original v) else degree r original value
    |node l v empty => if(v =? value) then 1 + length (parent original v) else degree l original value
    |node l v r => if(v =? value) then 2 + length (parent original v) else (degree l original value)+(degree r original value) 
  end.

Compute degree tree tree 3.

Fixpoint findLowestRightValue(t:btree) : nat :=
  match t with
   |empty => 0
   |node empty v empty => v
   |node l v empty => findLowestRightValue l
   |node empty v r => findLowestRightValue r
   |node l v r => findLowestRightValue r
  end.

Fixpoint deleteLowestRightValue(t:btree) : btree :=
  match t with
   |empty => empty
   |node empty v empty => empty
   |node l v empty => deleteLowestRightValue l
   |node empty v r => deleteLowestRightValue r
   |node l v r => deleteLowestRightValue r
  end.

Fixpoint modifyTree(t:btree) : btree :=
  match t with
    |empty => empty
    |node empty v empty => empty
    |node empty v r => node empty v (deleteLowestRightValue r)
    |node l v empty => node (deleteLowestRightValue l) v empty
    |node l v r => node l v (deleteLowestRightValue r)
  end.

Fixpoint delete(t:btree) (value:nat) : btree :=
  match t with
    |empty => empty
    |node empty v empty => if v =? value then empty 
                           else node empty v empty
    |node empty v r => if v =? value then node empty (findLowestRightValue r) (modifyTree r) 
                       else node empty v (delete r value)
    |node l v empty => if v =? value then node (modifyTree l) (findLowestRightValue l) empty 
                       else node (delete l value) v empty
    |node l v r => if v =? value then node l (findLowestRightValue r) (modifyTree r) 
                   else node (delete l value) v (delete r value)
  end.

Compute(delete tree2 7).



Fixpoint mirrorBT(t:btree) : btree :=  
  match t with
    | empty => empty
    | node l v r => node (mirrorBT r) v (mirrorBT l)
  end.

Compute (mirrorBT tree).



Fixpoint searchBTree(t:btree) : bool :=
  match t with
    | empty => true
    | node empty v empty => true
    | node empty v r => v <? (valueOfBtNode r)
    | node l v empty =>(valueOfBtNode l) <? v 
    | node l v r => andb (searchBTree l)(searchBTree r)
  end.

Compute searchBTree(tree).


Fixpoint height(t:btree) : nat :=
  match t with
    | empty => 0
    | node l v r => (max (height l) (height r)) + 1
end.

Compute height(tree).

Fixpoint searchInSearchBTree(t:btree)(value:nat) : bool :=
  match t with
    | empty => false
    | node l v r => if v =? value 
                    then true
                    else if v<?value then searchInSearchBTree r value
                    else searchInSearchBTree l value
  end.

Compute (searchInSearchBTree tree 4).

