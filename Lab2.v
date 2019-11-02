Require Import PeanoNat.
Local Open Scope nat_scope.

Inductive btree : Type :=
  | empty : btree 
  | node : btree->nat->btree->btree.

Definition tree :=node (node empty 7 (node empty 2 empty)) 1 (node(node empty 10 empty)8 empty).

(*OR(orb) - AND(andb)*)

Fixpoint searchBT(t:btree) (value:nat) : bool :=
  match t with
  |empty =>false
  |node l v r => if v=? value 
                  then true
                   else orb (searchBT l value) (searchBT r value)
end.

Compute (searchBT tree 10).
Compute(searchBT tree 24).

(*Oglinditul unui arbore binar de cautare*)
Fixpoint mirroredBT(t:btree):btree:=
  match t with 
  | empty =>empty
  | node l v r => node (mirroredBT r) v (mirroredBT l) 
end.
 

(*Verificare arbore binar de cautare*)
Compute (mirroredBT tree).
(*Valoare unui nod*)
Fixpoint returnNodeValue(t :btree):nat :=
  match t with
  |empty=>0
  |node l v r =>v  
end.

(*Este arbore binar de cautare?*)
Fixpoint isSearchBT(t:btree):bool := 
  match t with
  | empty => true
  | node empty v empty => true
  | node l v empty =>(returnNodeValue l) <?v
  | node empty v r => v <? (returnNodeValue r)
  | node l v r =>andb ((returnNodeValue l)<?v) (v<?(returnNodeValue r))
  
end.

Compute (isSearchBT tree).

Compute (isSearchBT (node (node empty 3 empty) 2 (node empty 4 empty ))).

(*Cautare intr-un arbore binar de cautare*)
Fixpoint searchInBST(t:btree) (n:nat):bool :=
  match t with
  |empty => false
  |node l v r => if n=?v 
                  then true
                  else if n<?v 
                        then searchInBST l n 
                        else searchInBST r n
end.
 
(*Inaltime unui arbore binar*)
Compute searchInBST (tree) (1).
Fixpoint lengthSearchBT(t:btree):nat :=
  match t with
  | empty=>0
  | node l v r => max (lengthSearchBT l) (lengthSearchBT r ) + 1
 end.

Compute(lengthSearchBT tree).
