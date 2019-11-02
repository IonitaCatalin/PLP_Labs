(*Definitie inductiva pentru o multime finita*)
Inductive day :=
  |monday : day
  |tuesday : day
  |wednesday : day
  |thursday : day
  |friday : day
  |saturday : day
  |sunday : day.

Check monday.

Check false.

(*Functii nerecursive*)

Definition equal (d1 d2 : day):bool :=
  match d1,d2 with 
  | monday,monday=>true
  | tuesday,tuesday=>true
  | wednesday,wednesday=>true
  | thursday,thursday=>true
  | friday,friday =>true
  | saturday,saturday =>true
  | sunday,sunday =>true
  | _,_=>false
end.

Eval compute in (equal friday monday).

Inductive natural:=
  | o:natural
  | s:natural->natural.

Check natural.
Check (s o).

(*Functii recursive*)

Fixpoint plus (n1 n2 :natural):=
  match n1 with 
  |o => n2
  |s m => s (plus m n2)
end.

Eval compute in (plus o (s o)).

Eval compute in(plus (s o) (s o)).

Definition nextDay (d1 : day ) : day :=
 match d1 with
  | monday =>tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday =>friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday 
end. 

Eval compute in ( nextDay sunday).

Inductive boolean :=
  |true : boolean
  |false : boolean.

Fixpoint and ( b1 b2 : boolean):=
match b1 with 
  |false => false
  |true =>false 
end.

Fixpoint not (b1:boolean):=
match b1 with
  | true =>false
  |false =>true
end.

Fixpoint or(b1 b2 :boolean):=
match b1 with 
| true => true
| false => b2
end.

Eval compute in ( not true).

Eval compute in ( and true false).

Eval compute in ( or false false).


