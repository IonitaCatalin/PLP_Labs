(* definitie inductiva pentru o multime finita *)
Inductive day :=
  |monday : day
  |tuesday : day
  |wednesday : day
  |thursday : day
  |friday : day
  |saturday : day
  |sunday : day.

Inductive bool :=
  |true : bool
  |false : bool.

(*functii nerecursive*)
Definition equal (d1 d2 : day) : bool :=
  match d1, d2 with
    |monday, monday => true
    |tuesday, tuesday => true
    |wednesday, wednesday => true
    |thursday, thursday => true
    |friday, friday => true
    |saturday, saturday => true
    |sunday, sunday => true
    | _, _ => false
    end.

Definition not (b1 : bool) : bool :=
  match b1 with
    |true => false
    |false => true
  end.

Definition and (b1 b2 : bool) :=
  match b1 with
    |false => false
    |true => b2
  end.

Definition or (b1 b2 : bool) :=
  match b1 with
    |true => true
    |false => b2
  end.

Eval compute in (not true).
Eval compute in (and true false).
Eval compute in (or true false).

Definition nextDay (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Eval compute in (equal monday monday).
Eval compute in (equal friday monday).
Eval compute in (nextDay friday).

Inductive natural :=
  | O : natural
  | S : natural -> natural.

Check natural.
Check O.
Check (S O).
Check (S (S O)).

(* Functii recursive *)
Fixpoint plus (n1 n2 : natural) : natural :=
  match n1 with
    | O => n2
    | S m => S (plus m n2)
  end.



Fixpoint equalNaturals(n1 n2 : natural):bool:=
match n1 with
| O => match n2 with 
       | O =>true
       | _ =>false
       end

| S x => match n2 with
          | O => false
          | S y => equalNaturals x y
          end

end.

Eval compute in (plus O (S O)).
Eval compute in (plus (S O) (S O)).
Eval compute in ( equalNaturals  O (S O)).
Eval compute in (equalNaturals O O).
Eval compute in (equalNaturals (S (S O)) (S (S O))).


Lemma a1_equal_a2:
  forall a1 a2,a1=a2 ->equalNaturals (S a1) (S a2)=true.
Proof.
    -induction a1.
      simpl.
      intros a2.
      * induction a2.
        trivial.
        
   
    


