Require Import PeanoNat.
Local Open Scope nat_scope.


Inductive ErrorNat :=
|Error : ErrorNat
|Num: nat -> ErrorNat.

Inductive Exp :=
| number : ErrorNat -> Exp
| plus : Exp -> Exp -> Exp
| minus : Exp -> Exp -> Exp
| mult : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion number : ErrorNat >-> Exp.
Coercion Num : nat >-> ErrorNat.

Fixpoint plusErr (n1 : ErrorNat) (n2 : ErrorNat) : ErrorNat :=
  match n1,n2 with
  | Error, _ => Error
  | _ , Error => Error
  | Num n1',Num n2' => Num (n1' + n2')
  end.


Fixpoint minusErr (n1 : ErrorNat) (n2 : ErrorNat) : ErrorNat :=
  match n1,n2 with
  | Error, _ => Error
  | _ , Error => Error
  | Num n1',Num n2' => if n1' <? n2' then Error else Num (n1' - n2') 
  end.

Fixpoint multiplyErr (n1 : ErrorNat) (n2 : ErrorNat) : ErrorNat :=
  match n1,n2 with
  | Error, _ => Error
  | _ , Error => Error
  | Num n1',Num n2' => Num (n1' * n2')
  end.

Fixpoint divisionErr (n1 : ErrorNat) (n2 : ErrorNat) : ErrorNat :=
  match n1,n2 with
  | Error, _ => Error
  | _ , Error => Error
  | Num n1',Num n2' => if n2' =? 0 then Error else Num (n1' / n2') 
  end.

Fixpoint eval (exp: Exp) : ErrorNat :=
  match exp with
    |number n => n 
    |plus exp1 exp2 => plusErr (eval exp1)(eval exp2)
    |minus exp1 exp2 => minusErr (eval exp1)(eval exp2)
    |mult exp1 exp2 => multiplyErr(eval exp1)(eval exp2)
    |div exp1 exp2 => divisionErr(eval exp1)(eval exp2)
  end.

Compute (eval(div 7 2)).
Compute (eval (plus 12 3)).
Compute (eval (mult 12 0)).
