Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && 
    (Z.odd (get_first_digit (Z.abs n) 100)) && 
    (Z.odd (Z.abs n mod 10))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [100; 101; 102; 103; 21517] = 2.
Proof. reflexivity. Qed.