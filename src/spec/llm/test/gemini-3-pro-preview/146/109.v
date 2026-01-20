Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit_aux p (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat (Z.abs n)) (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := 
    (x >? 10) && 
    (Z.odd (x mod 10)) && 
    (Z.odd (get_first_digit x)) 
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter:
  specialFilter [11; 12; 13; 14; 15; 16] = 3.
Proof.
  compute. reflexivity.
Qed.