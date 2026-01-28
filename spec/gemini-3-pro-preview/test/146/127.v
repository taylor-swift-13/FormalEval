Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd_digit (n : Z) : bool :=
  match n with
  | 1 => true
  | 3 => true
  | 5 => true
  | 7 => true
  | 9 => true
  | _ => false
  end.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else get_first_digit_aux (n / 10) f
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100.

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := 
    if x >? 10 then 
      andb (is_odd_digit (get_first_digit x)) (is_odd_digit (get_last_digit x))
    else false
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [11; 12; 13; 14; 15; 16; 13] = 4.
Proof. reflexivity. Qed.