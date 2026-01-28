Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := (n mod 2 =? 1).

Fixpoint first_digit_aux (n : nat) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if (Nat.ltb n 10) then Z.of_nat n
      else first_digit_aux (Nat.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat (Z.abs n)) (Z.to_nat (Z.abs n)).

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool := 
    (x >? 10) && 
    (is_odd (get_first_digit x)) && 
    (is_odd (x mod 10)) in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [123; 505; 789; 111] = 4.
Proof.
  vm_compute. reflexivity.
Qed.