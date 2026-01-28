Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if Z.ltb n 10 then n 
      else first_digit_aux (Z.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 100.

Definition get_last_digit (n : Z) : Z :=
  Z.rem (Z.abs n) 10.

Definition specialFilter (nums : list Z) : Z :=
  let count (n : Z) :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (get_last_digit n)) in
  Z.of_nat (length (filter count nums)).

Example test_specialFilter: specialFilter [-324; 456; 1111; 7113; 63] = 2.
Proof.
  compute.
  reflexivity.
Qed.