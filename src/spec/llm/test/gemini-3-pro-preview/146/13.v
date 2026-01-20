Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.eqb (Z.modulo n 2) 1.

Definition last_digit (n : Z) : Z := Z.modulo (Z.abs n) 10.

Fixpoint first_digit_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' => if Nat.ltb n 10 then n else first_digit_aux (Nat.div n 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  Z.of_nat (first_digit_aux n_nat n_nat).

Definition specialFilter (nums : list Z) : Z :=
  let valid (x : Z) : bool :=
    (x >? 10) && (is_odd (first_digit x)) && (is_odd (last_digit x))
  in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter: specialFilter [55; -62; 7; 99; 23; 18] = 2.
Proof.
  reflexivity.
Qed.