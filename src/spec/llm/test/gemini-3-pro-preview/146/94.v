Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if Nat.ltb n 10 then n
    else get_first_digit_aux fuel' (n / 10)%nat
  end.

Definition get_first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat n in
  Z.of_nat (get_first_digit_aux n_nat n_nat).

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if Z.gtb n 10 then
      let first := get_first_digit n in
      let last := get_last_digit n in
      andb (Z.odd first) (Z.odd last)
    else false
  in
  fold_right (fun x acc => if check x then 1 + acc else acc) 0 nums.

Example test_specialFilter:
  specialFilter [-23%Z; -16%Z; 42%Z; 99%Z; 56%Z; 104%Z; 42%Z; 104%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.