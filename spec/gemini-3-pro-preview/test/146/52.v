Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat n).

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  fold_right (fun x acc =>
    if (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (get_last_digit x))
    then acc + 1
    else acc) 0 nums.

Example test_case_1: specialFilter [101%Z; -35%Z; 16%Z; 44%Z; -67%Z; -67%Z] = 1%Z.
Proof. reflexivity. Qed.