Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux n 50.

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition check_num (n : Z) : bool :=
  if n >? 10 then
    let first := get_first_digit n in
    let last := get_last_digit n in
    andb (Z.odd first) (Z.odd last)
  else
    false.

Definition specialFilter (nums : list Z) : Z :=
  fold_right (fun n acc => if check_num n then acc + 1 else acc) 0 nums.

Example test_specialFilter:
  specialFilter [71; 55; -62; 7; 99; 23; 18; 71; 55] = 5.
Proof.
  reflexivity.
Qed.