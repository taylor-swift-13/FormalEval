Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_last_digit (n : Z) : Z := (Z.abs n) mod 10.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
    if (n <? 10) then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (get_last_digit n)) in
  fold_right (fun x acc => (if check x then 1 else 0) + acc) 0 nums.

Example test_specialFilter: specialFilter [456; -123; 93; 456; 111; 456] = 2.
Proof. reflexivity. Qed.