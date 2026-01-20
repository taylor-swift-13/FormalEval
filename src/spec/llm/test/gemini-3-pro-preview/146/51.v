Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n 20.

Definition check (n : Z) : bool :=
  if n >? 10 then
    let last := n mod 10 in
    let first := get_first_digit n in
    (Z.odd last) && (Z.odd first)
  else
    false.

Definition specialFilter (nums : list Z) : Z :=
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example test_case : specialFilter [10%Z; 22%Z; -76%Z; 37%Z] = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.