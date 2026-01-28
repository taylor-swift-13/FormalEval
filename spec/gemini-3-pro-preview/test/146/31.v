Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n 100 in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else
      false
  in
  fold_right (fun x acc => (if check x then 1 else 0) + acc) 0 nums.

Example test_case_1 : specialFilter [104; 14; -8; 62; 72; 39] = 1.
Proof. reflexivity. Qed.