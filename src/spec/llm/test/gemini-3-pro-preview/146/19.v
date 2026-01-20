Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
      andb (Z.odd first) (Z.odd last)
    else false
  in
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example test_specialFilter:
  specialFilter [6; 89; -12; 77; 13; 196; 196] = 2.
Proof.
  reflexivity.
Qed.