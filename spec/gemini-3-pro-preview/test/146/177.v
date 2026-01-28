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
  get_first_digit_aux n 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      Z.odd first && Z.odd last
    else
      false
  in
  fold_right (fun x acc => if check x then 1 + acc else acc) 0 nums.

Example test_case_2:
  specialFilter [120; 121; 414; 214; 357; 8518; 21517; 2123; 918; 2123; 21517] = 2.
Proof.
  reflexivity.
Qed.