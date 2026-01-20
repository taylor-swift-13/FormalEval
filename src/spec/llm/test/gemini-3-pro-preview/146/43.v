Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let is_odd (d : Z) : bool := Z.odd d in
  let check (n : Z) : bool :=
    if n >? 10 then
      let f := first_digit n 100 in
      let l := n mod 10 in
      is_odd f && is_odd l
    else false
  in
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example test_case_1 : specialFilter [89; -25; 9; -91; -71; -91; -71; -18; 5] = 0.
Proof.
  compute.
  reflexivity.
Qed.