Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_fuel (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_fuel n 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else
      false
  in
  fold_right (fun n c => if check n then c + 1 else c) 0 nums.

Example test_specialFilter: specialFilter [63; 24; 84; 75; -56; 13] = 2.
Proof.
  reflexivity.
Qed.