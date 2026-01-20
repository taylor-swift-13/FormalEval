Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n 
      else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let f := get_first_digit n in
      let l := n mod 10 in
      (Z.odd f) && (Z.odd l)
    else false
  in
  fold_right (fun x acc => if check x then 1 + acc else acc) 0 nums.

Example test_case_2 : specialFilter [6%Z; 89%Z; -12%Z; 77%Z; 196%Z; 196%Z] = 1%Z.
Proof.
  reflexivity.
Qed.