Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in
  fold_right (fun x acc => if predicate x then acc + 1 else acc) 0 nums.

Example test_specialFilter : specialFilter [-2; 4; -324; 6; 8; 10; 12; 15] = 1.
Proof. reflexivity. Qed.