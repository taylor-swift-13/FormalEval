Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit 100 n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in
  fold_right (fun x count => if check x then count + 1 else count) 0 nums.

Example test_specialFilter : specialFilter [100; 101; 102; 103] = 2.
Proof.
  simpl.
  reflexivity.
Qed.