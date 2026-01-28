Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (x : Z) :=
    match fuel with
    | O => x 
    | S fuel' => if x <? 10 then x else aux fuel' (x / 10)
    end
  in aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let condition (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in
  Z.of_nat (length (filter condition nums)).

Example test_specialFilter: specialFilter [12; 415; 789; 13; 15; 16] = 3.
Proof.
  reflexivity.
Qed.