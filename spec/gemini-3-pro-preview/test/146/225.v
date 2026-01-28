Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope bool_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (x : Z) (fuel : nat) : Z :=
    match fuel with
    | O => x
    | S fuel' => 
      if x <? 10 then x else aux (x / 10) fuel'
    end
  in aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else
      false
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [120; 122; 414; 214; 415; 45; 357; 8518; 21517; 2123; 122; 918; 2123; 21517; 918] = 1.
Proof.
  reflexivity.
Qed.