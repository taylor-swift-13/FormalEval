Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (m : Z) (fuel : nat) :=
    match fuel with
    | O => m
    | S f => if m <? 10 then m else aux (m / 10) f
    end
  in aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [55; -62; 7; 23; 18] = 1.
Proof. compute. reflexivity. Qed.