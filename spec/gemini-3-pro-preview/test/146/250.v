Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (z : Z) : Z :=
    match fuel with
    | O => z
    | S fuel' =>
      if z <? 10 then z else aux fuel' (z / 10)
    end
  in aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10))
  in
  Z.of_nat (length (filter check nums)).

Example test_case: specialFilter [101; 100; 8518; 103; 104; 102] = 2.
Proof.
  compute. reflexivity.
Qed.