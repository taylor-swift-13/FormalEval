Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit p (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    if n >? 10 then
      let first := get_first_digit 100 n in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else false
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [112; -324; 456; 1111; 7113; 456; 100; 63] = 2.
Proof. reflexivity. Qed.