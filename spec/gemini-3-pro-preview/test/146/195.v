Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition valid (n : Z) : bool :=
  if n >? 10 then
    let first := get_first_digit n in
    let last := n mod 10 in
    (Z.odd first) && (Z.odd last)
  else false.

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter valid nums)).

Example test_case: specialFilter [11%Z; -12%Z; 93%Z; -125%Z; 121%Z; 109%Z; 93%Z; 11%Z; -12%Z] = 6%Z.
Proof. reflexivity. Qed.