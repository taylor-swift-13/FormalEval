Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    if x <=? 10 then false
    else
      let first := get_first_digit (Z.to_nat x) x in
      let last := x mod 10 in
      (Z.odd first) && (Z.odd last)
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [100%Z; 101%Z; 103%Z; 102%Z] = 2%Z.
Proof. reflexivity. Qed.