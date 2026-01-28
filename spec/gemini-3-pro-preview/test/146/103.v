Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := negb (Z.even n).

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    if n >? 10 then
      let fd := get_first_digit 100 n in
      let ld := n mod 10 in
      is_odd fd && is_odd ld
    else false
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [-62; 232; 324; -46; -876; 152; 799; 324] = 1.
Proof. reflexivity. Qed.