Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
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
      (Z.odd first) && (Z.odd last)
    else false
  in
  Z.of_nat (length (filter check nums)).

Example test_case : specialFilter [11; 232; 324; -877; 62; -876; 152; 799] = 2.
Proof. reflexivity. Qed.