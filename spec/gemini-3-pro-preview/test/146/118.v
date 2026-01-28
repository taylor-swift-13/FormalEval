Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint digits_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else digits_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z := digits_aux n 50.

Definition check (n : Z) : bool :=
  if n >? 10 then
    let first := get_first_digit n in
    let last := n mod 10 in
    (Z.odd first) && (Z.odd last)
  else false.

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [-2; 4; 6; 8; 14; 10; 12; 15] = 1.
Proof. reflexivity. Qed.