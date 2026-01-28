Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n 100)) && (Z.odd (n mod 10)) in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter: specialFilter [-2; 4; 6; 8; 14; 10; 12; 103; 15] = 2.
Proof. reflexivity. Qed.