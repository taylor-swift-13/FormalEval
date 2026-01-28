Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else digits_fuel (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := digits_fuel n 100.

Definition last_digit (n : Z) : Z := n mod 10.

Definition is_odd (n : Z) : bool := Z.odd n.

Definition check (n : Z) : bool :=
  (n >? 10) && (is_odd (first_digit n)) && (is_odd (last_digit n)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_case: specialFilter [-324; 4; 6; 8; 14; 12; 15] = 1.
Proof.
  simpl.
  reflexivity.
Qed.