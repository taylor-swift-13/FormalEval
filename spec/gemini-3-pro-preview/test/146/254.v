Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat n) n.

Definition check (n : Z) : bool :=
  (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (n mod 10)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [11; 12; 103; 1892; 15; 16] = 3.
Proof.
  reflexivity.
Qed.