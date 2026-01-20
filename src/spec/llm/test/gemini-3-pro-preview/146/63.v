Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_fuel fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z := get_first_digit_fuel 100 n.

Definition check (n : Z) : bool :=
  (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_case_1 : specialFilter [39; 152; 240; 39] = 2.
Proof. reflexivity. Qed.