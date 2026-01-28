Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition check (n : Z) : bool :=
  (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [-23%Z; -15%Z; 42%Z; 99%Z; 56%Z; 104%Z; 42%Z] = 1%Z.
Proof. reflexivity. Qed.