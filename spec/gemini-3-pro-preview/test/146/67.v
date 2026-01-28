Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100.

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter (fun n =>
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n))
  ) nums)).

Example test_specialFilter:
  specialFilter [-23; -15; 42; 99; 56; 104; 42; 104; 56] = 1.
Proof.
  compute. reflexivity.
Qed.