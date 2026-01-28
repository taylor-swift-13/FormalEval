Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 100.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) : bool :=
    (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (n mod 10))
  in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter: specialFilter [14; -8; 62; 71; -123; 39] = 2.
Proof.
  compute. reflexivity.
Qed.