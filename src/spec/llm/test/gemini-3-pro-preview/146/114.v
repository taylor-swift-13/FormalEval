Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_rec (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_rec fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z := first_digit_rec 100 (Z.abs n).

Definition last_digit (n : Z) : Z := (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n))
  in Z.of_nat (length (filter check nums)).

Example test_case: specialFilter [33; -2; -3; 45; 21; 109; 121; 357; 1892] = 4.
Proof.
  reflexivity.
Qed.