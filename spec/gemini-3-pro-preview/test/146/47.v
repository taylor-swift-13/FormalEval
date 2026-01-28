Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 20.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (x : Z) :=
    (x >? 10) && (Z.odd (first_digit x)) && (Z.odd (x mod 10))
  in Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [-8; 62; 37; 6; -76; 6] = 1.
Proof. reflexivity. Qed.