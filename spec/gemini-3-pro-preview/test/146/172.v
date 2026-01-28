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

Definition first_digit (n : Z) : Z := first_digit_aux n 100.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (first_digit n)) in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter : specialFilter [33; -2; -3; 46; 21; -2; 121; 357; 1892; -2; -2] = 3.
Proof. reflexivity. Qed.