Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | 0%nat => n
  | S fuel' =>
    if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter : specialFilter [14; -8; 62; -123; 39; -8] = 1.
Proof.
  reflexivity.
Qed.