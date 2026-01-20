Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (m : Z) (fuel : nat) : Z :=
    match fuel with
    | O => m
    | S fuel' =>
      if m <? 10 then m else aux (m / 10) fuel'
    end
  in aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) : bool :=
    if x >? 10 then
      (Z.odd (get_first_digit x)) && (Z.odd (x mod 10))
    else
      false
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter:
  specialFilter [57; -23; -15; 42; 99; 104] = 2.
Proof. reflexivity. Qed.