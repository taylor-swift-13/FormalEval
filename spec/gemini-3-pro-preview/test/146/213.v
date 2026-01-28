Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (x : Z) : Z :=
    match fuel with
    | O => x
    | S fuel' => if x <? 10 then x else aux fuel' (x / 10)
    end
  in aux 100%nat n.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) : bool :=
    (x >? 10) && (Z.odd (x mod 10)) && (Z.odd (get_first_digit x))
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter:
  specialFilter [11; -12; 93; 121; 109; 93; 11; -12; 93; -12; 121] = 8.
Proof.
  reflexivity.
Qed.