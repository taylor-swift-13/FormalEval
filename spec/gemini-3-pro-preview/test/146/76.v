Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (z : Z) : Z :=
    match fuel with
    | O => z
    | S fuel' => if z <? 10 then z else aux fuel' (z / 10)
    end
  in aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) :=
    (x >? 10) &&
    Z.odd (get_first_digit x) &&
    Z.odd (x mod 10)
  in
  Z.of_nat (List.length (List.filter p nums)).

Example test_specialFilter: specialFilter [57; -23; -15; 42; 99; 56; 104; 42; 99] = 3.
Proof. reflexivity. Qed.