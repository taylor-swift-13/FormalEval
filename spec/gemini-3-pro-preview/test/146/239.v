Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (x : Z) :=
    match fuel with
    | O => x
    | S fuel' => if x <? 10 then x else aux fuel' (x / 10)
    end
  in aux (Z.to_nat (Z.abs n)) (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n))
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [24; 84; 75; -56; 214; 13; -56] = 2.
Proof. reflexivity. Qed.