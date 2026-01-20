Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  let fix aux (fuel : nat) (curr : Z) : Z :=
    match fuel with
    | O => curr
    | S fuel' => if curr <? 10 then curr else aux fuel' (curr / 10)
    end
  in aux n_nat (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) : bool :=
    (x >? 10) && (Z.odd (x mod 10)) && (Z.odd (first_digit x))
  in
  Z.of_nat (length (filter p nums)).

Example test_case: specialFilter [6; 89; -12; 77; 13; 196] = 2.
Proof.
  compute.
  reflexivity.
Qed.