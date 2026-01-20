Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_fuel (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_fuel n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (x mod 10))
  in
  Z.of_nat (length (filter check nums)).

Example test_case_new: specialFilter [239%Z; 39%Z; 152%Z; -35%Z; 240%Z; -339%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.