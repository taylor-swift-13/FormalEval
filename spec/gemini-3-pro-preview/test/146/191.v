Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (n_nat : nat) (fuel : nat) : Z :=
    match fuel with
    | O => 0
    | S fuel' =>
      if Nat.ltb n_nat 10 then Z.of_nat n_nat
      else aux (Nat.div n_nat 10) fuel'
    end
  in aux (Z.to_nat n) (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if Z.gtb n 10 then
      andb (Z.odd (get_first_digit n)) (Z.odd (n mod 10))
    else false
  in Z.of_nat (length (filter check nums)).

Example human_eval_example : specialFilter [-12; 93; -125; 1111; 109; 109] = 4.
Proof.
  compute.
  reflexivity.
Qed.