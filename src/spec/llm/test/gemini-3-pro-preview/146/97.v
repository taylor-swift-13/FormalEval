Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : nat) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Nat.ltb n 10 then Z.of_nat n
      else get_first_digit_aux (Nat.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat n in
  get_first_digit_aux n_nat n_nat.

Definition specialFilter (nums : list Z) : Z :=
  let p (n : Z) : bool :=
    if Z.gtb n 10 then
      let first := get_first_digit n in
      let last := Z.rem n 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [-23%Z; -16%Z; 99%Z; 56%Z; 104%Z; 42%Z; 104%Z] = 1%Z.
Proof. compute. reflexivity. Qed.