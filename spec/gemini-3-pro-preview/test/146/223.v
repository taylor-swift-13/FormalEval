Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint digits_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0 
  | S fuel' => 
    if Z.ltb n 10 then n else digits_aux (Z.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  digits_aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let valid (x : Z) :=
    if Z.gtb x 10 then
      let first := get_first_digit x in
      let last := Z.modulo x 10 in
      andb (Z.odd first) (Z.odd last)
    else false in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter:
  specialFilter [63; -55; 84; 83; 75; -56; 13; 12; -55; 63] = 2.
Proof.
  compute. reflexivity.
Qed.