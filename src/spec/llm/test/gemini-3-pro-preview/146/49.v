Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    match Nat.div n 10 with
    | O => n
    | n' => first_digit_nat n' fuel'
    end
  end.

Definition get_first_digit (n : Z) : Z :=
  let nat_n := Z.to_nat n in
  Z.of_nat (first_digit_nat nat_n nat_n).

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    if n >? 10 then
      let last := n mod 10 in
      let first := get_first_digit n in
      (Z.odd first) && (Z.odd last)
    else false
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter : specialFilter [239%Z; 39%Z; 152%Z; 240%Z; -339%Z] = 1%Z.
Proof. reflexivity. Qed.