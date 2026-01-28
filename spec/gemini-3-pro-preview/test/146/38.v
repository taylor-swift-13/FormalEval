Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => 
      let abs_n := Z.abs n in
      if abs_n <? 10 then abs_n else first_digit (abs_n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (first_digit n 100))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [39%Z; 152%Z; 240%Z; -339%Z] = 1%Z.
Proof.
  reflexivity.
Qed.