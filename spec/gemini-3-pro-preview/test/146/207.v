Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    if n >? 10 then
      let fd := get_first_digit 100 n in
      let ld := n mod 10 in
      (Z.odd fd) && (Z.odd ld)
    else false
  in Z.of_nat (length (filter predicate nums)).

Example test_specialFilter : specialFilter [102; 505; 789] = 2.
Proof. reflexivity. Qed.