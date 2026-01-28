Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let p (n : Z) :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (get_first_digit n (Z.to_nat n)))
  in
  Z.of_nat (length (filter p nums)).

Example test_case: specialFilter [33%Z; 8%Z; -3%Z; 45%Z; 21%Z; -2%Z; 121%Z; 357%Z; 1892%Z; -2%Z] = 3%Z.
Proof.
  compute. reflexivity.
Qed.