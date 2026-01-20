Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition specialFilter (nums : list Z) : Z :=
  let fix get_first_digit (fuel : nat) (n : Z) : Z :=
    match fuel with
    | O => n
    | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
    end in
  let is_odd (n : Z) := Z.eqb (n mod 2) 1 in
  let predicate (n : Z) :=
    if n >? 10 then
      andb (is_odd (get_first_digit (Z.to_nat n) n)) (is_odd (n mod 10))
    else false in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [39%Z; 151%Z; 152%Z; 240%Z] = 2%Z.
Proof. reflexivity. Qed.