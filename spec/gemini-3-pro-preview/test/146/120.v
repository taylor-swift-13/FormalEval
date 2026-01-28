Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    if n >? 10 then
      let f := first_digit n 100 in
      let l := n mod 10 in
      andb (Z.odd f) (Z.odd l)
    else
      false
  in Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [11; -12; 93; -125; 121; 109; -125] = 4.
Proof.
  compute. reflexivity.
Qed.