Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    (n >? 10) && 
    (Z.odd (n mod 10)) && 
    (Z.odd (get_first_digit n 100))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [-12%Z; 93%Z; -125%Z; 1111%Z; 109%Z] = 3%Z.
Proof. reflexivity. Qed.