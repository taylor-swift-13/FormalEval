Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
    if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100.

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && 
    (Z.odd (get_first_digit n)) && 
    (Z.odd (get_last_digit n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [55%Z; -62%Z; 7%Z; 24%Z; 18%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.