Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := first_digit_aux n 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      andb (Z.odd (n mod 10)) (Z.odd (first_digit n))
    else
      false
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [789; 93; -125; 121; 109; 10; -125; 11; 10] = 5.
Proof.
  vm_compute. reflexivity.
Qed.