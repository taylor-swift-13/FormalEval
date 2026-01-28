Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition first_digit (n : Z) : Z :=
  get_first_digit n (Z.to_nat (Z.log2 n + 1)).

Definition last_digit (n : Z) : Z := n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) :=
    (x >? 10) && (Z.odd (first_digit x)) && (Z.odd (last_digit x)) in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter:
  specialFilter [120; 121; 122; 357; 8518; 21517; 100; 919] = 3.
Proof.
  vm_compute. reflexivity.
Qed.