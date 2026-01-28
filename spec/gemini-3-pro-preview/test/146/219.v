Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => 
      if n <? 10 then n 
      else first_digit_aux (n / 10) f
  end.

Definition first_digit (n : Z) : Z := first_digit_aux (Z.abs n) 100%nat.

Definition is_odd_digit (n : Z) : bool :=
  n mod 2 =? 1.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := 
    (x >? 10) && 
    (is_odd_digit (x mod 10)) && 
    (is_odd_digit (first_digit x)) 
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: 
  specialFilter [120; 122; 13; 4; 615; 8518; 21517; 2123; 918] = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.