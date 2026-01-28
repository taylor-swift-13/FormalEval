Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n 100.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (x mod 10)) in
  Z.of_nat (length (filter p nums)).

Example test_case: specialFilter [12%Z; 789%Z; 13%Z; 15%Z; 16%Z] = 3%Z.
Proof.
  vm_compute. reflexivity.
Qed.