Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux 100 (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter (fun n => 
    (n >? 10) && 
    (Z.odd (first_digit n)) && 
    (Z.odd (n mod 10))
  ) nums)).

Example test_specialFilter: specialFilter [100; 101; 505; 83; 102] = 2.
Proof.
  reflexivity.
Qed.