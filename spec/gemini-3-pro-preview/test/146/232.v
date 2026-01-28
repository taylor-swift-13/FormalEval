Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition first_digit (n : Z) : Z :=
  let fix loop (x : Z) (fuel : nat) : Z :=
    match fuel with
    | O => 0
    | S f => if x <? 10 then x else loop (x / 10) f
    end
  in loop n 100%nat.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (first_digit n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [100; 102; 103; 103; 103] = 3.
Proof. reflexivity. Qed.