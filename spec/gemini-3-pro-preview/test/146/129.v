Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let m := Z.to_nat n in
  let fix aux (k : nat) (fuel : nat) : nat :=
    match fuel with
    | 0%nat => 0%nat
    | S f => match (Nat.div k 10) with
             | 0%nat => k
             | k' => aux k' f
             end
    end
  in Z.of_nat (aux m m).

Definition solution (nums : list Z) : Z :=
  let p (x : Z) : bool :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (x mod 10))
  in
  Z.of_nat (length (filter p nums)).

Example test_case: solution [33; -2; -3; 45; 21; -2; 121; 357; 1892; -2] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.