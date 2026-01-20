Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial_nat (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S p => Z.of_nat n * factorial_nat p
  end.

Definition factorial (n : Z) : Z :=
  factorial_nat (Z.to_nat n).

Fixpoint sum_1_to_n_nat (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S p => Z.of_nat n + sum_1_to_n_nat p
  end.

Definition sum_1_to_n (n : Z) : Z :=
  sum_1_to_n_nat (Z.to_nat n).

Definition f_spec (n : nat) (result : list Z) : Prop :=
  length result = n /\
  (forall i : nat, (i < n)%nat ->
    let logical_index := Z.of_nat (i + 1) in
    let val := nth i result 0 in
    if Z.even logical_index then
      val = factorial logical_index
    else
      val = sum_1_to_n logical_index).

Example test_case_1 : f_spec 18 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    do 18 (destruct i as [|i]; [ simpl; reflexivity | ]).
    exfalso. do 18 apply lt_S_n in Hi. inversion Hi.
Qed.