Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint fact_aux (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S k => (Z.of_nat (S k)) * fact_aux k
  end.

Fixpoint sum_upto_aux (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S k => sum_upto_aux k + Z.of_nat (S k)
  end.

Definition factorial (n : Z) : Z := fact_aux (Z.to_nat n).

Definition sum_upto (n : Z) : Z := sum_upto_aux (Z.to_nat n).

Definition f_spec (n : Z) (ans : list Z) : Prop :=
  length ans = Z.to_nat n /\
  forall i : nat, (1 <= i <= Z.to_nat n)%nat ->
    nth_error ans (i - 1)%nat = 
    Some (if Z.even (Z.of_nat i) then factorial (Z.of_nat i) else sum_upto (Z.of_nat i)).

Example test_case_1 : f_spec 18 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [Hge Hle].
    destruct i; [ lia | ].
    do 18 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in Hle. lia.
Qed.