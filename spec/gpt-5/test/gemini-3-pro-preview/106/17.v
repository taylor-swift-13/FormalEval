Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S k => (Z.of_nat n) * factorial k
  end.

Fixpoint sum_upto (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S k => sum_upto k + Z.of_nat n
  end.

Definition f_spec (n : nat) (ans : list Z) : Prop :=
  length ans = n /\
  forall i, (1 <= i <= n)%nat ->
    nth_error ans (i - 1)%nat = Some (if Nat.even i then factorial i else sum_upto i).

Example test_case_1 : f_spec 19%nat [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [Hge Hle].
    destruct i; [ inversion Hge | ].
    do 19 (destruct i; [ simpl; reflexivity | ]).
    exfalso.
    do 19 apply le_S_n in Hle.
    inversion Hle.
Qed.