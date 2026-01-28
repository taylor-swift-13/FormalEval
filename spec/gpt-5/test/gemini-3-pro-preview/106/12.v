Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial_aux (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S k => (Z.of_nat n) * factorial_aux k
  end.

Definition factorial (n : Z) : Z := factorial_aux (Z.to_nat n).

Fixpoint sum_upto_aux (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S k => sum_upto_aux k + Z.of_nat n
  end.

Definition sum_upto (n : Z) : Z := sum_upto_aux (Z.to_nat n).

Definition f_spec (n : Z) (ans : list Z) : Prop :=
  Z.of_nat (length ans) = n /\
  forall i, (1 <= i <= Z.to_nat n)%nat ->
    nth_error ans (i - 1)%nat = Some (if Nat.even i then factorial (Z.of_nat i) else sum_upto (Z.of_nat i)).

Example test_case_1 : f_spec 15 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120].
Proof.
  unfold f_spec.
  split.
  - reflexivity.
  - intros i [Hge Hle].
    destruct i; [ inversion Hge | ].
    do 15 (destruct i; [ simpl; reflexivity | ]).
    exfalso.
    do 15 (apply le_S_n in Hle).
    inversion Hle.
Qed.