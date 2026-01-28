Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | S k => (Z.of_nat (S k) * factorial k)%Z
  end.

Fixpoint sum_upto (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | S k => (sum_upto k + Z.of_nat (S k))%Z
  end.

Definition f_spec (n : nat) (ans : list Z) : Prop :=
  length ans = n /\
  forall i, 1 <= i <= n ->
    nth_error ans (i - 1) = Some (if Nat.even i then factorial i else sum_upto i).

Example test_case_1 : f_spec 14 [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [Hge Hle].
    destruct i as [|i]; [ inversion Hge | ].
    do 14 (destruct i as [|i]; [ simpl; reflexivity | ]).
    exfalso.
    do 14 (apply le_S_n in Hle).
    inversion Hle.
Qed.