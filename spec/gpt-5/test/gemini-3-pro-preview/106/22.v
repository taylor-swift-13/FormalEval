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

Example test_case_1 : f_spec 13%nat [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91].
Proof.
  unfold f_spec.
  split.
  - reflexivity.
  - intros i [Hge Hle].
    destruct i. inversion Hge.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    destruct i. vm_compute. reflexivity.
    exfalso. do 13 (apply le_S_n in Hle). inversion Hle.
Qed.