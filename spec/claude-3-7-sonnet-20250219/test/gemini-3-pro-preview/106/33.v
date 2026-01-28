Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Fixpoint factorial (k : nat) : Z :=
  match k with
  | 0 => 1%Z
  | S k' => Z.mul (Z.of_nat k) (factorial k')
  end.

Fixpoint sum_1_to_i (i : nat) : Z :=
  match i with
  | 0 => 0%Z
  | S i' => Z.add (Z.of_nat i) (sum_1_to_i i')
  end.

Definition f_spec (n : nat) (l : list Z) : Prop :=
  length l = n /\
  (forall i, 1 <= i <= n ->
    nth (i-1) l 0%Z = 
      if Nat.even i then factorial i else sum_1_to_i i).

Open Scope Z_scope.

Example test_case : f_spec 17%nat [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [Hmin Hmax].
    destruct i. { lia. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    lia.
Qed.