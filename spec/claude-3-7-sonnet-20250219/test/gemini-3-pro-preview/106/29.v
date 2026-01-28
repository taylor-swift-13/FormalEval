Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial (k : nat) : Z :=
  match k with
  | 0%nat => 1
  | S k' => (Z.of_nat k) * factorial k'
  end.

Fixpoint sum_1_to_i (i : nat) : Z :=
  match i with
  | 0%nat => 0
  | S i' => (Z.of_nat i) + sum_1_to_i i'
  end.

Definition f_spec (n : Z) (l : list Z) : Prop :=
  Z.of_nat (length l) = n /\
  (forall i : Z, 1 <= i <= n ->
    nth (Z.to_nat (i - 1)) l 0 = 
      if Z.even i then factorial (Z.to_nat i) else sum_1_to_i (Z.to_nat i)).

Example test_case : f_spec 16 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    assert (H_eq: i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
    destruct H_eq as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]];
    vm_compute; reflexivity.
Qed.