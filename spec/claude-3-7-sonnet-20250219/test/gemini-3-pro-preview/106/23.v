Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint fact_nat (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S n' => Z.of_nat n * fact_nat n'
  end.

Definition factorial (n : Z) : Z := fact_nat (Z.to_nat n).

Definition sum_1_to_i (n : Z) : Z := n * (n + 1) / 2.

Definition f_spec (n : Z) (l : list Z) : Prop :=
  Z.of_nat (length l) = n /\
  (forall i, 1 <= i <= n ->
    nth (Z.to_nat (i-1)) l 0 = 
      if Z.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 18 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    assert (H_cases: i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18) by lia.
    destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]];
      vm_compute; reflexivity.
Qed.