Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint fact_nat (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S k => (Z.of_nat n) * fact_nat k
  end.

Definition factorial (n : Z) : Z :=
  fact_nat (Z.to_nat n).

Definition sum_upto (n : Z) : Z :=
  (n * (n + 1)) / 2.

Definition f_spec (n : Z) (ans : list Z) : Prop :=
  Z.of_nat (length ans) = n /\
  forall i, 1 <= i <= n ->
    nth_error ans (Z.to_nat (i - 1)) = Some (if Z.even i then factorial i else sum_upto i).

Example test_case_1 : f_spec 21 [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z; 120%Z; 20922789888000%Z; 153%Z; 6402373705728000%Z; 190%Z; 2432902008176640000%Z; 231%Z].
Proof.
  unfold f_spec.
  split.
  - reflexivity.
  - intros i Hi.
    assert (H_idx: i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ 
                   i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21).
    { lia. }
    destruct H_idx as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]];
    vm_compute; reflexivity.
Qed.