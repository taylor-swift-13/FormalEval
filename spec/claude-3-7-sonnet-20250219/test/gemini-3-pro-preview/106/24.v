Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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
  (forall i : nat, 1 <= Z.of_nat i <= n ->
    nth (i-1) l 0 = 
      if Nat.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 21 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190; 2432902008176640000; 231].
Proof.
  unfold f_spec.
  split.
  - (* Check length *)
    simpl. reflexivity.
  - (* Check elements *)
    intros i Hi.
    (* Use repeated destruct to handle each index 1 to 21 individually.
       We do 22 iterations: 
       - 1 for i=0 (eliminated by lia)
       - 21 for i=1..21 (checked by computation)
       The remaining goal covers i >= 22 (eliminated by lia). 
       Using vm_compute is essential for performance with large Z values. *)
    do 22 (destruct i; [ try lia; try (vm_compute; reflexivity) | ]).
    (* Remaining case: i >= 22 *)
    lia.
Qed.