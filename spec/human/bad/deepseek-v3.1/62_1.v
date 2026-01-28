Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat), (i < length ys)%nat -> 
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

Example derivative_example : 
  problem_62_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold problem_62_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i as [|i]; [simpl; reflexivity|].
    destruct i as [|i]; [simpl; reflexivity|].
    destruct i as [|i]; [simpl; reflexivity|].
    destruct i as [|i]; [simpl; reflexivity|].
    simpl in H.
    inversion H.
Qed.