Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_62_pre (xs : list Z) : Prop := True.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat),
    (i < length ys)%nat ->
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

Example problem_62_test_case :
  problem_62_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 10%Z] [0%Z; 0%Z; 0%Z; 0%Z; 50%Z].
Proof.
  unfold problem_62_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i1]; simpl.
    + reflexivity.
    + destruct i1 as [|i2]; simpl.
      * reflexivity.
      * destruct i2 as [|i3]; simpl.
        -- reflexivity.
        -- destruct i3 as [|i4]; simpl.
           ++ reflexivity.
           ++ destruct i4 as [|i5]; simpl.
              ** reflexivity.
              ** exfalso. simpl in Hi. lia.
Qed.