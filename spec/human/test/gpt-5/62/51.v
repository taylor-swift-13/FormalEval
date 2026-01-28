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
  problem_62_spec
    [6%Z; 0%Z; 0%Z; 0%Z; 6%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 7%Z; 0%Z; 0%Z; 0%Z; 8%Z; 0%Z]
    [0%Z; 0%Z; 0%Z; 24%Z; 0%Z; 0%Z; 0%Z; 0%Z; 9%Z; 70%Z; 0%Z; 0%Z; 0%Z; 112%Z; 0%Z].
Proof.
  unfold problem_62_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i1]; simpl; try reflexivity.
    destruct i1 as [|i2]; simpl; try reflexivity.
    destruct i2 as [|i3]; simpl; try reflexivity.
    destruct i3 as [|i4]; simpl; try reflexivity.
    destruct i4 as [|i5]; simpl; try reflexivity.
    destruct i5 as [|i6]; simpl; try reflexivity.
    destruct i6 as [|i7]; simpl; try reflexivity.
    destruct i7 as [|i8]; simpl; try reflexivity.
    destruct i8 as [|i9]; simpl; try reflexivity.
    destruct i9 as [|i10]; simpl; try reflexivity.
    destruct i10 as [|i11]; simpl; try reflexivity.
    destruct i11 as [|i12]; simpl; try reflexivity.
    destruct i12 as [|i13]; simpl; try reflexivity.
    destruct i13 as [|i14]; simpl; try reflexivity.
    destruct i14 as [|i15]; simpl; try reflexivity.
    exfalso. simpl in Hi. lia.
Qed.