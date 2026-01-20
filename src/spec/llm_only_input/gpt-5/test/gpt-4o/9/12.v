Require Import List.
Require Import ZArith.
Require Import Lia.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example rolling_max_spec_increasing_decreasing :
  rolling_max_spec
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z]
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold rolling_max_spec.
  split.
  simpl. reflexivity.
  intros i Hi.
  destruct i as [|i1].
  vm_compute. reflexivity.
  destruct i1 as [|i2].
  vm_compute. reflexivity.
  destruct i2 as [|i3].
  vm_compute. reflexivity.
  destruct i3 as [|i4].
  vm_compute. reflexivity.
  destruct i4 as [|i5].
  vm_compute. reflexivity.
  destruct i5 as [|i6].
  vm_compute. reflexivity.
  destruct i6 as [|i7].
  vm_compute. reflexivity.
  destruct i7 as [|i8].
  vm_compute. reflexivity.
  destruct i8 as [|i9].
  vm_compute. reflexivity.
  simpl in Hi. exfalso. lia.
Qed.