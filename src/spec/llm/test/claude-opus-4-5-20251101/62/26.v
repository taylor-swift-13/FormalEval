Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example derivative_test : derivative_spec [0%Z; 0%Z; 6%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 7%Z; 0%Z; 0%Z; 0%Z; 8%Z; 0%Z] [0%Z; 12%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 8%Z; 63%Z; 0%Z; 0%Z; 0%Z; 104%Z; 0%Z].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [|i']; [simpl; reflexivity|].
    destruct i' as [|i'']; [simpl; reflexivity|].
    destruct i'' as [|i''']; [simpl; reflexivity|].
    destruct i''' as [|i'''']; [simpl; reflexivity|].
    destruct i'''' as [|i5]; [simpl; reflexivity|].
    destruct i5 as [|i6]; [simpl; reflexivity|].
    destruct i6 as [|i7]; [simpl; reflexivity|].
    destruct i7 as [|i8]; [simpl; reflexivity|].
    destruct i8 as [|i9]; [simpl; reflexivity|].
    destruct i9 as [|i10]; [simpl; reflexivity|].
    destruct i10 as [|i11]; [simpl; reflexivity|].
    destruct i11 as [|i12]; [simpl; reflexivity|].
    destruct i12 as [|i13]; [simpl; reflexivity|].
    destruct i13 as [|i14]; [simpl; reflexivity|].
    simpl in Hi. lia.
Qed.