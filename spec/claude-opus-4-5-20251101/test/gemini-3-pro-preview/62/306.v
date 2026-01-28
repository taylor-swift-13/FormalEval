Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [-3; -26; -1; 63; -40; 0; 10; -8; -26; -1; -40] [-26; -2; 189; -160; 0; 60; -56; -208; -9; -400].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 10 (destruct i as [|i]; [simpl; reflexivity|]).
    lia.
Qed.