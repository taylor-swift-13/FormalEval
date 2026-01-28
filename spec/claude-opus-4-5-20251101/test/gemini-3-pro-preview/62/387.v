Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 62; -2; -40; 0; 10; 0; 5] [-25; 124; -6; -160; 0; 60; 0; 40].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i Hi.
    simpl in Hi.
    (* Use 'do' to destruct exactly the number of elements in the result list (8) *)
    (* vm_compute is used for efficient arithmetic evaluation to avoid timeouts *)
    do 8 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    (* The remaining case is when i >= 8, which contradicts Hi *)
    lia.
Qed.