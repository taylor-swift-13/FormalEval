Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [-25; 0; -40; 1; 0; 64; 0; 5; 63; 0] [0; -80; 3; 0; 320; 0; 35; 504; 0].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i Hi.
    (* We iterate destruct to handle each index 0 to 8 individually. *)
    (* Using vm_compute is faster than simpl for arithmetic verification. *)
    do 9 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    (* For i >= 9, the length condition Hi provides a contradiction. *)
    simpl in Hi. lia.
Qed.