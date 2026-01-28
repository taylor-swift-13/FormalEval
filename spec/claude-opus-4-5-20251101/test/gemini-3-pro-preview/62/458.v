Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec 
  [1; 0; 0; -1; 0; 0; 1; 0; 0; -5; 0; 0; 63; 0; -7; 0; 10; 0; 1; 0]
  [0; 0; -3; 0; 0; 6; 0; 0; -45; 0; 0; 756; 0; -98; 0; 160; 0; 18; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    (* We iterate destruct 19 times to cover indices 0 to 18.
       vm_compute is efficient for checking the arithmetic equality for each case. *)
    do 19 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    (* The remaining case i >= 19 contradicts the hypothesis Hi (i < 19) *)
    simpl in Hi. lia.
Qed.