Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative : derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold derivative_spec.
  split.
  - (* Check length condition *)
    simpl. reflexivity.
  - (* Check element-wise condition *)
    intros i Hi.
    simpl in Hi.
    (* Perform case analysis on the index i *)
    destruct i.
    + (* i = 0 *)
      simpl. reflexivity.
    + destruct i.
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ (* i >= 4, which contradicts Hi *)
              lia.
Qed.