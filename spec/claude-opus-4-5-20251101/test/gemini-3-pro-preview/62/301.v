Require Import List.
Require Import Reals.
Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec [1; -4; 0; 63; -4.5; -2.413995463147514; 6.8] [-4; 0; 189; -18; -12.06997731573757; 40.8].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [|i].
    + simpl. lra.
    + destruct i as [|i].
      * simpl. lra.
      * destruct i as [|i].
        -- simpl. lra.
        -- destruct i as [|i].
           ++ simpl. lra.
           ++ destruct i as [|i].
              ** simpl. lra.
              ** destruct i as [|i].
                 --- simpl. lra.
                 --- lia.
Qed.