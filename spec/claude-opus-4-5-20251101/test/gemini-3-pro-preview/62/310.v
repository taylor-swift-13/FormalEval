Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec 
  [1; -4; 0; 63; -45/10; -2413995463147514 / 10^15; 34009590491925366 / 10^16] 
  [-4; 0; 189; -18; 5 * (-2413995463147514 / 10^15); 6 * (34009590491925366 / 10^16)].
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