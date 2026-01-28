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
  [1; -5; -4; 0; 2.5; 6.8; 9; 3.5; 3.5; 3.5] 
  [-5; -8; 0; 10; 34; 54; 24.5; 28; 31.5].
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
                 --- destruct i as [|i].
                     +++ simpl. lra.
                     +++ destruct i as [|i].
                        *** simpl. lra.
                        *** destruct i as [|i].
                            ---- simpl. lra.
                            ---- lia.
Qed.