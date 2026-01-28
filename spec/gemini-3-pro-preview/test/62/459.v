Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Floats.Floats.
Import ListNotations.
Open Scope float_scope.

Fixpoint nat_to_float (n : nat) : float :=
  match n with
  | O => 0.0
  | S p => 1.0 + (nat_to_float p)
  end.

Definition derivative_spec (xs : list float) (result : list float) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0.0 = (nth (S i) xs 0.0) * (nat_to_float (S i)).

Example test_derivative: derivative_spec 
  [1.0; -4.0; 0.0; 62.0; -4.5; -2.413995463147514; 3.4009590491925366] 
  [-4.0; 0.0; 186.0; -18.0; -12.069977315737571; 20.40575429515522].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i.
    + simpl. reflexivity.
    + destruct i.
      * simpl. reflexivity.
      * destruct i.
        -- simpl. reflexivity.
        -- destruct i.
           ++ simpl. reflexivity.
           ++ destruct i.
              ** simpl. reflexivity.
              ** destruct i.
                 *** simpl. reflexivity.
                 *** lia.
Qed.