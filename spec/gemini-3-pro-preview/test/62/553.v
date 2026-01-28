Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec 
  [3.6845190419876506; 6.8; 3.4009590491925366; 1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -24; 3.5; 0] 
  [6.8; 6.8019180983850732; 5.6584754124329586; 14; -14; 6.6; -30.8; -36; -216; 35; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    (* We iterate through the specific indices 0 to 10 *)
    do 11 (destruct i; [simpl; lra | ]).
    (* i >= 11 contradicts H : i < 11 *)
    lia.
Qed.