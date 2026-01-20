Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_aux : list R -> list R -> Prop :=
| GP_nil : get_positive_aux [] []
| GP_pos : forall x xs ys, x > 0 -> get_positive_aux xs ys -> get_positive_aux (x :: xs) (x :: ys)
| GP_neg : forall x xs ys, x <= 0 -> get_positive_aux xs ys -> get_positive_aux (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_aux l res.

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -11.18889279027017; -8; -4; -7; 9.9; -11.18889279027017; -10.5] 
  [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  repeat (constructor; try lra).
Qed.