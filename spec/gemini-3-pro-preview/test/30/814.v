Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_pos : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys)
| gp_neg : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec 
  [-2.651030586877352; -4; 2.5; 5; -2.651030586877352; -8; 8.193677988449515; 7.7; 9.9; -10.5; -0.42322814636615796; -2.2] 
  [2.5; 5; 8.193677988449515; 7.7; 9.9].
Proof.
  unfold get_positive_spec.
  repeat constructor; lra.
Qed.