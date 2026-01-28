Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  exists f : R -> bool,
    (forall x, f x = true <-> x > 0) /\
    res = filter f l.

Example test_get_positive : get_positive_spec [9.9; 33.195768044846155; -2.25] [9.9; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  exists (fun x => if Rgt_dec x 0 then true else false).
  split.
  - intro x. destruct (Rgt_dec x 0); split; intro H; try lra; try discriminate; auto.
  - simpl.
    destruct (Rgt_dec 9.9 0); [| lra].
    destruct (Rgt_dec 33.195768044846155 0); [| lra].
    destruct (Rgt_dec (-2.25) 0); [lra |].
    reflexivity.
Qed.