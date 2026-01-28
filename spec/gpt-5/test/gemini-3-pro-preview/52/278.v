Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [5.5; 6.2; 7.9; 8.1; 6.2; 6.2] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      inversion H; subst.
      lra.
  - split.
    + intros _.
      exists 5.5.
      split.
      * simpl. left. reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.