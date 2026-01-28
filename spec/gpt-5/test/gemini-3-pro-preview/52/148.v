Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [62.5; 16.953176162073675; 2.9851560365316985; 16.953176162073675] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      assert (In 62.5 [62.5; 16.953176162073675; 2.9851560365316985; 16.953176162073675]).
      { left. reflexivity. }
      specialize (H _ H0).
      lra.
  - split.
    + intros _.
      exists 62.5.
      split.
      * left. reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.