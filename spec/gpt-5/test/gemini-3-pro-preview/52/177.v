Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [16.953176162073675; 2.9851560365316985] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* true = false is impossible *)
      discriminate H.
    + intros H.
      (* Forall (fun x => x < 1) ... -> False *)
      inversion H; subst.
      (* H2 : 16.95... < 1, which is false *)
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* We need to show exists x, In x l /\ 1 <= x *)
      exists 16.953176162073675.
      split.
      * simpl. left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.