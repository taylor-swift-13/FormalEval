Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [5.5; 7.9] (-199) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show that the hypothesis H implies False (since output is false) *)
    (* Instantiate H with an element that violates the condition *)
    assert (HIn : In 5.5 [5.5; 7.9]).
    { simpl. left. reflexivity. }
    specialize (H 5.5 HIn).
    (* 5.5 < -199 is false *)
    lra.
  - (* Right to Left implication *)
    intros H.
    (* H is false = true *)
    discriminate.
Qed.