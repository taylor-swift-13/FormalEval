Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [6.4133956835438735; 7.9] (-200) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We must show a contradiction because output is false *)
    assert (In 6.4133956835438735 [6.4133956835438735; 7.9]).
    { simpl. left. reflexivity. }
    specialize (H _ H0).
    lra.
  - (* Right to Left implication *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
Qed.