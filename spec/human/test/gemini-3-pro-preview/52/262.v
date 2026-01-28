Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; 9999999; -400; 19] 8000001 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H claims all elements are less than the threshold.
       We show a contradiction by picking an element that violates this. *)
    assert (C : In 9999999 [100; 9999999; -400; 19]).
    { simpl. right. left. reflexivity. }
    specialize (H 9999999 C).
    lia.
  - (* Right to Left implication *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
Qed.