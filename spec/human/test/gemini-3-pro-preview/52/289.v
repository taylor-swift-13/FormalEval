Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; 2000000; 300; -400; 500] (-1) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show False, derived from the hypothesis that all elements are < -1 *)
    (* We pick a counter-example from the list, e.g., 100 *)
    assert (100 < -1).
    {
      apply H.
      simpl.
      left.
      reflexivity.
    }
    lia.
  - (* Right to Left implication *)
    intros H.
    (* Hypothesis is false = true, which is contradictory *)
    discriminate H.
Qed.