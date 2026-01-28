Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; -200; 300; -400; 500] 1 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We derive a contradiction by showing an element in the list is not < 1 *)
    assert (100 < 1).
    {
      apply H.
      simpl.
      left.
      reflexivity.
    }
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.