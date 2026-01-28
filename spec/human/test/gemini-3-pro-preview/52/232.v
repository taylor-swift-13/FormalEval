Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-200; 10; 20; -30; 40; 8000000; -50] 8000000 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (8000000 < 8000000).
    {
      apply H.
      simpl.
      right; right; right; right; right; left.
      reflexivity.
    }
    lia.
  - intros H.
    discriminate H.
Qed.