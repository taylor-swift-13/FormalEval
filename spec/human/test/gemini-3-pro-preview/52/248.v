Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 20; -30; 0; 40; -50] 13 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (20 < 13).
    {
      apply H.
      simpl.
      right; left.
      reflexivity.
    }
    lia.
  - intros H.
    discriminate.
Qed.