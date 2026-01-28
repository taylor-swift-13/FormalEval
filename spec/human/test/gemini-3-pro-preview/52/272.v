Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1; 0; 1; 0; 0; 0; 1; 0; 1; 0] (-1) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (1 < -1).
    { apply H. simpl. left. reflexivity. }
    lia.
  - intros H.
    discriminate.
Qed.