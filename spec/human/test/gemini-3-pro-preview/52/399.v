Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [30; 97; 90; -200; 59] 0 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 30).
    simpl in H.
    assert (30 < 0).
    { apply H. left. reflexivity. }
    lia.
  - intros H.
    discriminate.
Qed.