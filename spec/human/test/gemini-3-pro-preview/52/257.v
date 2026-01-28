Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 6000001; -30; 40; -50] 13 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 6000001).
    assert (In 6000001 [10; 6000001; -30; 40; -50]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
  - intros H.
    discriminate.
Qed.