Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10000000; 9000000; 10000001; 10; 8000000; 6000000; 2000000; 10000001] 0 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 10).
    assert (In 10 [10000000; 9000000; 10000001; 10; 8000000; 6000000; 2000000; 10000001]).
    { simpl. tauto. }
    apply H in H0.
    lia.
  - intros H.
    discriminate.
Qed.