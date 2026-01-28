Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000] 9999998 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    specialize (H 10000000).
    assert (In 10000000 [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000]).
    { simpl. right. right. right. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.