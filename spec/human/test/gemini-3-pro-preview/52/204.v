Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-200; 300; 8000000; -400; -600; 300] 1001 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    assert (In 8000000 [-200; 300; 8000000; -400; -600; 300]) as HIn.
    { simpl. right. right. left. reflexivity. }
    specialize (H 8000000 HIn).
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.