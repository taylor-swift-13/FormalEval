Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [2000000; 10000000; 9000000; 8000000; 6000000; 2000000; 7999999] 200 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication: (forall x, In x l -> x < t) -> false *)
    intros H.
    (* We exhibit a counter-example from the list: 2000000 *)
    assert (2000000 < 200).
    { apply H. simpl. left. reflexivity. }
    lia.
  - (* Right to Left implication: false -> ... *)
    intros H.
    inversion H.
Qed.