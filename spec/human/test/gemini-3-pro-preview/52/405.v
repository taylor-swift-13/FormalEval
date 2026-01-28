Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10000000; 9000000; 8000000; 2000; 6000000; 100; 8000000] (-50) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show that the hypothesis implies False (since output is false) *)
    (* We pick a counter-example from the list: 10000000 *)
    specialize (H 10000000).
    assert (In 10000000 [10000000; 9000000; 8000000; 2000; 6000000; 100; 8000000]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    inversion H.
Qed.