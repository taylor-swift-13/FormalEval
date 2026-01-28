Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; 200; 300] 0 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H implies that all elements are < 0. *)
    (* We show that 100 (the first element) is not < 0, leading to a contradiction. *)
    assert (100 < 0).
    { apply H. simpl. left. reflexivity. }
    lia.
  - (* Right to Left implication *)
    intros H.
    (* The hypothesis H is false = true, which is a contradiction. *)
    discriminate.
Qed.