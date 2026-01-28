Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; -200; 300; 0; 500; 300] 9 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 100).
    assert (HIn : In 100 [100; -200; 300; 0; 500; 300]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
  - intros H.
    discriminate.
Qed.