Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10000001; -200; 300; -400; 500; -600] 1999 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 10000001).
    assert (In 10000001 [10000001; -200; 300; -400; 500; -600]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
  - intros H.
    discriminate.
Qed.