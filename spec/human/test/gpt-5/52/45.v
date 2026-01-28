Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [0%Z; 0%Z; 2%Z; 0%Z; 0%Z] 1%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 2%Z).
    assert (In 2%Z [0%Z; 0%Z; 2%Z; 0%Z; 0%Z]) as Hin.
    { simpl. right. right. left. reflexivity. }
    specialize (H Hin).
    exfalso. lia.
  - intros Heq.
    intros x HIn.
    exfalso. discriminate Heq.
Qed.