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
  problem_52_spec [1%Z; 4%Z; 7%Z; 10%Z; 7%Z] 6%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (H7 : 7%Z < 6%Z).
    { apply H. simpl. right. right. left. reflexivity. }
    exfalso. lia.
  - intros H.
    intros x HIn.
    exfalso. discriminate H.
Qed.