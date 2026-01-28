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
  problem_52_spec [10%Z; 20%Z; -30%Z; 40%Z; -50%Z] 15%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll.
    exfalso.
    assert (H20: 20%Z < 15%Z).
    { apply HAll.
      simpl. right. left. reflexivity. }
    lia.
  - intros H.
    intros x HIn.
    exfalso.
    discriminate H.
Qed.