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
  problem_52_spec [1%Z; 3%Z; 7%Z; 5%Z] (-3)%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 1%Z).
    assert (In 1%Z [1%Z; 3%Z; 7%Z; 5%Z]) as Hin by (simpl; left; reflexivity).
    specialize (H Hin).
    exfalso.
    lia.
  - intros Heq.
    intros x HIn.
    exfalso.
    discriminate Heq.
Qed.