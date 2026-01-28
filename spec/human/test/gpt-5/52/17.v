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
  problem_52_spec [1%Z; 3%Z; 4%Z] 4%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros Hall.
    specialize (Hall 4%Z).
    assert (In 4%Z [1%Z; 3%Z; 4%Z]) as Hin by (simpl; right; right; left; reflexivity).
    specialize (Hall Hin).
    exfalso.
    apply (Z.lt_irrefl 4%Z).
    exact Hall.
  - intros H.
    intros x HIn.
    exfalso.
    discriminate H.
Qed.