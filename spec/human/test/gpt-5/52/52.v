Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [(if true then 1%Z else 0%Z); (if false then 1%Z else 0%Z); (if false then 1%Z else 0%Z)] (-4%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hin: In 1%Z [(if true then 1%Z else 0%Z); (if false then 1%Z else 0%Z); (if false then 1%Z else 0%Z)]).
    { simpl. left. reflexivity. }
    specialize (H 1%Z Hin).
    lia.
  - intros Hout.
    intros x HIn.
    exfalso.
    discriminate Hout.
Qed.