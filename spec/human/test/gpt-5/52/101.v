Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [100%Z; -200%Z; 300%Z; -400%Z; 500%Z; -600%Z] 100%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    apply (Z.lt_irrefl 100%Z).
    apply H.
    simpl; left; reflexivity.
  - intros H.
    intros x HIn.
    exfalso.
    discriminate H.
Qed.