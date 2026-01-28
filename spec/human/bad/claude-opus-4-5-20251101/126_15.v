Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_example : problem_126_spec [8; 7; 6; 5; 4; 3; 2; 1] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    exfalso.
    inversion H. subst.
    inversion H2. subst.
    inversion H5.
    lia.
  - intros H. discriminate.
Qed.