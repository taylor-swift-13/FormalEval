Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_example : problem_126_spec [3; 2; 1] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    inversion H. subst.
    inversion H2. subst.
    inversion H5. subst.
    lia.
  - intros H. discriminate.
Qed.