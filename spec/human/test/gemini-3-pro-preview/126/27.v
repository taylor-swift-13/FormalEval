Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example test_case : problem_126_spec [1; 0; 2; 3] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    inversion H as [| ? ? H_sorted H_hdrel]. subst.
    inversion H_hdrel as [| ? ? H_lt]. subst.
    inversion H_lt.
  - intros H.
    discriminate.
Qed.