Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example test_case : problem_126_spec [3; 3; 3; 3; 2; 2; 2; 2; 1; 1] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    inversion H as [| ? ? Htail Hrel]; subst.
    inversion Hrel as [| ? ? Hlt]; subst.
    apply Nat.lt_irrefl in Hlt.
    contradiction.
  - intros H.
    discriminate.
Qed.