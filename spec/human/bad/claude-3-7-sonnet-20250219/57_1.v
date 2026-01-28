Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  (b = true) <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic_1 :
  problem_57_spec [1%Z; 2%Z; 4%Z; 10%Z] true.
Proof.
  unfold problem_57_spec.
  split; intros H.
  - (* -> direction *)
    rewrite H.
    left.
    (* Prove Sorted Z.le for [1;2;4;10] *)
    repeat constructor; lia.
  - (* <- direction *)
    destruct H as [Hle | Hge].
    + reflexivity.
    + reflexivity.
Qed.