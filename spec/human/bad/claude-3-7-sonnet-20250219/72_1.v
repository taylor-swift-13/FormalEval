Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_case_72 :
  problem_72_spec [3; 2; 3] 9 true.
Proof.
  unfold problem_72_spec.
  split.
  - intros H. subst output.
    split.
    + simpl. reflexivity.
    + simpl. lia.
  - intros [Hpal Hsum].
    subst output.
    reflexivity.
Qed.