Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [2; 4; 6; 8; 10; 14; 17; 17; 20; 12; 10] 4 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros [Hpal Hsum].
    lia.
Qed.