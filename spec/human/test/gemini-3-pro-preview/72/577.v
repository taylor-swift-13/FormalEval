Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [0; 1; 2; 5; 1; 31; 3; 2; 1; 31; 2] 8 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [H _]. inversion H.
Qed.