Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [30; 14; 4; 4; 4; 4] 16 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [H1 H2]. inversion H1.
Qed.