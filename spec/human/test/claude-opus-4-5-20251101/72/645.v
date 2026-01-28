Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [1%Z; 8%Z; 2%Z; 3%Z; 2%Z; 1%Z; 3%Z; 2%Z; 1%Z; 2%Z; 3%Z; 2%Z; 1%Z] 6%Z false.
Proof.
  unfold problem_72_spec.
  split.
  - intros H. discriminate H.
  - intros [H1 H2].
    simpl in H1.
    discriminate H1.
Qed.