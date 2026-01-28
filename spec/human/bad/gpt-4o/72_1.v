Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example problem_72_example : 
  problem_72_spec [3%Z; 2%Z; 3%Z] 9%Z true.
Proof.
  unfold problem_72_spec.
  split.
  - intros H.
    split.
    + reflexivity.
    + simpl.
      lia.
  - intros [H1 H2].
    simpl in H2.
    rewrite H1.
    reflexivity.
Qed.