Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 :
  problem_72_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 20%Z false.
Proof.
  unfold problem_72_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [Hrev Hsum]. exfalso. simpl in Hsum. lia.
Qed.