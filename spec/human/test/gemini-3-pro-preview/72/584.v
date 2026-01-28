Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

(* will_it_fly 函数的程序规约*)
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [1; 3; 5; 7; 4; 9; 7; 5; 3; 1; 1; 4] (-1) false.
Proof.
  unfold problem_72_spec.
  split.
  - intros H.
    inversion H.
  - intros [Hpal Hsum].
    simpl in Hsum.
    lia.
Qed.