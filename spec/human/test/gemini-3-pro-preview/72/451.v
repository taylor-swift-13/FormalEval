Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

(* will_it_fly 函数的程序规约*)
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [1; 2; 3; 2; 1; 0; 1; 0; 2; 2] 20 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros [H_pal _].
    discriminate H_pal.
Qed.