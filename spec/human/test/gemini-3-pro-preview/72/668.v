Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

(* will_it_fly 函数的程序规约*)
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [1; 2; 3; 4; 5; 6] 7 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Backward direction: ... -> false = true *)
    intros [H1 H2].
    (* H1 states that [1; 2; 3; 4; 5; 6] = [6; 5; 4; 3; 2; 1], which is false *)
    inversion H1.
Qed.