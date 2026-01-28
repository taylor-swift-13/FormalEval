Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

(* will_it_fly 函数的程序规约*)
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [1; 2; 3; 8; 2; 1; 0; 1] 7 false.
Proof.
  unfold problem_72_spec.
  simpl.
  split.
  - intros H.
    inversion H.
  - intros [Hpal Hsum].
    (* The sum is 18, and 18 <= 7 is false. *)
    lia.
Qed.