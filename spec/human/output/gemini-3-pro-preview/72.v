Require Import List.
Require Import ZArith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop := True.

(* will_it_fly 函数的程序规约*)
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).

Example test_problem_72 : problem_72_spec [3; 2; 3] 9 true.
Proof.
  unfold problem_72_spec.
  (* Simplify the list operations: rev and fold_left *)
  simpl.
  (* The goal becomes: true = true <-> [3; 2; 3] = [3; 2; 3] /\ 8 <= 9 *)
  split.
  - (* Forward direction: true = true -> ... *)
    intros _.
    split.
    + (* Check palindrome property *)
      reflexivity.
    + (* Check sum property: 8 <= 9 *)
      lia.
  - (* Backward direction: ... -> true = true *)
    intros _.
    reflexivity.
Qed.