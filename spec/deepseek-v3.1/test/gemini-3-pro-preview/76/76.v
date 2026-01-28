Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 82 true.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: true = true -> exists k, 0 <= k /\ 82 ^ k = 82 *)
  - intros _.
    (* We need to provide the witness k. Since 82^1 = 82, we use 1. *)
    exists 1.
    split.
    + (* Prove 0 <= 1 *)
      lia.
    + (* Prove 82 ^ 1 = 82 *)
      simpl. (* Computes the exponentiation *)
      reflexivity.

  (* Subgoal 2: (exists k, ...) -> true = true *)
  - intros _.
    reflexivity.
Qed.