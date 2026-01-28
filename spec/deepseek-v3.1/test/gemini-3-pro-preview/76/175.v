Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 16777216 16777216 true.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: true = true -> exists k, 0 <= k /\ 16777216 ^ k = 16777216 *)
  - intros _.
    (* We need to provide the witness k. Since 16777216^1 = 16777216, we use 1. *)
    exists 1.
    split.
    + (* Prove 0 <= 1 *)
      lia.
    + (* Prove 16777216 ^ 1 = 16777216 *)
      simpl.
      reflexivity.

  (* Subgoal 2: (exists k, ...) -> true = true *)
  - intros _.
    reflexivity.
Qed.