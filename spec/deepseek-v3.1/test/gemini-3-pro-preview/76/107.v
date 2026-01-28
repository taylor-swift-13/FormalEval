Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 16777216 4 true.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: true = true -> exists k, 0 <= k /\ 4 ^ k = 16777216 *)
  - intros _.
    (* We need to provide the witness k. Since 4^12 = 16777216, we use 12. *)
    exists 12.
    split.
    + (* Prove 0 <= 12 *)
      lia.
    + (* Prove 4 ^ 12 = 16777216 *)
      vm_compute. (* Computes the exponentiation *)
      reflexivity.

  (* Subgoal 2: (exists k, ...) -> true = true *)
  - intros _.
    reflexivity.
Qed.