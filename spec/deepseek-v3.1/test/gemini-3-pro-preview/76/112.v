Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 245 5 false.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: false = true -> exists k, ... *)
  - intros H.
    discriminate.

  (* Subgoal 2: (exists k, ...) -> false = true *)
  - intros [k [Hk_nonneg Hk_eq]].
    (* We check cases based on the value of k *)
    assert (H_cases: k < 4 \/ k >= 4) by lia.
    destruct H_cases as [H_small | H_large].
    + (* Case k < 4: k can be 0, 1, 2, or 3 *)
      assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [? | [? | [? | ?]]]; subst k; simpl in Hk_eq; discriminate.
    + (* Case k >= 4: 5^k >= 625 > 245 *)
      assert (H_mono: 5 ^ 4 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      lia.
Qed.