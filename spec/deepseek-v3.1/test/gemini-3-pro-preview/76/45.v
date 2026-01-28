Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 21 35 false.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: false = true -> exists k, ... *)
  - intros H.
    discriminate.

  (* Subgoal 2: (exists k, ...) -> false = true *)
  - intros [k [Hk1 Hk2]].
    (* We proceed by cases on k *)
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk_ge_1] by lia.
    + (* Case k = 0 *)
      subst k.
      simpl in Hk2.
      (* 1 = 21 is false *)
      lia.
    + (* Case k >= 1 *)
      (* Since the base 35 > 1, 35^k is increasing. 35^1 = 35 > 21. *)
      assert (35 ^ 1 <= 35 ^ k) as H_pow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      rewrite Hk2 in H_pow.
      (* We have 35 <= 21, which is a contradiction *)
      lia.
Qed.