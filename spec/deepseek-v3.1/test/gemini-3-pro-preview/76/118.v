Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2188 2189 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    (* false = true is a contradiction *)
    discriminate.
  - intros [k [Hk_nonneg Hk_eq]].
    (* We have 2189 ^ k = 2188 with 0 <= k *)
    assert (k = 0 \/ 1 <= k) as [Hk0 | Hk1] by lia.
    + (* Case k = 0 *)
      subst k.
      simpl in Hk_eq.
      (* 1 = 2188 is false *)
      discriminate.
    + (* Case k >= 1 *)
      (* Since 2189 > 0 and 1 <= k, we use monotonicity of exponentiation *)
      assert (2189 ^ 1 <= 2189 ^ k) as H_ineq.
      {
        apply Z.pow_le_mono_r; lia.
      }
      simpl in H_ineq.
      (* We have 2189 <= 2189^k. But 2189^k = 2188.
         So 2189 <= 2188, which is a contradiction. *)
      lia.
Qed.