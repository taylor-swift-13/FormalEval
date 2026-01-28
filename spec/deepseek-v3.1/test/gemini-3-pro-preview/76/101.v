Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 7 25 false.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: false = true -> exists k, ... *)
  - intros H.
    (* The premise false = true is contradictory *)
    discriminate.

  (* Subgoal 2: (exists k, ...) -> false = true *)
  - intros [k [Hk_nonneg Hk_eq]].
    (* We need to derive a contradiction from 25^k = 7 *)
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_neq0].
    + (* Case k = 0 *)
      subst.
      simpl in Hk_eq. (* 25^0 = 1 *)
      (* 1 = 7 is false *)
      discriminate.
    + (* Case k > 0, which implies k >= 1 since k is integer *)
      assert (Hk_ge_1 : k >= 1) by lia.
      (* Since base 25 > 0, the power function is monotonic. 25^k >= 25^1 *)
      assert (Hpow : 25 ^ 1 <= 25 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow. (* 25 <= 25^k *)
      (* Contradiction: 25 <= 25^k = 7 implies 25 <= 7 *)
      lia.
Qed.