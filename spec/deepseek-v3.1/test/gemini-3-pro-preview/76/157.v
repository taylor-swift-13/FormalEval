Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4722366482869645213695 4722366482869645213696 false.
Proof.
  (* Unfold the definition of the specification *)
  unfold is_simple_power_spec.

  (* Split the bi-implication <-> into two subgoals *)
  split.

  (* Subgoal 1: false = true -> ... *)
  - intros H.
    discriminate H.

  (* Subgoal 2: (exists k, ...) -> false = true *)
  - intros [k [Hk_nonneg Hk_eq]].
    (* We need to show a contradiction derived from n^k = x where n = x + 1 *)
    assert (k = 0 \/ k > 0) as [Hk0 | Hk_pos] by lia.
    
    + (* Case k = 0 *)
      subst k.
      simpl in Hk_eq.
      (* 1 = 4722366482869645213695 *)
      (* This is structurally false for distinct Z constants *)
      discriminate Hk_eq.

    + (* Case k > 0 *)
      (* Since k is integer, k >= 1 *)
      assert (Hk1 : 1 <= k) by lia.
      assert (Hn_pos : 0 < 4722366482869645213696) by reflexivity.
      
      (* Use monotonicity of power: n^1 <= n^k *)
      pose proof (Z.pow_le_mono_r 4722366482869645213696 1 k Hn_pos Hk1) as H_mono.
      
      (* Simplify n^1 *)
      replace (4722366482869645213696 ^ 1) with 4722366482869645213696 in H_mono by reflexivity.
      
      (* Substitute n^k = x *)
      rewrite Hk_eq in H_mono.
      
      (* We have n <= x, but we know n > x. Contradiction. *)
      assert (H_contra : 4722366482869645213696 > 4722366482869645213695) by reflexivity.
      lia.
Qed.