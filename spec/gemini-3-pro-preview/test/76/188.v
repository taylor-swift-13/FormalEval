Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213696 65537 false.
Proof.
  unfold is_simple_power_spec.
  split; [intro H; discriminate |].
  intros [k [Hk Heq]].
  assert (H_low : 65537 ^ 4 < 4722366482869645213696) by (vm_compute; reflexivity).
  assert (H_high : 4722366482869645213696 < 65537 ^ 5) by (vm_compute; reflexivity).
  rewrite Heq in *.
  assert (H_cases : k <= 4 \/ 5 <= k) by lia.
  destruct H_cases as [Hle | Hge].
  - apply Z.pow_le_mono_r with (a:=65537) in Hle; try lia.
  - apply Z.pow_le_mono_r with (a:=65537) in Hge; try lia.
Qed.