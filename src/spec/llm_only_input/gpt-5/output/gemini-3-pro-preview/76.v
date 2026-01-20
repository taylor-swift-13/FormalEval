Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example is_simple_power_spec_16_2_true :
  is_simple_power_spec 16%Z 2%Z true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _. exists 4%Z. split; [lia|].
    vm_compute. reflexivity.
  - intros _. reflexivity.
Qed.