Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example simplify_spec_example_1 : simplify_spec 1 5 5 1 true.
Proof.
  unfold simplify_spec.
  split.
  - lia.
  - split.
    + lia.
    + assert (Hmod : (1 * 5) mod (5 * 1) = 0) by (vm_compute; reflexivity).
      split.
      * intros _. reflexivity.
      * intros _. exact Hmod.
Qed.