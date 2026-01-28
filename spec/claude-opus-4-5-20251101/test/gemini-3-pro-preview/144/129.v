Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_176_17_8_13 : simplify_spec 176 17 8 13 false.
Proof.
  unfold simplify_spec.
  split.
  - (* Prove x2 > 0 *)
    lia.
  - split.
    + (* Prove n2 > 0 *)
      lia.
    + (* Prove the equivalence *)
      split.
      * (* Left to Right: (176 * 8) mod (17 * 13) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate.
      * (* Right to Left: false = true -> (176 * 8) mod (17 * 13) = 0 *)
        intros H.
        discriminate.
Qed.