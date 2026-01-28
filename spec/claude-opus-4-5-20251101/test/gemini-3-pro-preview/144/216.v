Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_8_3_468_6 : simplify_spec 8 3 468 6 true.
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
      * (* Left to Right: (8 * 468) mod (3 * 6) = 0 -> true = true *)
        intros H.
        reflexivity.
      * (* Right to Left: true = true -> (8 * 468) mod (3 * 6) = 0 *)
        intros H.
        vm_compute.
        reflexivity.
Qed.