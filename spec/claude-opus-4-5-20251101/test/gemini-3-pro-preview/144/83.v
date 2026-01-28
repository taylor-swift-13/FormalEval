Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_1112_9_1112_9 : simplify_spec 1112 9 1112 9 false.
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
      * (* Left to Right: (1112 * 1112) mod (9 * 9) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        inversion H.
      * (* Right to Left: false = true -> (1112 * 1112) mod (9 * 9) = 0 *)
        intros H.
        discriminate.
Qed.