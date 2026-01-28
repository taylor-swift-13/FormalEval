Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_15_17_112_9 : simplify_spec 15 17 112 9 false.
Proof.
  unfold simplify_spec.
  split.
  - (* Prove 17 > 0 *)
    lia.
  - split.
    + (* Prove 9 > 0 *)
      lia.
    + (* Prove the equivalence *)
      split.
      * (* Left to Right: (15 * 112) mod (17 * 9) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate H.
      * (* Right to Left: false = true -> (15 * 112) mod (17 * 9) = 0 *)
        intros H.
        discriminate H.
Qed.