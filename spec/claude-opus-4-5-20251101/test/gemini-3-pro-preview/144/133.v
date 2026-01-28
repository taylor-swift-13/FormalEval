Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_943_29_453_384 : simplify_spec 943 29 453 384 false.
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
      * (* Left to Right: (943 * 453) mod (29 * 384) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate H.
      * (* Right to Left: false = true -> (943 * 453) mod (29 * 384) = 0 *)
        intros H.
        discriminate H.
Qed.