Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_11_9_911_9 : simplify_spec 11 9 911 9 false.
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
      * (* Left to Right: (11 * 911) mod (9 * 9) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate.
      * (* Right to Left: false = true -> (11 * 911) mod (9 * 9) = 0 *)
        intros H.
        discriminate.
Qed.