Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_8577_2921_8577_291 : simplify_spec 8577 2921 8577 291 false.
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
      * (* Left to Right: (8577 * 8577) mod (2921 * 291) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate.
      * (* Right to Left: false = true -> (8577 * 8577) mod (2921 * 291) = 0 *)
        intros H.
        discriminate.
Qed.