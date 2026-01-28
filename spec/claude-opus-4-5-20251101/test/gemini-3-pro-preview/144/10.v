Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_2_4_8_4 : simplify_spec 2 4 8 4 true.
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
      * (* Left to Right: (2 * 8) mod (4 * 4) = 0 -> true = true *)
        intros H.
        reflexivity.
      * (* Right to Left: true = true -> (2 * 8) mod (4 * 4) = 0 *)
        intros H.
        vm_compute.
        reflexivity.
Qed.