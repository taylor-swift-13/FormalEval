Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_857_29911_857_2991 : simplify_spec 857 29911 857 2991 false.
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
      * (* Left to Right: (857 * 857) mod (29911 * 2991) = 0 -> false = true *)
        intros H.
        vm_compute in H.
        discriminate.
      * (* Right to Left: false = true -> (857 * 857) mod (29911 * 2991) = 0 *)
        intros H.
        discriminate.
Qed.