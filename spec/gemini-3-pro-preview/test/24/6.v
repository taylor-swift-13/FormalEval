Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_2: largest_divisor_spec 2 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 1 2 *)
    exists 2. reflexivity.
  - split.
    + (* Prove 1 < 2 *)
      lia.
    + (* Prove maximality *)
      intros k Hdiv Hlt.
      (* In Z, k < 2 implies k <= 1 immediately *)
      lia.
Qed.