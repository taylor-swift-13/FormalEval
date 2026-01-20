Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example largest_divisor_spec_2 : largest_divisor_spec 2%Z 1%Z.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2%Z. lia.
  - right.
    split; [lia|].
    split; [lia|].
    intros m [Hm1 Hm2] Hdiv.
    lia.
Qed.