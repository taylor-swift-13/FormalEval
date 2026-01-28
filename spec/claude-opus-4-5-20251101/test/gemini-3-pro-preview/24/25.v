Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  (n <= 1 -> result = 1) /\
  (n > 1 -> 
    result >= 1 /\
    result < n /\
    (n mod result = 0) /\
    (forall d : Z, d > result -> d < n -> n mod d <> 0 \/ d * (n / d) <> n / (n / d))).

Example test_largest_divisor_236: largest_divisor_spec 236 118.
Proof.
  unfold largest_divisor_spec.
  split.
  - intros H.
    lia.
  - intros H.
    split.
    + lia.
    + split.
      * lia.
      * split.
        -- reflexivity.
        -- intros d H_gt H_lt.
           left.
           intro H_mod.
           assert (H_div: 236 / d = 1).
           {
             symmetry.
             apply Z.div_unique with (r := 236 - d).
             - left. lia.
             - lia.
           }
           rewrite Z.mod_eq in H_mod.
           ++ rewrite H_div in H_mod. lia.
           ++ lia.
Qed.