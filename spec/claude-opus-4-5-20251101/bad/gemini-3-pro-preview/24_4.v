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

Example test_largest_divisor_100: largest_divisor_spec 100 50.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Case n <= 1 *)
    intros H.
    lia.
  - (* Case n > 1 *)
    intros H.
    split.
    + (* result >= 1 *)
      lia.
    + split.
      * (* result < n *)
        lia.
      * split.
        -- (* n mod result = 0 *)
           reflexivity.
        -- (* forall d ... *)
           intros d H_gt H_lt.
           left.
           intro H_mod.
           (* We prove that d must be 100 if it divides 100 and d > 50 *)
           assert (H_quot: 100 / d = 1).
           { symmetry. apply Z.div_unique with (r := 100 - d).
             - left. lia.
             - lia. }
           rewrite Z.mod_eq in H_mod; try lia.
           rewrite H_quot in H_mod.
           lia.
Qed.