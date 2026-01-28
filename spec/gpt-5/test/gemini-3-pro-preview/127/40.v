Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_prime (a : Z) : Prop :=
  2 <= a /\ forall x : Z, 2 <= x -> x * x <= a -> Z.modulo a x <> 0.

Definition intersection_spec (interval1 interval2 : Z * Z) (result : string) : Prop :=
  let l := Z.max (fst interval1) (fst interval2) in
  let r := Z.min (snd interval1) (snd interval2) in
  (result = "YES" /\ is_prime (r - l)) \/ (result = "NO" /\ ~ is_prime (r - l)).

Example test_intersection : intersection_spec (5, 10) (5, 10) "YES".
Proof.
  unfold intersection_spec.
  simpl.
  left.
  split.
  - reflexivity.
  - unfold is_prime.
    split.
    + lia.
    + intros x Hle Hsq.
      assert (x < 3).
      {
        destruct (Z_le_gt_dec 3 x).
        - assert (9 <= x * x).
          { change 9 with (3 * 3). apply Z.mul_le_mono_nonneg; lia. }
          lia.
        - lia.
      }
      assert (x = 2) by lia.
      subst.
      compute.
      discriminate.
Qed.