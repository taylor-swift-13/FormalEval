Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_prime (a : Z) : Prop :=
  2 <= a /\ forall x : Z, 2 <= x -> x * x <= a -> Z.modulo a x <> 0.

Definition intersection_spec (interval1 interval2 : Z * Z) (result : string) : Prop :=
  let l := Z.max (fst interval1) (fst interval2) in
  let r := Z.min (snd interval1) (snd interval2) in
  (result = "YES" /\ is_prime (r - l)) \/ (result = "NO" /\ ~ is_prime (r - l)).

Example test_intersection : intersection_spec (-2, 2) (-4, 0) "YES".
Proof.
  unfold intersection_spec.
  simpl.
  left.
  split.
  - reflexivity.
  - unfold is_prime.
    split.
    + apply Z.le_refl.
    + intros x Hge2 Hsq.
      assert (H4: 4 <= x * x).
      {
        change 4 with (2 * 2).
        apply Z.mul_le_mono_nonneg; try assumption.
        - compute; congruence.
        - compute; congruence.
      }
      assert (Hcontra: 4 <= 2).
      { apply Z.le_trans with (m := x * x); assumption. }
      compute in Hcontra.
      contradiction.
Qed.