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

Example test_intersection : intersection_spec (7, 13) (10, 23) "YES".
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
      assert (H4: 2 * 2 <= x * x).
      { apply Z.mul_le_mono_nonneg; lia. }
      lia.
Qed.