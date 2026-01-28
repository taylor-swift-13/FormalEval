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

Example test_intersection : intersection_spec (11, 15) (11, 15) "NO".
Proof.
  unfold intersection_spec.
  simpl.
  right.
  split.
  - reflexivity.
  - unfold is_prime.
    intro H.
    destruct H as [_ Hforall].
    specialize (Hforall 2).
    assert (H_le : 2 <= 2) by apply Z.le_refl.
    assert (H_sq : 2 * 2 <= 4) by apply Z.le_refl.
    specialize (Hforall H_le H_sq).
    compute in Hforall.
    apply Hforall.
    reflexivity.
Qed.