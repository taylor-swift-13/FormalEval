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

Example test_intersection : intersection_spec (15, 25) (15, 25) "NO".
Proof.
  unfold intersection_spec.
  simpl.
  right.
  split.
  - reflexivity.
  - unfold is_prime.
    intro H.
    destruct H as [_ H].
    specialize (H 2).
    assert (H1: 2 <= 2) by (compute; discriminate).
    assert (H2: 2 * 2 <= 10) by (compute; discriminate).
    specialize (H H1 H2).
    compute in H.
    apply H.
    reflexivity.
Qed.