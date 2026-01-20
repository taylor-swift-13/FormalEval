Require Import ZArith.
Require Import Strings.String.
Require Import Lia.
Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> Z.rem n d <> 0.

Definition intersection_spec (interval1_start interval1_end : Z) 
                             (interval2_start interval2_end : Z) 
                             (result : string) : Prop :=
  let start1 := Z.min interval1_start interval2_start in
  let end1 := Z.max interval1_start interval2_start in
  let start2 := Z.min interval1_end interval2_end in
  let end2 := Z.max interval1_end interval2_end in
  let l := Z.max interval1_start interval2_start in
  let r := Z.min interval1_end interval2_end in
  let length := r - l in
  (l > r -> result = "NO"%string) /\
  (l <= r -> is_prime length -> result = "YES"%string) /\
  (l <= r -> ~is_prime length -> result = "NO"%string).

Lemma not_prime_20 : ~is_prime 20.
Proof.
  unfold is_prime.
  intros [Hge Hdiv].
  specialize (Hdiv 2).
  assert (H1: 2 <= 2) by lia.
  assert (H2: 2 * 2 <= 20) by lia.
  specialize (Hdiv H1 H2).
  compute in Hdiv.
  congruence.
Qed.

Example test_intersection : intersection_spec (-15) 15 (-10) 10 "NO"%string.
Proof.
  unfold intersection_spec.
  simpl.
  split.
  - intros H. lia.
  - split.
    + intros Hle Hprime.
      exfalso.
      apply not_prime_20.
      exact Hprime.
    + intros Hle Hnprime.
      reflexivity.
Qed.