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

Lemma not_prime_0 : ~is_prime 0.
Proof.
  unfold is_prime.
  intros [H _].
  lia.
Qed.

Example test_intersection : intersection_spec 1 2 2 3 "NO"%string.
Proof.
  unfold intersection_spec.
  simpl.
  split.
  - (* l > r case *)
    intros H. lia.
  - split.
    + (* l <= r /\ is_prime length -> YES *)
      intros Hle Hprime.
      (* l = 2, r = 2, length = 0 *)
      (* 0 is not prime, so this case is vacuously true if we can show is_prime 0 is false *)
      exfalso.
      apply not_prime_0.
      exact Hprime.
    + (* l <= r /\ ~is_prime length -> NO *)
      intros Hle Hnprime.
      reflexivity.
Qed.