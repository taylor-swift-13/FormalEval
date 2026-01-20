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

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) by lia.
    subst d.
    simpl.
    lia.
Qed.

Example test_intersection : intersection_spec 1 5 3 7 "YES"%string.
Proof.
  unfold intersection_spec.
  simpl.
  split.
  - intros H. lia.
  - split.
    + intros Hle Hprime.
      reflexivity.
    + intros Hle Hnprime.
      exfalso.
      apply Hnprime.
      exact prime_2.
Qed.