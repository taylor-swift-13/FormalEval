Require Import ZArith.
Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.
Open Scope string_scope.

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

Example test_intersection_no : intersection_spec 1 2 2 3 "NO".
Proof.
  (* Unfold the specification to expose the logic *)
  unfold intersection_spec.
  
  (* Simplify Z operations (max, min, sub) for the concrete values *)
  (* l = max 1 2 = 2 *)
  (* r = min 2 3 = 2 *)
  (* length = 2 - 2 = 0 *)
  simpl.

  (* The goal is a conjunction of three implications. Split them. *)
  repeat split.

  - (* Case 1: l > r -> result = "NO" *)
    (* 2 > 2 simplifies to False. We derive a contradiction. *)
    intros H_gt.
    inversion H_gt.

  - (* Case 2: l <= r -> is_prime length -> result = "YES" *)
    (* We need to prove that if length (0) is prime, then "NO" = "YES" *)
    intros _ H_prime.
    (* Expand the definition of is_prime *)
    unfold is_prime in H_prime.
    (* H_prime asserts 0 >= 2, which is false *)
    destruct H_prime as [H_ge2 _].
    inversion H_ge2.

  - (* Case 3: l <= r -> ~is_prime length -> result = "NO" *)
    (* We need to prove "NO" = "NO", which is reflexive *)
    intros _ _.
    reflexivity.
Qed.