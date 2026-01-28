Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Inductive digit_7_count_rel : nat -> nat -> Prop :=
| d7c_zero : digit_7_count_rel 0 0
| d7c_mod10_7 : forall n c,
    n mod 10 = 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n (S c)
| d7c_mod10_other : forall n c,
    n mod 10 <> 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n c.

Inductive fizz_buzz_rel : nat -> nat -> Prop :=
| fbz_zero : fizz_buzz_rel 0 0
| fbz_next_div : forall n acc c,
    fizz_buzz_rel n acc ->
    (n mod 11 = 0 \/ n mod 13 = 0) ->
    digit_7_count_rel n c ->
    fizz_buzz_rel (S n) (acc + c)
| fbz_next_nodiv : forall n acc,
    fizz_buzz_rel n acc ->
    ~(n mod 11 = 0 \/ n mod 13 = 0) ->
    fizz_buzz_rel (S n) acc.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  fizz_buzz_rel n output.

(* Helper to build digit_7_count_rel for numbers without 7 *)
Lemma digit_7_count_no_7 : forall n,
  n < 10 -> n <> 7 -> digit_7_count_rel n 0.
Proof.
  intros n Hlt Hne.
  apply d7c_mod10_other.
  - rewrite Nat.mod_small; lia.
  - rewrite Nat.div_small; [constructor | lia].
Qed.

Lemma digit_7_count_two_digits : forall n,
  n >= 10 -> n < 100 -> n mod 10 <> 7 -> (n / 10) mod 10 <> 7 ->
  digit_7_count_rel n 0.
Proof.
  intros n Hge Hlt Hmod1 Hmod2.
  apply d7c_mod10_other; auto.
  assert (n / 10 < 10) by (apply Nat.div_lt_upper_bound; lia).
  apply d7c_mod10_other.
  - rewrite Nat.mod_small; lia.
  - rewrite Nat.div_small; [constructor | lia].
Qed.

Example problem_36_test : problem_36_spec 50 0.
Proof.
  unfold problem_36_spec.
  
  (* We build the proof by going from 49 down to 0 *)
  (* Numbers divisible by 11 or 13 less than 50: 0, 11, 13, 22, 26, 33, 39, 44 *)
  (* None contain the digit 7, so total is 0 *)
  
  (* 49 -> 50 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 48 -> 49 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 47 -> 48 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 46 -> 47 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 45 -> 46 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 44 -> 45 : divisible by 11 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| left; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 43 -> 44 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 42 -> 43 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 41 -> 42 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 40 -> 41 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 39 -> 40 : divisible by 13 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| right; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 38 -> 39 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 37 -> 38 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 36 -> 37 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 35 -> 36 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 34 -> 35 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 33 -> 34 : divisible by 11 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| left; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 32 -> 33 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 31 -> 32 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 30 -> 31 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 29 -> 30 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 28 -> 29 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 27 -> 28 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 26 -> 27 : divisible by 13 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| right; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 25 -> 26 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 24 -> 25 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 23 -> 24 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 22 -> 23 : divisible by 11 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| left; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 21 -> 22 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 20 -> 21 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 19 -> 20 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 18 -> 19 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 17 -> 18 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 16 -> 17 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 15 -> 16 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 14 -> 15 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 13 -> 14 : divisible by 13 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| right; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 12 -> 13 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 11 -> 12 : divisible by 11 *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| left; reflexivity | ].
  { apply digit_7_count_two_digits; lia. }
  (* 10 -> 11 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 9 -> 10 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 8 -> 9 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 7 -> 8 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 6 -> 7 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 5 -> 6 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 4 -> 5 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 3 -> 4 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 2 -> 3 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 1 -> 2 : not divisible *)
  apply fbz_next_nodiv; [| intros [H|H]; compute in H; discriminate].
  (* 0 -> 1 : divisible by both 11 and 13 (0 mod anything = 0) *)
  change 0 with (0 + 0).
  apply fbz_next_div; [| left; reflexivity | constructor].
  (* Base case *)
  constructor.
Qed.