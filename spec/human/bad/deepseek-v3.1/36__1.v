Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
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

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  fizz_buzz_rel n output.

Example test_50 : problem_36_spec 50 0.
Proof.
  unfold problem_36_spec.
  
  (* Build the proof step by step from 0 to 50 *)
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. apply fbz_next_nodiv. 
  apply fbz_zero.
  
  (* Prove each ~(n mod 11 = 0 \/ n mod 13 = 0) condition *)
  all: intro H; destruct H as [H11 | H13];
  all: try (assert (Hmod := Nat.mod_upper_bound n 11); simpl in Hmod);
  all: try (assert (Hmod := Nat.mod_upper_bound n 13); simpl in Hmod);
  all: repeat (match goal with
              | H : ?n mod 11 = 0 |- _ => 
                  let H' := fresh in
                  assert (H' : n < 11 \/ n >= 11) by apply Nat.lt_ge_cases;
                  destruct H'
              | H : ?n mod 13 = 0 |- _ => 
                  let H' := fresh in
                  assert (H' : n < 13 \/ n >= 13) by apply Nat.lt_ge_cases;
                  destruct H'
              | H : ?n < 11, H1 : n mod 11 = 0 |- _ =>
                  rewrite Nat.mod_small in H1; auto
              | H : ?n < 13, H1 : n mod 13 = 0 |- _ =>
                  rewrite Nat.mod_small in H1; auto
              | H : ?n >= 11, H1 : n mod 11 = 0 |- _ =>
                  let Hdiv := fresh in
                  assert (Hdiv : exists q, n = 11 * q) by (apply Nat.mod_divides; [auto|exists 1]);
                  destruct Hdiv as [q Hdiv]; subst n;
                  simpl in *; discriminate
              | H : ?n >= 13, H1 : n mod 13 = 0 |- _ =>
                  let Hdiv := fresh in
                  assert (Hdiv : exists q, n = 13 * q) by (apply Nat.mod_divides; [auto|exists 1]);
                  destruct Hdiv as [q Hdiv]; subst n;
                  simpl in *; discriminate
              end);
  all: auto with arith.
Qed.