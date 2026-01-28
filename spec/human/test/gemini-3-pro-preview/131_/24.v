Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.

Inductive get_digits_rel : nat -> list nat -> Prop :=
| gdr_zero : get_digits_rel 0%nat nil
| gdr_step : forall n d ds, n > 0 -> d = n mod 10 ->
    get_digits_rel (n / 10) ds ->
    get_digits_rel n (d :: ds).

Inductive filter_odd_digits_rel : list nat -> list nat -> Prop :=
| fodr_nil : filter_odd_digits_rel nil nil
| fodr_odd : forall d ds res, Nat.odd d = true -> filter_odd_digits_rel ds res ->
    filter_odd_digits_rel (d :: ds) (d :: res)
| fodr_even : forall d ds res, Nat.odd d = false -> filter_odd_digits_rel ds res ->
    filter_odd_digits_rel (d :: ds) res.

Inductive product_rel : list nat -> nat -> Prop :=
| pr_nil : product_rel nil 1%nat
| pr_cons : forall d ds p p_tail, product_rel ds p_tail -> p = d * p_tail ->
    product_rel (d :: ds) p.

(* n 为正整数 *)
Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  exists ds odd_ds, get_digits_rel n ds /\
    filter_odd_digits_rel ds odd_ds /\
    (odd_ds = nil -> output = 0%nat) /\
    (odd_ds <> nil -> product_rel odd_ds output).

Example test_problem_131 : problem_131_spec 701 7.
Proof.
  unfold problem_131_spec.
  exists [1; 0; 7], [1; 7].
  repeat split.
  
  - (* Prove get_digits_rel 701 [1; 0; 7] *)
    apply gdr_step with (n := 701) (d := 1) (ds := [0; 7]).
    + lia.
    + reflexivity.
    + replace (701 / 10) with 70 by reflexivity.
      apply gdr_step with (n := 70) (d := 0) (ds := [7]).
      * lia.
      * reflexivity.
      * replace (70 / 10) with 7 by reflexivity.
        apply gdr_step with (n := 7) (d := 7) (ds := []).
        -- lia.
        -- reflexivity.
        -- replace (7 / 10) with 0 by reflexivity.
           apply gdr_zero.
      
  - (* Prove filter_odd_digits_rel [1; 0; 7] [1; 7] *)
    apply fodr_odd.
    + reflexivity.
    + apply fodr_even.
      * reflexivity.
      * apply fodr_odd.
        -- reflexivity.
        -- apply fodr_nil.
    
  - (* Prove implication: odd_ds = nil -> output = 0 *)
    intro H.
    inversion H.
    
  - (* Prove implication: odd_ds <> nil -> product_rel odd_ds output *)
    intro H.
    apply pr_cons with (p_tail := 7).
    + apply pr_cons with (p_tail := 1).
      * apply pr_nil.
      * lia.
    + lia.
Qed.