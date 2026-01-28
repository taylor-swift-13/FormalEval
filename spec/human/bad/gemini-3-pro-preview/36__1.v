Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
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

Example test_problem_36 : problem_36_spec 50 0.
Proof.
  unfold problem_36_spec.
  
  Ltac solve_d7 :=
    match goal with
    | [ |- digit_7_count_rel 0 _ ] => apply d7c_zero
    | [ |- digit_7_count_rel ?n _ ] =>
        let d := eval compute in (n mod 10) in
        match d with
        | 7 => apply d7c_mod10_7; [ reflexivity | solve_d7 ]
        | _ => apply d7c_mod10_other; [ lia | solve_d7 ]
        end
    end.

  Ltac solve_fbz :=
    match goal with
    | [ |- fizz_buzz_rel 0 0 ] => apply fbz_zero
    | [ |- fizz_buzz_rel (S ?n) ?acc ] =>
        let is_div := eval compute in ((n mod 11 =? 0) || (n mod 13 =? 0))%bool in
        match is_div with
        | true => 
            eapply fbz_next_div; 
            [ solve_fbz 
            | let m11 := eval compute in (n mod 11) in
              match m11 with
              | 0 => left; reflexivity
              | _ => right; reflexivity
              end
            | solve_d7 ]
        | false =>
            apply fbz_next_nodiv; 
            [ solve_fbz 
            | lia ]
        end
    end.

  solve_fbz.
Qed.