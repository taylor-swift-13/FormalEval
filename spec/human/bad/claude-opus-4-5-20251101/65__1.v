Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Inductive to_digits_fuel_rel : nat -> nat -> list nat -> Prop :=
  | tdfr_zero : forall n, to_digits_fuel_rel n 0 []
  | tdfr_single : forall n fuel fuel',
      fuel = S fuel' ->
      (n <? 10)%nat = true ->
      to_digits_fuel_rel n fuel [n]
  | tdfr_multi : forall n fuel fuel' rest,
      fuel = S fuel' ->
      (n <? 10)%nat = false ->
      to_digits_fuel_rel (n / 10) fuel' rest ->
      to_digits_fuel_rel n fuel (rest ++ [n mod 10]).

Inductive to_digits_rel : nat -> list nat -> Prop :=
  | tdr_zero : to_digits_rel 0 [0]
  | tdr_nonzero : forall n digits, n <> 0 -> to_digits_fuel_rel n n digits -> to_digits_rel n digits.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Inductive from_digits_to_string_rel : list nat -> string -> Prop :=
  | fdtsr_nil : from_digits_to_string_rel [] ""
  | fdtsr_cons : forall h t result rest,
      from_digits_to_string_rel t rest ->
      result = digit_to_string h ++ rest ->
      from_digits_to_string_rel (h :: t) result.

Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  (x = 0 /\ result = "0") \/
  (exists digits len,
     x <> 0 /\
     to_digits_rel x digits /\
     len = length digits /\
     (len <? shift)%nat = true /\
     from_digits_to_string_rel (rev digits) result) \/
  (exists digits len effective_shift,
     x <> 0 /\
     to_digits_rel x digits /\
     len = length digits /\
     (len <? shift)%nat = false /\
     effective_shift = shift mod len /\
     effective_shift = 0 /\
     from_digits_to_string_rel digits result) \/
  (exists digits len effective_shift split_point new_head new_tail,
     x <> 0 /\
     to_digits_rel x digits /\
     len = length digits /\
     (len <? shift)%nat = false /\
     effective_shift = shift mod len /\
     effective_shift <> 0 /\
     split_point = len - effective_shift /\
     new_head = skipn split_point digits /\
     new_tail = firstn split_point digits /\
     from_digits_to_string_rel (new_head ++ new_tail) result).

(* 100 / 10 = 10, 100 mod 10 = 0 *)
(* 10 / 10 = 1, 10 mod 10 = 0 *)
(* 1 < 10, so [1] *)
(* Result: [1] ++ [0] = [1; 0], then [1; 0] ++ [0] = [1; 0; 0] *)

Lemma to_digits_fuel_1 : to_digits_fuel_rel 1 98 [1].
Proof.
  apply (tdfr_single 1 98 97).
  - reflexivity.
  - reflexivity.
Qed.

Lemma to_digits_fuel_10 : to_digits_fuel_rel 10 99 [1; 0].
Proof.
  replace [1; 0] with ([1] ++ [0]) by reflexivity.
  apply (tdfr_multi 10 99 98 [1]).
  - reflexivity.
  - reflexivity.
  - exact to_digits_fuel_1.
Qed.

Lemma to_digits_fuel_100 : to_digits_fuel_rel 100 100 [1; 0; 0].
Proof.
  replace [1; 0; 0] with ([1; 0] ++ [0]) by reflexivity.
  apply (tdfr_multi 100 100 99 [1; 0]).
  - reflexivity.
  - reflexivity.
  - exact to_digits_fuel_10.
Qed.

Lemma to_digits_100 : to_digits_rel 100 [1; 0; 0].
Proof.
  apply tdr_nonzero.
  - lia.
  - exact to_digits_fuel_100.
Qed.

Lemma from_digits_001 : from_digits_to_string_rel [0; 0; 1] "001".
Proof.
  apply (fdtsr_cons 0 [0; 1] "001" "01").
  - apply (fdtsr_cons 0 [1] "01" "1").
    + apply (fdtsr_cons 1 [] "1" "").
      * apply fdtsr_nil.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Example problem_65_test : problem_65_spec 100 2 "001".
Proof.
  unfold problem_65_spec.
  right. right. right.
  exists [1; 0; 0], 3, 2, 1, [0; 0], [1].
  repeat split.
  - lia.
  - exact to_digits_100.
  - reflexivity.
  - lia.
  - simpl. exact from_digits_001.
Qed.