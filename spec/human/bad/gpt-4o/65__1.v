(* Import necessary libraries *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* Definitions and relations as previously provided *)

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

(* Test case: input = [100%Z; 2%Z], output = "001" *)

Example test_case_001 : problem_65_spec 100 2 "001".
Proof.
  unfold problem_65_spec.
  right. right. right.
  exists [1;0;0], 3, 2, 1, [0;0], [1].
  split.
  - discriminate.
  - split.
    + apply tdr_nonzero. discriminate.
      apply tdfr_multi with (fuel := 3) (fuel' := 2) (rest := [1]).
      * reflexivity.
      * lia.
      * apply tdfr_multi with (fuel := 2) (fuel' := 1) (rest := []).
        -- reflexivity.
        -- lia.
        -- apply tdfr_single with (fuel := 1) (fuel' := 0).
           ++ reflexivity.
           ++ lia.
    + split. reflexivity.
      split. reflexivity.
      split. reflexivity.
      split. reflexivity.
      split. reflexivity.
      apply fdtsr_cons with (h := 0) (t := [0;1]) (rest := "01").
      * apply fdtsr_cons with (h := 0) (t := [1]) (rest := "1").
        -- apply fdtsr_cons with (h := 1) (t := []) (rest := "").
           ++ apply fdtsr_nil.
           ++ reflexivity.
        -- reflexivity.
      * reflexivity.
Qed.