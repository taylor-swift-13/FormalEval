(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

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

Example test_case_problem_65_1 :
  let x := Z.to_nat 100%Z in
  let shift := Z.to_nat 2%Z in
  problem_65_spec x shift "001".
Proof.
  simpl.
  right. right. right.
  (* Choose the last case with effective_shift <> 0 *)
  exists [1; 0; 0]. exists 3.
  exists (2 mod 3).
  exists (3 - (2 mod 3)).
  exists (skipn (3 - (2 mod 3)) [1; 0; 0]).
  exists (firstn (3 - (2 mod 3)) [1; 0; 0]).
  repeat split.
  - (* x <> 0 *)
    lia.
  - (* to_digits_rel 100 [1;0;0] *)
    apply tdr_nonzero.
    + lia.
    + (* Build to_digits_fuel_rel 100 100 [1;0;0] *)
      eapply tdfr_multi with (fuel' := 99) (rest := [1;0]).
      * reflexivity.
      * simpl. reflexivity.
      * (* to_digits_fuel_rel 10 99 [1;0] *)
        eapply tdfr_multi with (fuel' := 98) (rest := [1]).
        -- reflexivity.
        -- simpl. reflexivity.
        -- (* to_digits_fuel_rel 1 98 [1] *)
           apply tdfr_single with (fuel' := 97).
           ++ reflexivity.
           ++ simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - (* effective_shift <> 0 *)
    simpl. lia.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    (* from_digits_to_string_rel [0;0;1] "001" *)
    apply fdtsr_cons with (h := 0) (t := [0;1]) (rest := "01").
    + apply fdtsr_cons with (h := 0) (t := [1]) (rest := "1").
      * apply fdtsr_cons with (h := 1) (t := []) (rest := "").
        -- apply fdtsr_nil.
        -- simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. reflexivity.
Qed.