Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* --- Specification Definitions --- *)

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

(* --- Proof for Test Case: input = [100; 2], output = "001" --- *)

Example test_problem_65 : problem_65_spec 100 2 "001".
Proof.
  unfold problem_65_spec.
  (* Select the 4th branch: circular shift *)
  right. right. right.
  
  (* Instantiate existential variables:
     x = 100
     digits = [1; 0; 0]
     len = 3
     shift = 2
     effective_shift = 2 mod 3 = 2
     split_point = 3 - 2 = 1
     new_head = skipn 1 [1;0;0] = [0;0]
     new_tail = firstn 1 [1;0;0] = [1]
  *)
  exists [1; 0; 0], 3, 2, 1, [0; 0], [1].

  repeat split.
  
  - (* x <> 0 *)
    intro H. inversion H.
    
  - (* to_digits_rel 100 [1; 0; 0] *)
    apply tdr_nonzero.
    + intro H. inversion H.
    + (* Proof of to_digits_fuel_rel 100 100 [1; 0; 0] *)
      (* Reshape list to match tdfr_multi: rest ++ [n mod 10] *)
      change [1; 0; 0] with ([1; 0] ++ [0]).
      eapply tdfr_multi.
      * reflexivity. (* 100 = S 99 *)
      * reflexivity. (* 100 < 10 is false *)
      * (* Recursive step for 10 *)
        simpl.
        change [1; 0] with ([1] ++ [0]).
        eapply tdfr_multi.
        -- reflexivity. (* 99 = S 98 *)
        -- reflexivity. (* 10 < 10 is false *)
        -- (* Recursive step for 1 *)
           simpl.
           eapply tdfr_single.
           ++ reflexivity. (* 98 = S 97 *)
           ++ reflexivity. (* 1 < 10 is true *)

  - (* len = length digits *)
    reflexivity.

  - (* len < shift is false (3 < 2 is false) *)
    reflexivity.

  - (* effective_shift = shift mod len *)
    reflexivity.

  - (* effective_shift <> 0 *)
    intro H. inversion H.

  - (* split_point calculation *)
    reflexivity.

  - (* new_head calculation *)
    simpl. reflexivity.

  - (* new_tail calculation *)
    simpl. reflexivity.

  - (* from_digits_to_string_rel (new_head ++ new_tail) result *)
    (* [0; 0] ++ [1] = [0; 0; 1] -> "001" *)
    simpl.
    constructor.
    + constructor.
      * constructor.
        -- apply fdtsr_nil.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
Qed.