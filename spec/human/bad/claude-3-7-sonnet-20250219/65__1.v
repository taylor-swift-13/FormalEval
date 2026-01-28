Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
  | _ => "" (* impossible in digit context *)
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

(* 转换 Z 到 nat 的函数 *)
Definition Z_to_nat_nonneg (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => Pos.to_nat p
  | Zneg _ => 0 (* 只考虑非负输入 *)
  end.

Example test_circular_shift_100_2 :
  problem_65_spec (Z_to_nat_nonneg 100) (Z_to_nat_nonneg 2) "001".
Proof.
  unfold Z_to_nat_nonneg.
  simpl.
  (* x = 100, shift = 2 *)
  assert (Hnz : 100 <> 0) by lia.

  (* 构造 digits = [1;0;0] 且 to_digits_fuel_rel 100 100 [1;0;0] *)
  assert (Hfuel : to_digits_fuel_rel 100 100 [1;0;0]).
  {
    apply tdfr_multi with (fuel' := 99) (rest := [1;0]); try reflexivity; try lia.
    apply tdfr_multi with (fuel' := 9) (rest := [1]); try reflexivity; try lia.
    apply tdfr_single; try reflexivity; try lia.
  }
  apply tdr_nonzero with (digits := [1;0;0]); auto.

  (* length digits = 3 *)
  assert (Hlen : length [1;0;0] = 3) by reflexivity.

  (* len <? shift = (3 <? 2)%nat = false *)
  assert (Hlt : (3 <? 2)%nat = false) by reflexivity.

  (* effective_shift = 2 mod 3 = 2 *)
  assert (Heff : 2 mod 3 = 2) by reflexivity.

  (* effective_shift <> 0 *)
  assert (Heff_neq : 2 <> 0) by lia.

  (* split_point = 3 - 2 = 1 *)
  assert (Hsplit : 3 - 2 = 1) by lia.

  (* new_head = skipn 1 [1;0;0] = [0;0] *)
  assert (Hnew_head : skipn 1 [1;0;0] = [0;0]) by reflexivity.

  (* new_tail = firstn 1 [1;0;0] = [1] *)
  assert (Hnew_tail : firstn 1 [1;0;0] = [1]) by reflexivity.

  (* new_head ++ new_tail = [0;0] ++ [1] = [0;0;1] *)
  assert (Hconcat : [0;0] ++ [1] = [0;0;1]) by reflexivity.

  (* from_digits_to_string_rel [0;0;1] "001" *)
  assert (Hfrom : from_digits_to_string_rel [0;0;1] "001").
  {
    apply fdtsr_cons with (rest := "01").
    - apply fdtsr_cons with (rest := "1").
      + apply fdtsr_cons with (rest := "").
        * apply fdtsr_nil.
        * reflexivity.
      + reflexivity.
    - reflexivity.
  }

  (* 组合 exists，完成证明 *)
  right. right. right.
  exists [1;0;0], 3, 2, 1, [0;0], [1].
  repeat split; try assumption; reflexivity.
Qed.