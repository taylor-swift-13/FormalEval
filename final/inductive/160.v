(* def do_algebra(operator, operand):
"""
Given two lists operator, and operand. The first list has basic algebra operations, and
the second list is a list of integers. Use the two given lists to build the algebric
expression and return the evaluation of this expression.

The basic algebra operations:
Addition ( + )
Subtraction ( - )
Multiplication ( * )
Floor division ( // )
Exponentiation ( ** )

Example:
operator['+', '*', '-']
array = [2, 3, 4, 5]
result = 2 + 3 * 4 - 5
=> result = 9

Note:
The length of operator list is equal to the length of operand list minus one.
Operand is a list of of non-negative integers.
Operator list has at least one operator, and operand list has at least two operands.

""" *)
(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition Zdiv_floor := Z.div.

Inductive interp_op_rel : ascii -> Z -> Z -> Z -> Prop :=
  | ior_add : forall z1 z2, interp_op_rel "+"%char z1 z2 (z1 + z2)
  | ior_sub : forall z1 z2, interp_op_rel "-"%char z1 z2 (z1 - z2)
  | ior_mul : forall z1 z2, interp_op_rel "*"%char z1 z2 (z1 * z2)
  | ior_div : forall z1 z2, z2 <> 0 -> interp_op_rel "/"%char z1 z2 (Z.div z1 z2)
  | ior_pow : forall z1 z2, interp_op_rel "^"%char z1 z2 (Z.pow z1 z2)
  | ior_other : forall op z1 z2, op <> "+"%char -> op <> "-"%char -> op <> "*"%char -> op <> "/"%char -> op <> "^"%char -> interp_op_rel op z1 z2 0.

Inductive find_index_aux_rel {A} : (A -> bool) -> list A -> nat -> option nat -> Prop :=
  | fiar_nil : forall p n, find_index_aux_rel p [] n None
  | fiar_found : forall p x xs n, p x = true -> find_index_aux_rel p (x :: xs) n (Some n)
  | fiar_skip : forall p x xs n result,
      p x = false ->
      find_index_aux_rel p xs (S n) result ->
      find_index_aux_rel p (x :: xs) n result.

Inductive find_index_rel {A} : (A -> bool) -> list A -> option nat -> Prop :=
  | fir_base : forall p l result, find_index_aux_rel p l 0 result -> find_index_rel p l result.

Inductive rfind_index_rel {A} : (A -> bool) -> list A -> option nat -> Prop :=
  | rfir_base : forall p l rev_l idx rev_idx,
      rev l = rev_l ->
      find_index_rel p rev_l rev_idx ->
      match rev_idx with
      | Some i => idx = Some ((length l - 1) - i)%nat
      | None => idx = None
      end ->
      rfind_index_rel p l idx.

Inductive eval_helper_rel : list ascii -> list Z -> nat -> Z -> Prop :=
  | ehr_zero_fuel : forall ops nums, eval_helper_rel ops nums 0 0
  | ehr_empty : forall ops fuel, eval_helper_rel ops [] fuel 0
  | ehr_single : forall ops n fuel, eval_helper_rel ops [n] fuel n
  | ehr_add_sub : forall ops nums fuel fuel' i op left_ops right_ops left_nums right_nums left_res right_res res,
      fuel = S fuel' ->
      rfind_index_rel (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ops (Some i) ->
      (i < length ops)%nat ->
      op = nth i ops " "%char ->
      left_ops = firstn i ops ->
      right_ops = skipn (i + 1) ops ->
      left_nums = firstn (i + 1) nums ->
      right_nums = skipn (i + 1) nums ->
      eval_helper_rel left_ops left_nums fuel' left_res ->
      eval_helper_rel right_ops right_nums fuel' right_res ->
      interp_op_rel op left_res right_res res ->
      eval_helper_rel ops nums fuel res
  | ehr_mul_div : forall ops nums fuel fuel' i op left_ops right_ops left_nums right_nums left_res right_res res,
      fuel = S fuel' ->
      rfind_index_rel (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ops None ->
      rfind_index_rel (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ops (Some i) ->
      (i < length ops)%nat ->
      op = nth i ops " "%char ->
      left_ops = firstn i ops ->
      right_ops = skipn (i + 1) ops ->
      left_nums = firstn (i + 1) nums ->
      right_nums = skipn (i + 1) nums ->
      eval_helper_rel left_ops left_nums fuel' left_res ->
      eval_helper_rel right_ops right_nums fuel' right_res ->
      interp_op_rel op left_res right_res res ->
      eval_helper_rel ops nums fuel res
  | ehr_pow : forall ops nums fuel fuel' i op left_ops right_ops left_nums right_nums left_res right_res res,
      fuel = S fuel' ->
      rfind_index_rel (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ops None ->
      rfind_index_rel (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ops None ->
      find_index_rel (fun c => (c =? "^"%char)%char) ops (Some i) ->
      (i < length ops)%nat ->
      op = nth i ops " "%char ->
      left_ops = firstn i ops ->
      right_ops = skipn (i + 1) ops ->
      left_nums = firstn (i + 1) nums ->
      right_nums = skipn (i + 1) nums ->
      eval_helper_rel left_ops left_nums fuel' left_res ->
      eval_helper_rel right_ops right_nums fuel' right_res ->
      interp_op_rel op left_res right_res res ->
      eval_helper_rel ops nums fuel res
  | ehr_none : forall ops nums fuel fuel',
      fuel = S fuel' ->
      rfind_index_rel (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ops None ->
      rfind_index_rel (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ops None ->
      find_index_rel (fun c => (c =? "^"%char)%char) ops None ->
      eval_helper_rel ops nums fuel 0.

Inductive eval_rel : list ascii -> list Z -> Z -> Prop :=
  | er_base : forall ops nums fuel result,
      fuel = length nums ->
      eval_helper_rel ops nums fuel result ->
      eval_rel ops nums result.



Definition do_algebra_spec (operators : list ascii) (operands : list Z) (result : Z) : Prop :=
  exists fuel,
    fuel = length operands /\
    eval_helper_rel operators operands fuel result.
