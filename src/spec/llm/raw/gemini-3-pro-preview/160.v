
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Define operator precedence levels to match Python's order of operations *)
Definition op_precedence (op : string) : nat :=
  if string_dec op "**" then 3
  else if string_dec op "*" then 2
  else if string_dec op "//" then 2
  else 1. (* + and - *)

(* Define the arithmetic operations corresponding to the strings *)
(* Note: Z.div represents floor division, matching Python's // operator *)
Definition apply_op (op : string) (v1 v2 : Z) : Z :=
  if string_dec op "+" then v1 + v2
  else if string_dec op "-" then v1 - v2
  else if string_dec op "*" then v1 * v2
  else if string_dec op "//" then v1 / v2
  else if string_dec op "**" then v1 ^ v2
  else 0.

(* Predicate to check if a precedence value is minimal within a list of operators *)
Definition is_min_precedence (ops : list string) (p : nat) : Prop :=
  Forall (fun op => p <= op_precedence op)%nat ops.

(* Inductive predicate defining a valid splitting point in the operator list based on precedence rules.
   Python evaluates expressions based on precedence. 
   - Operators with lower precedence are evaluated later (higher in the AST).
   - ** is right-associative (split at the first occurrence of min precedence).
   - +, -, *, // are left-associative (split at the last occurrence of min precedence).
*)
Inductive valid_split : list string -> nat -> string -> Prop :=
| Split_Right_Assoc : forall ops k op,
    nth_error ops k = Some op ->
    op_precedence op = 3%nat ->
    is_min_precedence ops 3%nat ->
    (* For right associativity, we pick the first occurrence *)
    (forall j, (j < k)%nat -> exists op', nth_error ops j = Some op' /\ (op_precedence op' > 3)%nat) ->
    valid_split ops k op
| Split_Left_Assoc : forall ops k op p,
    nth_error ops k = Some op ->
    op_precedence op = p ->
    (p < 3)%nat ->
    is_min_precedence ops p ->
    (* For left associativity, we pick the last occurrence *)
    (forall j, (j > k)%nat -> (j < length ops)%nat -> exists op', nth_error ops j = Some op' /\ (op_precedence op' > p)%nat) ->
    valid_split ops k op.

(* Main evaluation relation *)
Inductive algebra_eval : list string -> list Z -> Z -> Prop :=
| AE_Base : forall n, 
    algebra_eval [] [n] n
| AE_Step : forall ops nums res k op opsL opsR numsL numsR vL vR,
    (* Ensure the lists are valid for a step *)
    length ops = length nums - 1 ->
    (* Find the correct operator to split on *)
    valid_split ops k op ->
    (* Split operators *)
    opsL = firstn k ops ->
    opsR = skipn (S k) ops ->
    (* Split operands: numsL has length k+1, numsR has remaining *)
    numsL = firstn (S k) nums ->
    numsR = skipn (S k) nums ->
    (* Recursive evaluation *)
    algebra_eval opsL numsL vL ->
    algebra_eval opsR numsR vR ->
    (* Combine results *)
    res = apply_op op vL vR ->
    algebra_eval ops nums res.

Definition do_algebra_spec (operator : list string) (operand : list Z) (result : Z) : Prop :=
  algebra_eval operator operand result.
