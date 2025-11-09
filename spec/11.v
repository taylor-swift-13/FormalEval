(* """ Input are two strings a and b consisting only of 1s and 0s.
Perform binary XOR on these inputs and return result also as a string.
>>> string_xor('010', '110')
'100'
""" *)

(* Spec(a, b, output) :=
length(output) == length(a) ∧
∀ i ∈ [0, length(output)),
  a[i] = b[i] -> output[i] = '0' /\
  a[i]<>b[i] -> output[i] = '1' *)

Require Import List.
Require Import Ascii.
Require Import Bool.
Import ListNotations.
Open Scope char_scope.

(* 定义 Spec 规约 *)

Definition Spec (a b output : list ascii) : Prop :=
  length a = length b /\
  length output = length a /\
  forall i,
    i < length output ->
    (nth i a "0" = nth i b "0" -> nth i output "0" = "0") /\
    (nth i a "0" <> nth i b "0" -> nth i output "0" = "1").