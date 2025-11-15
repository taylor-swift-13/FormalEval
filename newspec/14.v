(* """ Return list of all prefixes from shortest to longest of the input string
>>> all_prefixes('abc')
['a', 'ab', 'abc']
""" *)

(* Spec(input, output) :=

(length(input) = 0 ∧ output = {}) ∨
(length(input) > 0 ∧
  length(output) = length(input) ∧
  ∀ i ∈ [0, length(input)),
    length(output[i]) = i+1 ∧
    prefix(output[i], input)
) *)

Require Import List Ascii.
Import ListNotations.

(* prefix p s := p 是 s 的前缀 *)
Definition prefix  (l1 l2 : list ascii) : Prop :=
  exists rest : list ascii, l2 = l1 ++ rest.

Definition Spec (input : list ascii)(output : list (list ascii)) : Prop :=
  (length input = 0 /\ output = []) \/
  (length input > 0 /\
   length output = length input /\
   forall i, i < length input ->
     length (nth i output ["0"%char]) = i + 1 /\
     prefix (nth i output ["0"%char]) input).
