
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Definition is_nested_spec (string : string) (result : bool) : Prop :=
  exists subseq, 
    (forall i, nth_error subseq i = Some "[" \/ nth_error subseq i = Some "]") /\
    (forall i, nth_error subseq i = Some "[" -> exists j, j > i /\ nth_error subseq j = Some "]") /\
    (forall i, nth_error subseq i = Some "]" -> exists j, j < i /\ nth_error subseq j = Some "[") /\
    (exists i j, i < j /\ nth_error subseq i = Some "[" /\ nth_error subseq j = Some "[" /\ 
                 exists k, i < k < j /\ nth_error subseq k = Some "]") /\
    result = true \/ 
    (forall subseq, 
      (forall i, nth_error subseq i = Some "[" \/ nth_error subseq i = Some "]") ->
      (forall i, nth_error subseq i = Some "[" -> exists j, j > i /\ nth_error subseq j = Some "]") ->
      (forall i, nth_error subseq i = Some "]" -> exists j, j < i /\ nth_error subseq j = Some "[") ->
      (forall i j, i < j -> nth_error subseq i = Some "[" -> nth_error subseq j = Some "[" -> 
                   (forall k, i < k < j -> nth_error subseq k <> Some "]")) ->
      result = false).
