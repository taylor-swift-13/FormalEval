
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Definition is_even_length (s : string) : bool :=
  Nat.even (String.length s).

Definition string_le (s1 s2 : string) : Prop :=
  s1 = s2 \/ String.lt s1 s2.

Definition custom_le (s1 s2 : string) : Prop :=
  (String.length s1 < String.length s2) \/
  (String.length s1 = String.length s2 /\ string_le s1 s2).

Definition sorted_list_sum_spec (lst : list string) (result : list string) : Prop :=
  Permutation result (filter is_even_length lst) /\
  Sorted custom_le result.
