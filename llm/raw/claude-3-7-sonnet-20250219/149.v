
Require Import List.
Require Import String.
Require Import ZArith.
Import ListNotations.

Definition even (n : nat) : Prop := exists k, n = 2 * k.

Definition sorted_list_sum_spec (lst result : list string) : Prop :=
  (* All elements in result have even length *)
  (forall s, In s result -> even (String.length s)) /\
  (* result is a sublist of lst containing only strings with even length *)
  (forall s, In s result <-> In s lst /\ even (String.length s)) /\
  (* result is sorted by ascending length, and by alphabetical order if lengths equal *)
  (forall i j s t,
      nth_error result i = Some s ->
      nth_error result j = Some t ->
      i < j ->
      (String.length s < String.length t) \/
      (String.length s = String.length t /\ s <= t)).
