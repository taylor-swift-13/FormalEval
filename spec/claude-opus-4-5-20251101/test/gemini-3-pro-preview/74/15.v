Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ s' => S (string_length s')
  end.

Fixpoint total_chars (lst : list string) : nat :=
  match lst with
  | [] => 0
  | s :: rest => string_length s + total_chars rest
  end.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := total_chars lst1 in
  let c2 := total_chars lst2 in
  (c1 <= c2 -> result = lst1) /\
  (c1 > c2 -> result = lst2).

Example test_case_1 : total_match_spec ["happy"; "new"; "year"] ["happy"; "new"; "year"; "2022"] ["happy"; "new"; "year"].
Proof.
  unfold total_match_spec.
  simpl.
  split.
  - intros H. reflexivity.
  - intros H. lia.
Qed.