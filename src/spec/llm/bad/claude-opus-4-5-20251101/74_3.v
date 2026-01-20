Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

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

Definition total_match (lst1 lst2 : list string) : list string :=
  let c1 := total_chars lst1 in
  let c2 := total_chars lst2 in
  if c1 <=? c2 then lst1 else lst2.

Example test_total_match : total_match ["hi"; "admin"] ["hi"; "hi"; "admin"; "project"] = ["hi"; "admin"].
Proof.
  unfold total_match.
  simpl.
  reflexivity.
Qed.

Example test_total_match_spec : total_match_spec ["hi"; "admin"] ["hi"; "hi"; "admin"; "project"] ["hi"; "admin"].
Proof.
  unfold total_match_spec.
  simpl.
  split.
  - intros _. reflexivity.
  - intros H. inversion H.
Qed.