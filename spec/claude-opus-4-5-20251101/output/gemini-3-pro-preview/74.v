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

Example test_case_empty : total_match_spec [] [] [].
Proof.
  (* Unfold the specification definition *)
  unfold total_match_spec.
  
  (* Simplify the computation of total_chars for empty lists *)
  simpl.
  
  (* Split the conjunction into two subgoals *)
  split.
  
  - (* Subgoal 1: 0 <= 0 -> [] = [] *)
    intros H.
    reflexivity.
    
  - (* Subgoal 2: 0 > 0 -> [] = [] *)
    intros H.
    (* 0 > 0 implies 0 < 0, which is impossible for natural numbers. *)
    (* Inversion on the hypothesis H reveals the contradiction. *)
    inversion H.
Qed.