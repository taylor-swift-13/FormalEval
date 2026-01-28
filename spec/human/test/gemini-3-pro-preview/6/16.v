Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Helper function required for SplitOnSpaces_aux *)
Fixpoint string_of_list_ascii (s : list ascii) : string :=
  match s with
  | [] => EmptyString
  | c :: s => String c (string_of_list_ascii s)
  end.

(* Definitions provided in the specification *)

(* Define ASCII characters *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  Specification 1: MaxDepth(g)
  Calculates the maximum nesting depth of a single group of parentheses.
*)
Fixpoint max_depth_aux (g : string) (current_depth max_seen : nat) : nat :=
  match g with
  | EmptyString => max_seen
  | String h t =>
    if ascii_dec h lparen then
      let new_depth := S current_depth in
      max_depth_aux t new_depth (Nat.max max_seen new_depth)
    else if ascii_dec h rparen then
      max_depth_aux t (Nat.pred current_depth) max_seen
    else
      max_depth_aux t current_depth max_seen (* Ignore other characters *)
  end.

Definition MaxDepth (g : string) : nat :=
  max_depth_aux g 0 0.

(*
  Specification 2: SplitOnSpaces(S)
  Splits a string into a list of strings based on spaces.
*)
Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h space then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* Multiple or leading spaces *)
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

(*
  Helper assertion: Check if a character is a parenthesis or space
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Fixpoint IsBalanced_aux (l : string) (count : nat) : Prop :=
  match l with
  | EmptyString => count = 0
  | String h t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False (* Right parenthesis exceeds left, unbalanced *)
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count (* Ignore other characters *)
  end.

Definition IsBalanced (l : string) : Prop :=
  IsBalanced_aux l 0.

Definition parse_nested_parens_impl (input : string) : list nat :=
  List.map MaxDepth (SplitOnSpaces input).

(*
  Helper function: Check if all characters in string satisfy property P
*)
Fixpoint ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => P h /\ ForallChars P t
  end.

(*
  Precondition: problem_6_pre
*)
Definition problem_6_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (IsBalanced input).

Definition problem_6_spec (input : string) (output : list nat) : Prop :=
  output = parse_nested_parens_impl input.

(* Example Proof *)
Example test_problem_6 : problem_6_spec "(()()(((())))(()(())(((())(()(()))((()()))))(()(()))((()()))))()" [7].
Proof.
  (* Unfold the specification definition *)
  unfold problem_6_spec.
  
  (* Unfold the implementation to expose the logic *)
  unfold parse_nested_parens_impl.
  
  (* 
     Use reflexivity. 
     Since the input string is constant and the functions are computable,
     Coq can simplify the Right Hand Side (RHS) by evaluating 
     SplitOnSpaces and MaxDepth.
  *)
  reflexivity.
Qed.