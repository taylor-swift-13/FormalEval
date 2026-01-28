Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.

Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

Definition string_of_list_ascii (l : list ascii) : string :=
  List.fold_right (fun c s => String c s) EmptyString l.

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
      max_depth_aux t current_depth max_seen
  end.

Definition MaxDepth (g : string) : nat :=
  max_depth_aux g 0 0.

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
      | [] => SplitOnSpaces_aux [] t
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition parse_nested_parens_impl (input : string) : list nat :=
  List.map MaxDepth (SplitOnSpaces input).

Example test_parse_nested_parens :
  parse_nested_parens_impl "()(((())))" = [4].
Proof.
  unfold parse_nested_parens_impl.
  unfold SplitOnSpaces.
  simpl.
  unfold SplitOnSpaces_aux.
  simpl.
  repeat (match goal with
          | |- context [ascii_dec ?x ?y] => 
              destruct (ascii_dec x y); try congruence; simpl
          end).
  unfold MaxDepth.
  unfold max_depth_aux.
  simpl.
  reflexivity.
Qed.