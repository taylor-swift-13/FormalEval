Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition lparen : ascii := ascii_of_nat 40.
Definition rparen : ascii := ascii_of_nat 41.
Definition space : ascii := ascii_of_nat 32.

Fixpoint max_depth_aux (g : list ascii) (current_depth max_seen : nat) : nat :=
  match g with
  | [] => max_seen
  | h :: t =>
    if ascii_dec h lparen then
      let new_depth := S current_depth in
      max_depth_aux t new_depth (Nat.max max_seen new_depth)
    else if ascii_dec h rparen then
      max_depth_aux t (Nat.pred current_depth) max_seen
    else
      max_depth_aux t current_depth max_seen 
  end.

Definition MaxDepth (g : list ascii) : nat :=
  max_depth_aux g 0 0.

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : list ascii) : list (list ascii) :=
  match S with
  | [] =>
    match current_group with
    | [] => []
    | _ => [List.rev current_group]
    end
  | h :: t =>
    if ascii_dec h space then
      match current_group with
      | [] => SplitOnSpaces_aux [] t 
      | _ => (List.rev current_group) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : list ascii) : list (list ascii) :=
  SplitOnSpaces_aux [] S.

Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Fixpoint IsBalanced_aux (l : list ascii) (count : nat) : Prop :=
  match l with
  | [] => count = 0
  | h :: t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False 
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count 
  end.

Definition IsBalanced (l : list ascii) : Prop :=
  IsBalanced_aux l 0.
  
Fixpoint remove_spaces (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t =>
    if ascii_dec h space then
      remove_spaces t
    else
      h :: remove_spaces t
  end.

Definition separate_paren_groups_pre (input : list ascii) : Prop :=
  (Forall is_paren_or_space input) /\
  (IsBalanced (remove_spaces input)).

Definition parse_nested_parens_spec (input : list ascii) (output : list nat) : Prop :=
  output = List.map MaxDepth (SplitOnSpaces input).

Definition input : list ascii :=
  [lparen; rparen;
   space;
   lparen; lparen; rparen; rparen;
   space;
   lparen; lparen; lparen; rparen; rparen; rparen;
   space;
   lparen; lparen; lparen; lparen; rparen; rparen; rparen; rparen].

Definition output : list nat := [1; 2; 3; 4].

Example test_case : parse_nested_parens_spec input output.
Proof.
  unfold parse_nested_parens_spec, input, output, SplitOnSpaces, MaxDepth.
  cbn.
  reflexivity.
Qed.