Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.

Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.
Definition space : ascii := " "%char.

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
      | 0 => False
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count
  end.

Definition IsBalanced (l : string) : Prop :=
  IsBalanced_aux l 0%nat.
  
Definition parse_nested_parens_impl (input : string) : list nat :=
  List.map MaxDepth (SplitOnSpaces input).

Fixpoint ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => P h /\ ForallChars P t
  end.

Definition problem_6_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (IsBalanced input).

Definition problem_6_spec (input : string) (output : list nat) : Prop :=
  output = parse_nested_parens_impl input.

Example parse_nested_parens_test_nat :
  parse_nested_parens_impl "()()()()()" = [1].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example parse_nested_parens_test_Z :
  List.map Z.of_nat (parse_nested_parens_impl "()()()()()")
  = [1%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example problem_6_spec_example :
  problem_6_spec "()()()()()" [1].
Proof.
  unfold problem_6_spec.
  vm_compute.
  reflexivity.
Qed.