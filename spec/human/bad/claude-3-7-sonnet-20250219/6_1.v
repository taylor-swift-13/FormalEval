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

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | h :: t => String h (string_of_list_ascii t)
  end.

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
  IsBalanced_aux l 0.

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

Example test_parse_nested_parens :
  problem_6_pre "(()()) ((())) () ((())()())" /\
  problem_6_spec "(()()) ((())) () ((())()())" [2;3;1;3].
Proof.
  split.

  - unfold problem_6_pre.
    split.

    + (* ForallChars is_paren_or_space for the fixed string *)
      unfold ForallChars, is_paren_or_space.
      (* We prove by repeated constructor and destruct ascii_dec *)

      (* To avoid re-focusing issue later, we do a tactic with repeat *)
      (* Generate all characters for the string manually *)

      (* We write a Ltac to handle this large conjunction *)
      revert "(()()) ((())) () ((())()())".
      induction 1 as [| c s IH]; simpl; intros; try constructor.
      destruct (ascii_dec c lparen).
      * left; reflexivity.
      * destruct (ascii_dec c rparen).
        -- right; left; assumption.
        -- destruct (ascii_dec c space).
           ++ right; right; assumption.
           ++ (* No other chars in string *) discriminate.
      split; auto.

    + (* IsBalanced holds *)
      unfold IsBalanced.
      (* Use induction on input string with counter *)
      remember "(()()) ((())) () ((())()())" as s eqn:Hs.
      revert Hs.
      induction s as [| c s IH]; intros Hs count; simpl.
      * lia.
      * destruct (ascii_dec c lparen).
        -- apply IH with (count := S count).
           reflexivity.
        -- destruct (ascii_dec c rparen).
           ++ destruct count.
              ** discriminate.
              ** apply IH with (count := count).
                 reflexivity.
           ++ apply IH with count.
              reflexivity.

      specialize (IH _ eq_refl 0).
      assumption.

  - (* problem_6_spec *)

    unfold problem_6_spec, parse_nested_parens_impl, SplitOnSpaces.

    (* We unfold SplitOnSpaces_aux step by step for the input string *)
    (* The input: "(()()) ((())) () ((())()())" *)

    (* Assert the split result *)
    assert (Hsplit:
      SplitOnSpaces "(()()) ((())) () ((())()())" = ["(()())"; "((()))"; "()"; "((())()())"]).
    {
      unfold SplitOnSpaces, SplitOnSpaces_aux.
      reflexivity.
    }
    rewrite Hsplit.

    simpl.

    (* Now prove MaxDepth of each string *)

    assert (Hmd1 : MaxDepth "(()())" = 2).
    {
      unfold MaxDepth.
      simpl.
      reflexivity.
    }
    assert (Hmd2 : MaxDepth "((()))" = 3).
    {
      unfold MaxDepth.
      simpl.
      reflexivity.
    }
    assert (Hmd3 : MaxDepth "()" = 1).
    {
      unfold MaxDepth.
      simpl.
      reflexivity.
    }
    assert (Hmd4 : MaxDepth "((())()())" = 3).
    {
      unfold MaxDepth.
      simpl.
      reflexivity.
    }

    rewrite Hmd1, Hmd2, Hmd3, Hmd4.
    reflexivity.
Qed.