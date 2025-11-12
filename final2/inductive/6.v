(* Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens('(()()) ((())) () ((())()())')
[2, 3, 1, 3] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.

(* 定义 '(' 和 ')' 和 ' ' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

Inductive max_depth_aux_rel : list ascii -> nat -> nat -> nat -> Prop :=
  | mdar_nil : forall current_depth max_seen, max_depth_aux_rel [] current_depth max_seen max_seen
  | mdar_lparen : forall h t current_depth max_seen new_depth new_max result,
      h = lparen ->
      new_depth = S current_depth ->
      new_max = Nat.max max_seen new_depth ->
      max_depth_aux_rel t new_depth new_max result ->
      max_depth_aux_rel (h :: t) current_depth max_seen result
  | mdar_rparen : forall h t current_depth max_seen result,
      h = rparen ->
      max_depth_aux_rel t (Nat.pred current_depth) max_seen result ->
      max_depth_aux_rel (h :: t) current_depth max_seen result
  | mdar_other : forall h t current_depth max_seen result,
      h <> lparen ->
      h <> rparen ->
      max_depth_aux_rel t current_depth max_seen result ->
      max_depth_aux_rel (h :: t) current_depth max_seen result.

Inductive MaxDepth_rel : list ascii -> nat -> Prop :=
  | md_base : forall g result, max_depth_aux_rel g 0 0 result -> MaxDepth_rel g result.

Inductive SplitOnSpaces_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group [] []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group [] [List.rev current_group]
  | sosar_space_empty : forall current_group h t result,
      h = space ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = space ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) ((List.rev current_group) :: result)
  | sosar_char : forall current_group h t result,
      h <> space ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result.

Inductive SplitOnSpaces_rel : list ascii -> list (list ascii) -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.


Definition parse_nested_parens_spec (input : list ascii) (output : list nat) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    length output = length groups /\
    (forall i, i < length groups -> MaxDepth_rel (nth i groups []) (nth i output 0)).
