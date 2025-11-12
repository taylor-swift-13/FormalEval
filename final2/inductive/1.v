(*Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings and return the list of those.
Separate groups are balanced (each open brace is properly closed) and not nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups('( ) (( )) (( )( ))')
['()', '(())', '(()())'] *)

(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

Inductive IsBalanced_aux_rel : list ascii -> nat -> Prop :=
  | ibar_nil : forall count, count = 0 -> IsBalanced_aux_rel [] count
  | ibar_lparen : forall h t count,
      h = lparen ->
      IsBalanced_aux_rel t (S count) ->
      IsBalanced_aux_rel (h :: t) count
  | ibar_rparen : forall h t count n',
      h = rparen ->
      count = S n' ->
      IsBalanced_aux_rel t n' ->
      IsBalanced_aux_rel (h :: t) count
  | ibar_other : forall h t count,
      h <> lparen ->
      h <> rparen ->
      IsBalanced_aux_rel t count ->
      IsBalanced_aux_rel (h :: t) count.

Definition IsBalanced (l : list ascii) : Prop :=
  IsBalanced_aux_rel l 0.

Definition IsMinimalBalanced (l : list ascii) : Prop :=
  IsBalanced l /\
  ~ (exists l1 l2,
       l1 <> [] /\
       l2 <> [] /\
       l = l1 ++ l2 /\
       IsBalanced l1 /\
       IsBalanced l2).

Inductive remove_spaces_rel : list ascii -> list ascii -> Prop :=
  | rsr_nil : remove_spaces_rel [] []
  | rsr_space : forall h t res,
      h = space ->
      remove_spaces_rel t res ->
      remove_spaces_rel (h :: t) res
  | rsr_char : forall h t res,
      h <> space ->
      remove_spaces_rel t res ->
      remove_spaces_rel (h :: t) (h :: res).

Inductive separate_paren_groups_aux_rel : list ascii -> nat -> list ascii -> list (list ascii) -> list (list ascii) -> Prop :=
  | spgar_nil_empty : forall acc, separate_paren_groups_aux_rel [] 0 [] acc acc
  | spgar_nil_nonempty : forall current acc, current <> [] -> separate_paren_groups_aux_rel [] 0 current acc (acc ++ [List.rev current])
  | spgar_lparen : forall h t count current acc result,
      h = lparen ->
      separate_paren_groups_aux_rel t (S count) (h :: current) acc result ->
      separate_paren_groups_aux_rel (h :: t) count current acc result
  | spgar_rparen_zero : forall h t count current acc result,
      h = rparen ->
      count = 0 ->
      separate_paren_groups_aux_rel t count current acc result ->
      separate_paren_groups_aux_rel (h :: t) count current acc result
  | spgar_rparen_minimal : forall h t n' current acc result,
      h = rparen ->
      n' = 0 ->
      separate_paren_groups_aux_rel t 0 [] (acc ++ [List.rev (h :: current)]) result ->
      separate_paren_groups_aux_rel (h :: t) (S n') current acc result
  | spgar_rparen_nonminimal : forall h t n' current acc result,
      h = rparen ->
      n' <> 0 ->
      separate_paren_groups_aux_rel t n' (h :: current) acc result ->
      separate_paren_groups_aux_rel (h :: t) (S n') current acc result
  | spgar_space : forall h t count current acc result,
      h = space ->
      separate_paren_groups_aux_rel t count current acc result ->
      separate_paren_groups_aux_rel (h :: t) count current acc result
  | spgar_other : forall h t count current acc result,
      h <> lparen -> h <> rparen -> h <> space ->
      separate_paren_groups_aux_rel t count (h :: current) acc result ->
      separate_paren_groups_aux_rel (h :: t) count current acc result.


Definition separate_paren_groups_spec (input : list ascii) (output : list (list ascii)) : Prop :=
  exists input_no_spaces,
    remove_spaces_rel input input_no_spaces /\
    separate_paren_groups_aux_rel input_no_spaces 0 [] [] output.
