(* """ Input is a space-delimited string of numberals from 'zero' to 'nine'.
Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
Return the string with numbers sorted from smallest to largest
>>> sort_numbers('three one five')
'one three five'
""" *)

(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Permutation.

(* 导入列表表示法 *)
Import ListNotations.

(*
  定义一个从单词 (list ascii) 到数字 (nat) 的关系。
*)
Inductive WordToNum : list ascii -> nat -> Prop :=
  | wtn_zero  : WordToNum (("z"%char : ascii) :: ("e"%char : ascii) :: ("r"%char : ascii) :: ("o"%char : ascii) :: []) 0
  | wtn_one   : WordToNum (("o"%char : ascii) :: ("n"%char : ascii) :: ("e"%char : ascii) :: []) 1
  | wtn_two   : WordToNum (("t"%char : ascii) :: ("w"%char : ascii) :: ("o"%char : ascii) :: []) 2
  | wtn_three : WordToNum (("t"%char : ascii) :: ("h"%char : ascii) :: ("r"%char : ascii) :: ("e"%char : ascii) :: ("e"%char : ascii) :: []) 3
  | wtn_four  : WordToNum (("f"%char : ascii) :: ("o"%char : ascii) :: ("u"%char : ascii) :: ("r"%char : ascii) :: []) 4
  | wtn_five  : WordToNum (("f"%char : ascii) :: ("i"%char : ascii) :: ("v"%char : ascii) :: ("e"%char : ascii) :: []) 5
  | wtn_six   : WordToNum (("s"%char : ascii) :: ("i"%char : ascii) :: ("x"%char : ascii) :: []) 6
  | wtn_seven : WordToNum (("s"%char : ascii) :: ("e"%char : ascii) :: ("v"%char : ascii) :: ("e"%char : ascii) :: ("n"%char : ascii) :: []) 7
  | wtn_eight : WordToNum (("e"%char : ascii) :: ("i"%char : ascii) :: ("g"%char : ascii) :: ("h"%char : ascii) :: ("t"%char : ascii) :: []) 8
  | wtn_nine  : WordToNum (("n"%char : ascii) :: ("i"%char : ascii) :: ("n"%char : ascii) :: ("e"%char : ascii) :: []) 9.

(* 定义一个谓词，用于判断一个 ASCII 列表是否是有效的数字单词 *)
Definition is_valid_word (s : list ascii) : Prop :=
  exists n, WordToNum s n.

(*
  定义一个谓词，用于判断一个 ASCII 列表的列表是否已排序。
*)
Definition IsSorted (l : list (list ascii)) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l [] = s_i ->
      nth j l [] = s_j ->
      WordToNum s_i n_i ->
      WordToNum s_j n_j ->
      (n_i <= n_j)%nat.

Inductive SplitOnSpaces_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group [] []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group [] [List.rev current_group]
  | sosar_space_empty : forall current_group h t result,
      h = " "%char ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = " "%char ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) ((List.rev current_group) :: result)
  | sosar_char : forall current_group h t result,
      h <> " "%char ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result.

Inductive SplitOnSpaces_rel : list ascii -> list (list ascii) -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.

Inductive insert_sorted_rel : list ascii -> list (list ascii) -> list (list ascii) -> Prop :=
  | isr_nil : forall w, insert_sorted_rel w [] [w]
  | isr_le : forall w h t n1 n2,
      WordToNum w n1 ->
      WordToNum h n2 ->
      (n1 <= n2)%nat ->
      insert_sorted_rel w (h :: t) (w :: h :: t)
  | isr_gt : forall w h t result n1 n2,
      WordToNum w n1 ->
      WordToNum h n2 ->
      (n1 > n2)%nat ->
      insert_sorted_rel w t result ->
      insert_sorted_rel w (h :: t) (h :: result)
  | isr_invalid : forall w h t result,
      ~ (exists n, WordToNum w n) \/ ~ (exists n, WordToNum h n) ->
      insert_sorted_rel w t result ->
      insert_sorted_rel w (h :: t) (h :: result).

Inductive sort_words_rel : list (list ascii) -> list (list ascii) -> Prop :=
  | swr_nil : sort_words_rel [] []
  | swr_cons : forall h t sorted_tail result,
      sort_words_rel t sorted_tail ->
      insert_sorted_rel h sorted_tail result ->
      sort_words_rel (h :: t) result.

(* 用单个空格拼接单词列表（无尾随空格） *)
Inductive join_with_single_spaces_rel : list (list ascii) -> list ascii -> Prop :=
  | jwss_nil : join_with_single_spaces_rel [] []
  | jwss_single : forall w, join_with_single_spaces_rel [w] w
  | jwss_cons : forall w rest out_rest,
      join_with_single_spaces_rel rest out_rest ->
      join_with_single_spaces_rel (w :: rest) (w ++ [" "%char] ++ out_rest).


Definition Spec (input output : list ascii) : Prop :=
  exists words sorted_words,
    SplitOnSpaces_rel input words /\
    sort_words_rel words sorted_words /\
    join_with_single_spaces_rel sorted_words output.
