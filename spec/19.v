(* """ Input is a space-delimited string of numberals from 'zero' to 'nine'.
Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
Return the string with numbers sorted from smallest to largest
>>> sort_numbers('three one five')
'one three five'
""" *)

(* Spec(input, output) :=

∃ input_list, output_list,
    split_by_space(input, input_list) ∧
    split_by_space(output, output_list) ∧
    IsPermutation(input_list, output_list) ∧
    IsSorted(output_list) *)


(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.

(* 导入列表表示法 *)
Import ListNotations.

(*
  定义一个从单词 (list ascii) 到数字 (nat) 的关系。
  我们通过 ("z" : ascii) 的方式为每个字符明确标注类型。
*)
Inductive WordToNum : list ascii -> nat -> Prop :=
  | wtn_zero  : WordToNum (("z" : ascii) :: ("e" : ascii) :: ("r" : ascii) :: ("o" : ascii) :: []) 0
  | wtn_one   : WordToNum (("o" : ascii) :: ("n" : ascii) :: ("e" : ascii) :: []) 1
  | wtn_two   : WordToNum (("t" : ascii) :: ("w" : ascii) :: ("o" : ascii) :: []) 2
  | wtn_three : WordToNum (("t" : ascii) :: ("h" : ascii) :: ("r" : ascii) :: ("e" : ascii) :: ("e" : ascii) :: []) 3
  | wtn_four  : WordToNum (("f" : ascii) :: ("o" : ascii) :: ("u" : ascii) :: ("r" : ascii) :: []) 4
  | wtn_five  : WordToNum (("f" : ascii) :: ("i" : ascii) :: ("v" : ascii) :: ("e" : ascii) :: []) 5
  | wtn_six   : WordToNum (("s" : ascii) :: ("i" : ascii) :: ("x" : ascii) :: []) 6
  | wtn_seven : WordToNum (("s" : ascii) :: ("e" : ascii) :: ("v" : ascii) :: ("e" : ascii) :: ("n" : ascii) :: []) 7
  | wtn_eight : WordToNum (("e" : ascii) :: ("i" : ascii) :: ("g" : ascii) :: ("h" : ascii) :: ("t" : ascii) :: []) 8
  | wtn_nine  : WordToNum (("n" : ascii) :: ("i" : ascii) :: ("n" : ascii) :: ("e" : ascii) :: []) 9.

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

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : list ascii) : list (list ascii) :=
  match S with
  | [] =>
    match current_group with
    | [] => []
    | _ => [List.rev current_group]
    end
  | h :: t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (List.rev current_group) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : list ascii) : list (list ascii) :=
  SplitOnSpaces_aux [] S.

Definition Spec (input output : list ascii) : Prop :=
    let input_list := SplitOnSpaces input in
    let output_list := SplitOnSpaces output in
    (*  输入列表中的所有单词都是有效的数字单词 *)
    Forall is_valid_word input_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.