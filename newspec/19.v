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
Require Import Coq.Bool.Bool.
Require Import Permutation.

(* 导入列表表示法 *)
Import ListNotations.

(*
  定义一个从单词 (list ascii) 到数字 (nat) 的关系。
  我们通过 ("z"%char : ascii) 的方式为每个字符明确标注类型。
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

Definition z_char : ascii := "z"%char.
Definition e_char : ascii := "e"%char.
Definition r_char : ascii := "r"%char.
Definition o_char : ascii := "o"%char.
Definition n_char : ascii := "n"%char.
Definition t_char : ascii := "t"%char.
Definition w_char : ascii := "w"%char.
Definition h_char : ascii := "h"%char.
Definition f_char : ascii := "f"%char.
Definition i_char : ascii := "i"%char.
Definition v_char : ascii := "v"%char.
Definition s_char : ascii := "s"%char.
Definition x_char : ascii := "x"%char.
Definition g_char : ascii := "g"%char.
Definition u_char : ascii := "u"%char.

Definition word_to_nat_impl (word : list ascii) : option nat :=
  match word with
  | [] => None
  | c :: rest =>
      if Ascii.eqb c z_char then
        match rest with
        | [e; r; o] => if andb (andb (Ascii.eqb e e_char) (Ascii.eqb r r_char)) (Ascii.eqb o o_char) then Some 0 else None
        | _ => None
        end
      else if Ascii.eqb c o_char then
        match rest with
        | [n; e] => if andb (Ascii.eqb n n_char) (Ascii.eqb e e_char) then Some 1 else None
        | _ => None
        end
      else if Ascii.eqb c t_char then
        match rest with
        | [w; o] => if andb (Ascii.eqb w w_char) (Ascii.eqb o o_char) then Some 2 else None
        | [h; r; e; e'] => if andb (Ascii.eqb h h_char) (andb (Ascii.eqb r r_char) (andb (Ascii.eqb e e_char) (Ascii.eqb e' e_char))) then Some 3 else None
        | _ => None
        end
      else if Ascii.eqb c f_char then
        match length rest with
        | 3 =>
            match rest with
            | [c1; c2; c3] =>
                if andb (Ascii.eqb c1 o_char) (andb (Ascii.eqb c2 u_char) (Ascii.eqb c3 r_char)) then Some 4
                else if andb (Ascii.eqb c1 i_char) (andb (Ascii.eqb c2 v_char) (Ascii.eqb c3 e_char)) then Some 5
                else None
            | _ => None
            end
        | _ => None
        end
      else if Ascii.eqb c s_char then
        match rest with
        | [i; x] => if andb (Ascii.eqb i i_char) (Ascii.eqb x x_char) then Some 6 else None
        | [e; v; e'; n] => if andb (Ascii.eqb e e_char) (andb (Ascii.eqb v v_char) (andb (Ascii.eqb e' e_char) (Ascii.eqb n n_char))) then Some 7 else None
        | _ => None
        end
      else if Ascii.eqb c e_char then
        match rest with
        | [i; g; h; t] => if andb (Ascii.eqb i i_char) (andb (Ascii.eqb g g_char) (andb (Ascii.eqb h h_char) (Ascii.eqb t t_char))) then Some 8 else None
        | _ => None
        end
      else if Ascii.eqb c n_char then
        match rest with
        | [i; n'; e] => if andb (Ascii.eqb i i_char) (andb (Ascii.eqb n' n_char) (Ascii.eqb e e_char)) then Some 9 else None
        | _ => None
        end
      else None
  end.

Fixpoint insert_sorted (w : list ascii) (words : list (list ascii)) : list (list ascii) :=
  match words with
  | [] => [w]
  | h :: t =>
      match word_to_nat_impl w, word_to_nat_impl h with
      | Some n1, Some n2 => if n1 <=? n2 then w :: words else h :: insert_sorted w t
      | _, _ => h :: insert_sorted w t
      end
  end.

Fixpoint sort_words (words : list (list ascii)) : list (list ascii) :=
  match words with
  | [] => []
  | h :: t => insert_sorted h (sort_words t)
  end.

Fixpoint sort_numbers_impl (input : list ascii) : list ascii :=
  let words := SplitOnSpaces input in
  let sorted_words := sort_words words in
  List.concat (List.map (fun w => w ++ [" "%char]) sorted_words).

(* Pre: no additional constraints for `sort_numbers` by default *)
Definition Pre (input : list ascii) : Prop := True.

Definition Spec (input output : list ascii) : Prop :=
  output = sort_numbers_impl input.
