Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.

(* Helper function to convert list of ascii to string *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: s => String c (string_of_list_ascii s)
  end.

(*
  定义一个从单词 (string) 到数字 (nat) 的关系。
*)
Inductive WordToNum : string -> nat -> Prop :=
  | wtn_zero  : WordToNum "zero" 0
  | wtn_one   : WordToNum "one" 1
  | wtn_two   : WordToNum "two" 2
  | wtn_three : WordToNum "three" 3
  | wtn_four  : WordToNum "four" 4
  | wtn_five  : WordToNum "five" 5
  | wtn_six   : WordToNum "six" 6
  | wtn_seven : WordToNum "seven" 7
  | wtn_eight : WordToNum "eight" 8
  | wtn_nine  : WordToNum "nine" 9.

(* 定义一个谓词，用于判断一个 string 是否是有效的数字单词 *)
Definition is_valid_word (s : string) : Prop :=
  exists n, WordToNum s n.

(*
  定义一个谓词，用于判断一个 string 列表是否已排序。
*)
Definition IsSorted (l : list string) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l "" = s_i ->
      nth j l "" = s_j ->
      WordToNum s_i n_i ->
      WordToNum s_j n_j ->
      (n_i <= n_j)%nat.

(* Define space character safely *)
Definition space : ascii := ascii_of_nat 32.

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
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition problem_19_spec (input output : string) : Prop :=
    let input_list := SplitOnSpaces input in
    let output_list := SplitOnSpaces output in
    (*  输入列表中的所有单词都是有效的数字单词 *)
    Forall is_valid_word input_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.

(* Proof for the test case input = "four two", output = "two four" *)
Example test_four_two : problem_19_spec "four two" "two four".
Proof.
  unfold problem_19_spec.
  (* Compute the split lists to simplify the goal to concrete lists *)
  compute.
  split.
  - (* Forall is_valid_word ["four"; "two"] *)
    repeat constructor.
    + exists 4; apply wtn_four.
    + exists 2; apply wtn_two.
  - split.
    + (* Permutation ["four"; "two"] ["two"; "four"] *)
      apply perm_swap.
    + (* IsSorted ["two"; "four"] *)
      unfold IsSorted.
      intros i j H_lt H_len s_i s_j n_i n_j H_nth_i H_nth_j H_wtn_i H_wtn_j.
      (* Determine i and j. Since length is 2, and i < j, only i=0, j=1 is possible. *)
      destruct i.
      * (* i = 0 *)
        destruct j.
        -- (* j = 0 *) lia. (* 0 < 0 contradiction *)
        -- (* j = 1 or j > 1 *)
           destruct j.
           ++ (* j = 1 *)
              (* Substitute the strings found by nth *)
              simpl in H_nth_i; rewrite <- H_nth_i in H_wtn_i.
              simpl in H_nth_j; rewrite <- H_nth_j in H_wtn_j.
              (* Invert WordToNum to get the numbers *)
              inversion H_wtn_i; subst.
              inversion H_wtn_j; subst.
              (* Check 2 <= 4 *)
              lia.
           ++ (* j > 1 *)
              simpl in H_len. lia.
      * (* i > 0 *)
        destruct j.
        -- lia.
        -- simpl in H_len. lia.
Qed.