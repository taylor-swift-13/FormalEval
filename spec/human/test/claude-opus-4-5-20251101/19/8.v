(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Lia.

(* 导入列表表示法 *)
Import ListNotations.
Open Scope string_scope.

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

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition problem_19_pre (input : string) : Prop := True.

Definition problem_19_spec (input output : string) : Prop :=
    let input_list := SplitOnSpaces input in
    let output_list := SplitOnSpaces output in
    (*  输入列表中的所有单词都是有效的数字单词 *)
    Forall is_valid_word input_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.

Lemma WordToNum_functional : forall s n1 n2, WordToNum s n1 -> WordToNum s n2 -> n1 = n2.
Proof.
  intros s n1 n2 H1 H2.
  inversion H1; inversion H2; subst; try reflexivity; try discriminate.
Qed.

Example test_one_six_two_four_nine : problem_19_spec "one six two four nine" "one two four six nine".
Proof.
  unfold problem_19_spec.
  unfold SplitOnSpaces.
  simpl.
  split.
  - repeat constructor; unfold is_valid_word.
    + exists 1. constructor.
    + exists 6. constructor.
    + exists 2. constructor.
    + exists 4. constructor.
    + exists 9. constructor.
  - split.
    + apply perm_trans with (l' := ["one"; "two"; "six"; "four"; "nine"]).
      * apply perm_skip.
        apply perm_swap.
      * apply perm_trans with (l' := ["one"; "two"; "four"; "six"; "nine"]).
        -- apply perm_skip. apply perm_skip.
           apply perm_swap.
        -- apply Permutation_refl.
    + unfold IsSorted.
      intros i j Hij Hj s_i s_j n_i n_j Hi_eq Hj_eq Hwi Hwj.
      simpl in Hj.
      destruct i as [|[|[|[|[|i']]]]]; destruct j as [|[|[|[|[|j']]]]]; simpl in *; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
      * subst. inversion Hwi; inversion Hwj; subst; try discriminate; try lia.
Qed.