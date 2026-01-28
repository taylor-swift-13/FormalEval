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

Definition problem_19_pre (input output : string) : Prop := True.

Definition problem_19_spec (input output : string) : Prop :=
    let input_list := SplitOnSpaces input in
    let output_list := SplitOnSpaces output in
    (*  输入列表中的所有单词都是有效的数字单词 *)
    Forall is_valid_word input_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.

Example test_two_zero_nine : problem_19_spec "two zero nine" "zero two nine".
Proof.
  unfold problem_19_spec.
  unfold SplitOnSpaces.
  simpl.
  split.
  - apply Forall_cons.
    + exists 2. constructor.
    + apply Forall_cons.
      * exists 0. constructor.
      * apply Forall_cons.
        -- exists 9. constructor.
        -- apply Forall_nil.
  - split.
    + apply perm_trans with (l' := ["zero"; "two"; "nine"]).
      * apply perm_swap.
      * apply Permutation_refl.
    + unfold IsSorted.
      intros i j Hij Hj s_i s_j n_i n_j Hi_eq Hj_eq Hwtn_i Hwtn_j.
      simpl in Hj.
      destruct i as [|i'].
      * simpl in Hi_eq.
        destruct j as [|j'].
        -- lia.
        -- destruct j' as [|j''].
           ++ simpl in Hj_eq.
              rewrite <- Hi_eq in Hwtn_i.
              rewrite <- Hj_eq in Hwtn_j.
              inversion Hwtn_i. inversion Hwtn_j. lia.
           ++ destruct j'' as [|j'''].
              ** simpl in Hj_eq.
                 rewrite <- Hi_eq in Hwtn_i.
                 rewrite <- Hj_eq in Hwtn_j.
                 inversion Hwtn_i. inversion Hwtn_j. lia.
              ** simpl in Hj. lia.
      * destruct i' as [|i''].
        -- simpl in Hi_eq.
           destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** lia.
              ** destruct j'' as [|j'''].
                 --- simpl in Hj_eq.
                     rewrite <- Hi_eq in Hwtn_i.
                     rewrite <- Hj_eq in Hwtn_j.
                     inversion Hwtn_i. inversion Hwtn_j. lia.
                 --- simpl in Hj. lia.
        -- destruct i'' as [|i'''].
           ++ simpl in Hi_eq.
              destruct j as [|j'].
              ** lia.
              ** destruct j' as [|j''].
                 --- lia.
                 --- destruct j'' as [|j'''].
                     +++ lia.
                     +++ simpl in Hj. lia.
           ++ simpl in Hj. lia.
Qed.