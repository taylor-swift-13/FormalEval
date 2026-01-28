Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.

(*
 * 辅助定义 1：is_space
 * 一个断言，当且仅当字符 c 是空格时为真。
 *)
Definition is_space (c : ascii) : Prop := c = " "%char.

(*
 * 辅助定义 2：is_sorted
 * 一个断言，当且仅当一个字符列表中的所有字符都根据其 ASCII 值按升序排列时为真。
 *)
Inductive is_sorted : string -> Prop :=
  | sorted_nil : is_sorted ""
  | sorted_one : forall c, is_sorted (String c "")
  | sorted_cons : forall c1 c2 s',
      nat_of_ascii c1 <= nat_of_ascii c2 ->
      is_sorted (String c2 s') ->
      is_sorted (String c1 (String c2 s')).

(*
 * 辅助定义 3：SplitOnSpaces_rel
 * 将字符串按空格分割成单词列表。
 *)
Inductive SplitOnSpaces_aux_rel : string -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = "" -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> "" -> SplitOnSpaces_aux_rel current_group "" [current_group]
  | sosar_space_empty : forall current_group h t result,
      is_space h ->
      current_group = "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      is_space h ->
      current_group <> "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) (current_group :: result)
  | sosar_char : forall current_group h t result,
      ~ is_space h ->
      SplitOnSpaces_aux_rel (current_group ++ String h "") t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall s result, SplitOnSpaces_aux_rel "" s result -> SplitOnSpaces_rel s result.


Definition problem_86_pre (s : string) : Prop := True.

(*
 * 程序规约：anti_shuffle_spec
 *
 * 这个规约定义了输入列表 's' 和输出列表 's_out' 必须满足的关系。
 * 它由三个核心属性构成。
 *)
Definition  problem_86_spec (s s_out : string) : Prop :=
  (* 属性 1: 输出列表的长度必须与输入列表的长度完全相等。 *)
  String.length s = String.length s_out /\

  (* 属性 2: 空格和非空格字符的位置必须保持不变。
     也就是说，在任意一个位置 i，如果输入字符是空格，那么输出字符也必须是空格，反之亦然。 *)
  (forall i, i < String.length s ->
    forall c1 c2,
      String.get i s = Some c1 ->
      String.get i s_out = Some c2 ->
      (is_space c1 <-> is_space c2)) /\

  (* 属性 3: 使用 SplitOnSpaces 提取单词，并要求对应单词满足置换和排序关系。 *)
  (exists words_in words_out,
    SplitOnSpaces_rel s words_in /\
    SplitOnSpaces_rel s_out words_out /\
    Forall2 (fun w_in w_out => Permutation (list_ascii_of_string w_in) (list_ascii_of_string w_out) /\ is_sorted w_out) words_in words_out).

Example test_case_86 : problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec.
  repeat split.
  
  (* 1. Proof of Length Equality *)
  - reflexivity.

  (* 2. Proof of Space Preservation *)
  - intros i Hlen c1 c2 Hget1 Hget2.
    (* Since s and s_out are identical, c1 must equal c2 *)
    rewrite Hget1 in Hget2.
    injection Hget2 as Heq.
    subst.
    (* Reflexivity holds for iff *)
    reflexivity.

  (* 3. Proof of Splitting and Sorting *)
  - exists ["Hi"], ["Hi"].
    repeat split.
    
    (* 3a. Proof that input "Hi" splits into ["Hi"] *)
    + apply sos_base.
      (* Process 'H' *)
      apply sosar_char.
      { unfold is_space. intro H. inversion H. }
      simpl.
      (* Process 'i' *)
      apply sosar_char.
      { unfold is_space. intro H. inversion H. }
      simpl.
      (* End of string *)
      apply sosar_nil_nonempty.
      intro H. discriminate.

    (* 3b. Proof that output "Hi" splits into ["Hi"] *)
    + apply sos_base.
      (* Process 'H' *)
      apply sosar_char.
      { unfold is_space. intro H. inversion H. }
      simpl.
      (* Process 'i' *)
      apply sosar_char.
      { unfold is_space. intro H. inversion H. }
      simpl.
      (* End of string *)
      apply sosar_nil_nonempty.
      intro H. discriminate.

    (* 3c. Proof of Permutation and Sorting *)
    + constructor.
      * split.
        (* Permutation holds by reflexivity *)
        { apply Permutation_refl. }
        (* Sortedness: 'H' (72) <= 'i' (105) *)
        { 
          apply sorted_cons.
          (* 72 <= 105 *)
          - compute. repeat constructor.
          (* Rest is sorted *)
          - apply sorted_one.
        }
      * constructor.
Qed.