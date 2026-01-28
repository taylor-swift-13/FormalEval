(* 导入列表和ASCII字符所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* 为清晰起见，定义字符常量 *)
Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

(*
  辅助关系: `skip_leading_spaces input remaining`
  这个关系为真，当且仅当 `remaining` 是 `input` 列表移除所有前导空格后的结果。
*)
Inductive skip_leading_spaces: list ascii -> list ascii -> Prop :=
  | sls_nil:
      skip_leading_spaces [] []
  | sls_non_space (c : ascii) (l : list ascii):
      c <> space ->
      skip_leading_spaces (c :: l) (c :: l)
  | sls_space (l l' : list ascii):
      skip_leading_spaces l l' ->
      skip_leading_spaces (space :: l) l'.

(*
  核心关系: `fix_spaces_relation input output`
  该关系通过一组构造规则，定义了输入列表和输出列表之间的合法转换。
  每一条规则都对应程序逻辑中的一个分支。
*)
Inductive fix_spaces_relation : list ascii -> list ascii -> Prop :=
  (* 规则1: 输入为空列表，则输出也必须为空列表。 *)
  | fsr_nil:
      fix_spaces_relation [] []

  (* 规则2: 输入以非空格字符 `c` 开头。
     输出也以 `c` 开头，然后对其余列表应用相同的关系。 *)
  | fsr_non_space (c : ascii) (i' o' : list ascii):
      c <> space ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (c :: i') (c :: o')

  (* 规则3: 输入以空格开头，但不是3个或更多连续空格的一部分。
     这包括单个空格的情况，或者两个连续空格的情况。
     如果是两个连续空格，该规则会应用两次，产生两个下划线。
     条件 `c1 <> space \/ c2 <> space` 确保了如果当前空格后面紧跟两个空格（即总共3个空格），则此规则不适用。 *)
  | fsr_single_space (i' o' : list ascii):
      (match i' with
       | c1 :: c2 :: _ => c1 <> space \/ c2 <> space
       | _ => True
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: i') (underscore :: o')

  (* 规则4: 输入以至少三个空格开头。
     输出一个破折号，并跳过所有连续的前导空格，然后对其余列表应用关系。 *)
  | fsr_multi_space (i_after_3_spaces i_rem o' : list ascii):
      (* i_after_3_spaces 是紧跟在头三个空格后的子列表 *)
      (* i_rem 是 i_after_3_spaces 跳过其所有前导空格后的结果 *)
      skip_leading_spaces i_after_3_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: space :: i_after_3_spaces) (dash :: o').

(* 输入文本任意 *)
Definition problem_140_pre (s : string) : Prop := True.
(*
  程序规约 (Spec)
  它断言输入列表和输出列表必须满足 `fix_spaces_relation` 所定义的关系。
*)
Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

(* Test case proof *)
Example test_fix_spaces_example : problem_140_spec "Testing     1  2   3" "Testing-1__2-3".
Proof.
  unfold problem_140_spec.
  simpl.
  
  (* Process "Testing" *)
  repeat (apply fsr_non_space; [ intro H; inversion H | ]).
  
  (* Process 5 spaces -> "-" *)
  eapply fsr_multi_space.
  { 
    (* Skip remaining 2 spaces *)
    apply sls_space.
    apply sls_space.
    apply sls_non_space.
    intro H. inversion H.
  }
  
  (* Process "1" *)
  apply fsr_non_space.
  { intro H. inversion H. }
  
  (* Process 2 spaces -> "__" *)
  (* First space *)
  apply fsr_single_space.
  { 
    (* Check lookahead: next is space, then '2'. space <> space \/ '2' <> space is True *)
    simpl. right. intro H. inversion H. 
  }
  (* Second space *)
  apply fsr_single_space.
  { 
    (* Check lookahead: next is '2', then space. '2' <> space \/ ... is True *)
    simpl. left. intro H. inversion H. 
  }
  
  (* Process "2" *)
  apply fsr_non_space.
  { intro H. inversion H. }
  
  (* Process 3 spaces -> "-" *)
  eapply fsr_multi_space.
  {
    (* Skip 0 spaces (next is '3') *)
    apply sls_non_space.
    intro H. inversion H.
  }
  
  (* Process "3" *)
  apply fsr_non_space.
  { intro H. inversion H. }
  
  (* End of string *)
  apply fsr_nil.
Qed.