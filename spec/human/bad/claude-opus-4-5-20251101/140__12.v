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

  (* 规则3: 输入以单个空格开头 (即下一个字符不是空格，或已到列表末尾)。
     该空格被替换为下划线。 *)
  | fsr_single_space (i' o' : list ascii):
      (match i' with
       | [] => True
       | c :: _ => c <> space
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: i') (underscore :: o')

  (* 规则4: 输入以至少两个空格开头。
     输出一个破折号，并跳过所有连续的前导空格，然后对其余列表应用关系。 *)
  | fsr_multi_space (i_after_2_spaces i_rem o' : list ascii):
      (* i_after_2_spaces 是紧跟在头两个空格后的子列表 *)
      (* i_rem 是 i_after_2_spaces 跳过其所有前导空格后的结果 *)
      skip_leading_spaces i_after_2_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: i_after_2_spaces) (dash :: o').

(* 输入文本任意 *)
Definition problem_140_pre (s : string) : Prop := True.
(*
  程序规约 (Spec)
  它断言输入列表和输出列表必须满足 `fix_spaces_relation` 所定义的关系。
*)
Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

Lemma T_not_space : "T"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma e_not_space : "e"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma s_not_space : "s"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma t_not_space : "t"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma i_not_space : "i"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma n_not_space : "n"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma g_not_space : "g"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma one_not_space : "1"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma two_not_space : "2"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma three_not_space : "3"%char <> space.
Proof. unfold space. discriminate. Qed.

Example test_testing_1_2_3 : problem_140_spec "Testing     1  2   3" "Testing-1__2-3".
Proof.
  unfold problem_140_spec.
  simpl.
  apply fsr_non_space. exact T_not_space.
  apply fsr_non_space. exact e_not_space.
  apply fsr_non_space. exact s_not_space.
  apply fsr_non_space. exact t_not_space.
  apply fsr_non_space. exact i_not_space.
  apply fsr_non_space. exact n_not_space.
  apply fsr_non_space. exact g_not_space.
  apply (fsr_multi_space [" "%char; " "%char; " "%char; "1"%char; " "%char; " "%char; "2"%char; " "%char; " "%char; " "%char; "3"%char]).
  - apply sls_space. apply sls_space. apply sls_space.
    apply sls_non_space. exact one_not_space.
  - apply fsr_non_space. exact one_not_space.
    apply fsr_single_space.
    + simpl. unfold space. discriminate.
    + apply fsr_single_space.
      * simpl. exact two_not_space.
      * apply fsr_non_space. exact two_not_space.
        apply (fsr_multi_space [" "%char; " "%char; "3"%char]).
        -- apply sls_space. apply sls_space.
           apply sls_non_space. exact three_not_space.
        -- apply fsr_non_space. exact three_not_space.
           apply fsr_nil.
Qed.