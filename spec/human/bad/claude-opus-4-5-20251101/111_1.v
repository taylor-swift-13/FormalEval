Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 辅助函数：过滤掉空格 *)
Definition filter_spaces (l : list ascii) : list ascii :=
  filter (fun c => if ascii_dec c " "%char then false else true) l.

(* 辅助函数：计算字符在列表中的出现次数 *)
Definition count_char (letters : list ascii) (c : ascii) : nat :=
  count_occ ascii_dec letters c.

(* 辅助函数：计算列表中出现次数最多的次数 *)
Definition get_max_count (letters : list ascii) : nat :=
  let unique_letters := nodup ascii_dec letters in
  let counts := map (count_char letters) unique_letters in
  fold_right max 0 counts.

(* 仅包含空格或小写字母 *)
Definition problem_111_pre (s : string) : Prop :=
  let letters := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in 97 <= n /\ n <= 122) letters.

(*
  程序规约 Spec
  输入：s : string (一个由字符组成的字符串)
  输出：res : list (ascii * nat) (一个由 (字符, 计数值) 对组成的列表)
*)
Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = [] (* 如果输入列表为空，则输出也为空 *)
  | _ :: _ => (* 如果列表不为空 *)
    let max_count := get_max_count letters in

    (*
      规约的核心：输出 res 必须精确地包含所有出现次数最多的字符及其计数值。
      这可以用两个方向的蕴含来表达。
    *)
    (* 1. "Soundness": 输出 res 中的每一个元素都必须是正确的。 *)
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char letters c = max_count) /\

    (* 2. "Completeness": 每一个符合条件的字符都必须出现在输出 res 中。 *)
    (forall c, In c unique_letters ->
      count_char letters c = max_count ->
      In (c, max_count) res)
  end.

(* First, let's compute what the values actually are *)
Definition test_input := "a b b a".
Definition test_letters := filter_spaces (list_ascii_of_string test_input).
Definition test_unique := nodup ascii_dec test_letters.
Definition test_max := get_max_count test_letters.

(* Test case: input = "a b b a", output = [('a', 2); ('b', 2)] *)
Example test_histogram_1 : problem_111_spec "a b b a" [("a"%char, 2); ("b"%char, 2)].
Proof.
  unfold problem_111_spec.
  unfold filter_spaces, list_ascii_of_string.
  simpl filter.
  unfold get_max_count.
  simpl nodup.
  unfold count_char.
  simpl count_occ.
  simpl map.
  simpl fold_right.
  split.
  - (* Soundness *)
    intros p Hin.
    simpl in Hin.
    destruct Hin as [Heq | [Heq | Hfalse]].
    + inversion Heq; subst. split; reflexivity.
    + inversion Heq; subst. split; reflexivity.
    + contradiction.
  - (* Completeness *)
    intros c Hin Hcount.
    simpl in Hin.
    simpl.
    destruct Hin as [Heq | [Heq | Hfalse]].
    + subst c. left. reflexivity.
    + subst c. right. left. reflexivity.
    + contradiction.
Qed.