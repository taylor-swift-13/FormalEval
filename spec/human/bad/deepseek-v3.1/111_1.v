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

Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = []
  | _ :: _ =>
    let max_count := get_max_count letters in
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char letters c = max_count) /\
    (forall c, In c unique_letters ->
      count_char letters c = max_count ->
      In (c, max_count) res)
  end.

(* 测试用例的实现 *)
Definition histogram_example : list (ascii * nat) :=
  [("a"%char, 2); ("b"%char, 2)].

Lemma test_case_proof :
  problem_111_spec "a b b a"%string histogram_example.
Proof.
  unfold problem_111_spec, histogram_example.
  simpl.
  
  (* 计算 letters *)
  unfold filter_spaces.
  simpl.
  
  (* 计算 unique_letters *)
  unfold nodup.
  simpl.
  
  (* 计算 count_char 和 max_count *)
  unfold count_char, get_max_count.
  simpl.
  
  (* 分割证明目标 *)
  split.
  - (* 第一部分：Soundness *)
    intros p H.
    destruct H as [H|H].
    + (* p = ("a", 2) *)
      simpl in H.
      destruct H.
      simpl.
      split; reflexivity.
      contradiction.
    + destruct H as [H|H].
      * (* p = ("b", 2) *)
        simpl in H.
        destruct H.
        simpl.
        split; reflexivity.
        contradiction.
      * (* 空情况 *)
        contradiction.
  - (* 第二部分：Completeness *)
    intros c H Hcount.
    destruct H as [H|H].
    + (* c = "a" *)
      simpl in H.
      destruct H.
      left. reflexivity.
      contradiction.
    + destruct H as [H|H].
      * (* c = "b" *)
        simpl in H.
        destruct H.
        right. left. reflexivity.
        contradiction.
      * (* 空情况 *)
        contradiction.
Qed.