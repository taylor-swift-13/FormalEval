Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Convert a Coq string to a list of its characters. *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a s' => a :: list_ascii_of_string s'
  end.

(* 辅助函数：过滤掉空格 *)
Definition filter_spaces (l : list ascii) : list ascii :=
  filter (fun c => negb (ascii_dec c " "%char)) l.

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

(* Spec definition *)
Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = [] (* 如果输入列表为空，则输出也为空 *)
  | _ :: _ => (* 如果列表不为空 *)
    let max_count := get_max_count letters in
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char letters c = max_count) /\
    (forall c, In c unique_letters ->
      count_char letters c = max_count ->
      In (c, max_count) res)
  end.

(* Test case *)
Example test_problem_111:
  problem_111_spec "a b b a" [('a', 2); ('b', 2)].
Proof.
  unfold problem_111_spec.
  simpl.
  split.
  - intros [c n] [H1|[H2|H3]]; simpl in *; subst; split; reflexivity.
  - intros c H1 H2.
    simpl in H1.
    destruct H1 as [H1|[H1|H1]]; subst; simpl in H2.
    + left. reflexivity.
    + right. left. reflexivity.
    + contradiction.
Qed.