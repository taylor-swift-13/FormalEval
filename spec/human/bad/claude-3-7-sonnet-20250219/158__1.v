(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Open Scope string_scope.

(* 字典序比较 *)
Inductive string_le_rel : string -> string -> Prop :=
| slr_empty : forall s, string_le_rel EmptyString s
| slr_lt : forall c1 s1 c2 s2,
    Nat.lt (nat_of_ascii c1) (nat_of_ascii c2) ->
    string_le_rel (String c1 s1) (String c2 s2)
| slr_eq : forall c s1 s2,
    string_le_rel s1 s2 ->
    string_le_rel (String c s1) (String c s2).

(* 字符是否出现在字符串中 *)
Inductive string_contains_rel (c : ascii) : string -> Prop :=
| scr_head : forall s, string_contains_rel c (String c s)
| scr_tail : forall x s, string_contains_rel c s -> string_contains_rel c (String x s).

(* 计算字符串中唯一字符数 *)
Inductive count_unique_chars_rel : string -> nat -> Prop :=
| cucr_empty : count_unique_chars_rel EmptyString 0
| cucr_seen : forall c s n,
    string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) n
| cucr_new : forall c s n,
    ~ string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) (S n).

(* 输入单词列表需非空 *)
Definition problem_158_pre (words : list string) : Prop := words <> [].

(* find_max 规约 *)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    exists c_res c_w,
      count_unique_chars_rel result c_res /\
      count_unique_chars_rel w c_w /\
      (c_res > c_w \/ (c_res = c_w /\ string_le_rel result w)).

(* ascii_eqb 定义，避免之前 Nat.eq_dec 类型不匹配 *)
Definition ascii_eqb (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).

(* 将字符串转成ascii列表 *)
Fixpoint list_ascii_of_string (s: string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* ascii是否在列表中 *)
Fixpoint ascii_in_list (a : ascii) (l : list ascii) : bool :=
  match l with
  | [] => false
  | h :: t => if ascii_eqb a h then true else ascii_in_list a t
  end.

(* 计算唯一字符数量的函数 *)
Fixpoint count_unique_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
    if ascii_in_list c (list_ascii_of_string s')
    then count_unique_chars s'
    else 1 + count_unique_chars s'
  end.

(* ascii_eqb 与 ascii相等的连接 *)
Lemma ascii_eqb_eq : forall a b,
  ascii_eqb a b = true <-> a = b.
Proof.
  intros a b.
  unfold ascii_eqb.
  rewrite Nat.eqb_eq.
  split; intros H; subst; reflexivity.
Qed.

(* ascii_in_list为true时，说明字符在字符串中 *)
Lemma ascii_in_list_string_contains_rel : forall c s,
  ascii_in_list c (list_ascii_of_string s) = true -> string_contains_rel c s.
Proof.
  induction s as [| ch s' IH]; simpl; intros H.
  - discriminate.
  - simpl in H.
    destruct (ascii_eqb c ch) eqn:Heq.
    + apply ascii_eqb_eq in Heq. subst. constructor.
    + constructor 2. apply IH. assumption.
Qed.

(* ascii_in_list为false时，字符串不包含该字符 *)
Lemma ascii_in_list_not_string_contains_rel : forall c s,
  ascii_in_list c (list_ascii_of_string s) = false -> ~ string_contains_rel c s.
Proof.
  induction s as [| ch s' IH]; simpl; intros H Hcont.
  - inversion Hcont.
  - simpl in H.
    destruct (ascii_eqb c ch) eqn:Heq.
    + discriminate.
    + inversion Hcont; subst.
      * apply ascii_eqb_eq in Heq. congruence.
      * apply IH in H. contradiction.
Qed.

(* count_unique_chars计算值与count_unique_chars_rel对应 *)
Lemma count_unique_chars_rel_correct : forall s n,
  count_unique_chars s = n ->
  count_unique_chars_rel s n.
Proof.
  induction s as [| c s' IH]; simpl; intros n Hn.
  - inversion Hn. constructor.
  - remember (ascii_in_list c (list_ascii_of_string s')) as b eqn:Heqb.
    destruct b eqn:B.
    + apply ascii_in_list_string_contains_rel in Heqb.
      apply IH in Hn.
      constructor 2; assumption.
    + apply ascii_in_list_not_string_contains_rel in Heqb.
      apply IH in Hn.
      constructor 3; assumption.
Qed.

(* 字符串字典序自反 *)
Lemma string_le_rel_refl : forall s, string_le_rel s s.
Proof.
  induction s.
  - constructor.
  - constructor. assumption.
Qed.

(* 证明示例 *)
Example problem_158_example_1 :
  problem_158_spec ["name"; "of"; "string"] "string".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. auto.
  - intros w Hw.
    simpl in Hw.
    destruct Hw as [Hw | [Hw | Hw]]; subst.
    + exists (count_unique_chars "string"), (count_unique_chars "name").
      split.
      * apply count_unique_chars_rel_correct, eq_refl.
      * split.
        -- apply count_unique_chars_rel_correct, eq_refl.
        -- left.
           unfold count_unique_chars; simpl.
           (* string unique chars = 6, name unique chars = 4 *)
           lia.
    + exists (count_unique_chars "string"), (count_unique_chars "of").
      split.
      * apply count_unique_chars_rel_correct, eq_refl.
      * split.
        -- apply count_unique_chars_rel_correct, eq_refl.
        -- left.
           unfold count_unique_chars; simpl.
           (* string unique chars = 6, of unique chars = 2 *)
           lia.
    + exists (count_unique_chars "string"), (count_unique_chars "string").
      split.
      * apply count_unique_chars_rel_correct, eq_refl.
      * split.
        -- apply count_unique_chars_rel_correct, eq_refl.
        -- right.
           split; [reflexivity | apply string_le_rel_refl].
Qed.