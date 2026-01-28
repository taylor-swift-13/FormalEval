(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* 定义：sub 是 main 的子串 *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* 定义：r 是 b 的一个循环旋转 *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* 任意字符串输入，无额外约束 *)
Definition problem_154_pre (a b : string) : Prop := True.

(* cycpattern_check 函数的程序规约 *)
Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <-> (exists b', is_rotation_of b' lb /\ is_substring b' la).

Example test_cycpattern_check :
  problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec.
  simpl.
  split.
  - intros H.
    intros [b' [Hrot Hsub]].
    destruct Hrot as [p1 [p2 [H1 H2]]].
    destruct Hsub as [prefix [suffix Heq]].
    rewrite <- H2 in Heq.
    rewrite H1 in Heq.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    simpl in Heq.
    discriminate Heq.
  - intros H.
    exfalso.
    destruct H as [b' [Hrot Hsub]].
    destruct Hrot as [p1 [p2 [H1 H2]]].
    destruct Hsub as [prefix [suffix Heq]].
    rewrite <- H2 in Heq.
    rewrite H1 in Heq.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    simpl in Heq.
    discriminate Heq.
Qed.