Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Lia.
Import ListNotations.

(* 空格字符 *)
Definition space : ascii := Ascii.ascii_of_nat 32.

(* 判断是否为英文字母 (A-Z 或 a-z) *)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

(* 判定：s 是否以单个字母作为最后的 token（最后字符是字母，且前一字符要么不存在要么是空格） *)
Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists pre c,
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists pre', pre = pre' ++ [space]).

(* 任意字符列表均可 *)
Definition problem_134_pre (s : string) : Prop := True.

(* 最终 Spec：输入 s，输出 b。当且仅当 ends_with_single_letter_pred s 成立时返回 true。 *)
Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

Lemma space_neq_l : space <> "l"%char.
Proof.
  unfold space.
  intro H.
  compute in H.
  discriminate H.
Qed.

(* Main lemma: apple doesn't end with single letter *)
Lemma apple_not_single_letter : ~ ends_with_single_letter_pred "apple".
Proof.
  unfold ends_with_single_letter_pred.
  simpl.
  intros [pre [c [Heq [Halpha Hpre]]]].
  destruct Hpre as [Hpre_empty | [pre' Hpre_space]].
  - (* pre = [] case *)
    subst pre. simpl in Heq. discriminate Heq.
  - (* pre = pre' ++ [space] case *)
    subst pre.
    (* Heq: ["a"; "p"; "p"; "l"; "e"] = (pre' ++ [space]) ++ [c] *)
    (* The second-to-last character of "apple" is "l", not space *)
    assert (Hlen: length (["a"%char; "p"%char; "p"%char; "l"%char; "e"%char]) = 
                  length ((pre' ++ [space]) ++ [c])).
    { rewrite Heq. reflexivity. }
    rewrite app_length in Hlen. simpl in Hlen.
    rewrite app_length in Hlen. simpl in Hlen.
    assert (Hpre'_len: length pre' = 3) by lia.
    (* Now we know pre' has length 3 *)
    destruct pre' as [|a0 pre0]; [simpl in Hpre'_len; lia|].
    destruct pre0 as [|a1 pre1]; [simpl in Hpre'_len; lia|].
    destruct pre1 as [|a2 pre2]; [simpl in Hpre'_len; lia|].
    destruct pre2 as [|a3 pre3]; [|simpl in Hpre'_len; lia].
    (* Now pre' = [a0; a1; a2] *)
    simpl in Heq.
    inversion Heq as [[Ha0 Hrest]].
    inversion Hrest as [[Ha1 Hrest2]].
    inversion Hrest2 as [[Ha2 Hrest3]].
    inversion Hrest3 as [[Hspace Hc]].
    (* Hspace says space = "l"%char, which is false *)
    apply space_neq_l. exact Hspace.
Qed.

Example test_apple : problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - intros H. discriminate H.
  - intros H. exfalso. apply apple_not_single_letter. exact H.
Qed.