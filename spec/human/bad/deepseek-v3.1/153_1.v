(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* 定义：检查一个字符是否为大写字母 *)
Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

(* 定义：检查一个字符是否为小写字母 *)
Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

(* 辅助函数：计算列表中满足特定谓词的字符数量 *)
Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

(* 定义：计算一个扩展名的"力量值" *)
Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

(*
  谓词：is_strongest best exts
  该谓词为真，当且仅当 'best' 是列表 'exts' 中的最强扩展。
*)
Definition is_strongest (best : string) (exts : list string) : Prop :=
  exists prefix post,
    exts = prefix ++ best :: post /\
    ~ In best prefix /\
    (forall e, In e prefix -> (strength e < strength best)) /\
    (forall e, In e post -> (strength e <= strength best)).

(* 程序规约 *)
Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False
  | _ :: _ => 
      exists strongest_ext,
        is_strongest strongest_ext extensions /\
        res = append class_name (append "." strongest_ext)
  end.

(* 字符串连接辅助函数 *)
Definition append (s1 s2 : string) : string :=
  match s1, s2 with
  | EmptyString, s => s
  | String c s, s2' => String c (append s s2')
  end.

(* 计算字符串强度值的辅助引理 *)
Lemma strength_values:
  strength "tEN" = (-1 : Z) /\
  strength "niNE" = (-4 : Z) /\
  strength "eIGHt8OKe" = (4 : Z).
Proof.
  unfold strength, count_pred, is_uppercase, is_lowercase.
  simpl.
  repeat split; reflexivity.
Qed.

(* 测试用例的证明 *)
Example test_watashi : 
  problem_153_spec "Watashi" ["tEN"; "niNE"; "eIGHt8OKe"] (append "Watashi" (append "." "eIGHt8OKe")).
Proof.
  unfold problem_153_spec.
  
  (* 对于非空列表的情况 *)
  exists "eIGHt8OKe".
  split.
  
  (* 证明 is_strongest *)
  - unfold is_strongest.
    exists ["tEN"; "niNE"], [].
    repeat split.
    + reflexivity.  (* exts = prefix ++ best :: post *)
    + intro H.
      simpl in H.
      destruct H as [H1 | H2].
      * unfold String.eqb in H1.
        discriminate H1.  (* "eIGHt8OKe" ≠ "tEN" *)
      * destruct H2 as [H2 | H3].
        -- unfold String.eqb in H2.
           discriminate H2.  (* "eIGHt8OKe" ≠ "niNE" *)
        -- contradiction H3. (* 空列表 *)
    + intros e H.
      simpl in H.
      destruct H as [H1 | H2].
      * subst e.
        unfold strength, count_pred, is_uppercase, is_lowercase.
        simpl.
        lia.
      * destruct H2 as [H2 | H3].
        -- subst e.
           unfold strength, count_pred, is_uppercase, is_lowercase.
           simpl.
           lia.
        -- contradiction H3.
    + intros e H.
      contradiction H.
  
  (* 证明字符串连接 *)
  - reflexivity.
Qed.