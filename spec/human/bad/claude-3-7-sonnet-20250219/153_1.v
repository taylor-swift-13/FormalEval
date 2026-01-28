(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

(*
  修正：
  Coq中::的优先级导致表达式最好明确加括号表示最好写成:
  prefix ++ (best :: post)
  其中 post 是 list string，best 是 string。
  错误来自于没有加括号。
*)

Definition is_strongest (best : string) (exts : list string) : Prop :=
  exists prefix post,
    exts = prefix ++ (best :: post) /\
    ~ In best prefix /\
    (forall e, In e prefix -> (strength e < strength best)%Z) /\
    (forall e, In e post -> (strength e <= strength best)%Z).

Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False
  | _ :: _ =>
    exists strongest_ext,
      is_strongest strongest_ext extensions /\
      res = class_name ++ "." ++ strongest_ext
  end.

(* 计算各字符串的 strength *)

Lemma strength_tEN : strength "tEN" = 1.
Proof.
  unfold strength, count_pred.
  simpl.
  reflexivity.
Qed.

Lemma strength_niNE : strength "niNE" = 0.
Proof.
  unfold strength, count_pred.
  simpl.
  reflexivity.
Qed.

Lemma strength_eIGHt8OKe : strength "eIGHt8OKe" = 2.
Proof.
  unfold strength, count_pred.
  simpl.
  reflexivity.
Qed.

(* 证明 eIGHt8OKe 比其他两个扩展强 *)
Lemma eIGHt8OKe_stronger_than_others :
  forall ext, In ext ["tEN"; "niNE"] -> (strength ext < strength "eIGHt8OKe")%Z.
Proof.
  intros ext H.
  destruct H as [H | [H | []]]; subst; simpl;
  rewrite ?strength_tEN, ?strength_niNE, strength_eIGHt8OKe; lia.
Qed.

(* 证明 eIGHt8OKe 后无扩展权值更强 *)
Lemma eIGHt8OKe_not_smaller_post :
  forall ext, In ext [] -> (strength ext <= strength "eIGHt8OKe")%Z.
Proof.
  intros ext H; inversion H.
Qed.

Example problem_153_test :
  problem_153_spec "Watashi" ["tEN"; "niNE"; "eIGHt8OKe"] "Watashi.eIGHt8OKe".
Proof.
  unfold problem_153_spec.
  simpl.
  exists "eIGHt8OKe".
  split.
  - unfold is_strongest.
    exists ["tEN"; "niNE"], [].
    repeat split.
    + reflexivity.
    + intro Hin; simpl in Hin; destruct Hin as [H | [H | []]]; discriminate.
    + apply eIGHt8OKe_stronger_than_others.
    + apply eIGHt8OKe_not_smaller_post.
  - reflexivity.
Qed.