Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* 定义字符串是否为小写的谓词 *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("a" <=? c)%char && (c <=? "z")%char) = true) (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词 *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("A" <=? c)%char && (c <=? "Z")%char) = true) (list_ascii_of_string s).

(* 定义键的类型，可以是字符串或其他类型 *)
Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

(* 定义字典的类型，键为 KeyType，值为字符串 *)
Definition dictionary := list (KeyType * string).

(* 字典类型已保证键值均为字符串，无附加约束；空字典由规约处理 *)
Definition problem_95_pre (d : dictionary) : Prop := True.

(* check_dict_case 函数的规约 *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

Example test_problem_95 : problem_95_spec [(KeyString "2", "banana"); (KeyString "3", "cherry"); (KeyString "Income", "New York")] false.
Proof.
  unfold problem_95_spec.
  simpl.
  split.
  - intros [H_lower | H_upper].
    + specialize (H_lower (KeyString "2") "banana").
      assert (In (KeyString "2", "banana") [(KeyString "2", "banana"); (KeyString "3", "cherry"); (KeyString "Income", "New York")]) as H_in.
      { left. reflexivity. }
      apply H_lower in H_in.
      simpl in H_in.
      unfold is_lowercase in H_in.
      simpl in H_in.
      inversion H_in as [| x l H_head H_tail].
      simpl in H_head.
      discriminate H_head.
    + specialize (H_upper (KeyString "2") "banana").
      assert (In (KeyString "2", "banana") [(KeyString "2", "banana"); (KeyString "3", "cherry"); (KeyString "Income", "New York")]) as H_in.
      { left. reflexivity. }
      apply H_upper in H_in.
      simpl in H_in.
      unfold is_uppercase in H_in.
      simpl in H_in.
      inversion H_in as [| x l H_head H_tail].
      simpl in H_head.
      discriminate H_head.
  - intros H. inversion H.
Qed.