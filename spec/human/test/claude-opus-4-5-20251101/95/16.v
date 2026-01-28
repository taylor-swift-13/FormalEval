Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
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

Definition test_dict2 : dictionary := 
  [(KeyString "2019", "year"%string)].

Lemma not_lowercase_2019 : ~ is_lowercase "2019".
Proof.
  unfold is_lowercase. simpl.
  intro H.
  inversion H.
  simpl in H2.
  discriminate H2.
Qed.

Lemma not_uppercase_2019 : ~ is_uppercase "2019".
Proof.
  unfold is_uppercase. simpl.
  intro H.
  inversion H.
  simpl in H2.
  discriminate H2.
Qed.

Example problem_95_test2 :
  problem_95_spec test_dict2 false.
Proof.
  unfold problem_95_spec, test_dict2.
  split.
  - intros [Hlow | Hup].
    + exfalso.
      specialize (Hlow (KeyString "2019") "year"%string).
      assert (Hin : In (KeyString "2019", "year"%string) [(KeyString "2019", "year"%string)]).
      { left. reflexivity. }
      specialize (Hlow Hin).
      apply not_lowercase_2019.
      exact Hlow.
    + exfalso.
      specialize (Hup (KeyString "2019") "year"%string).
      assert (Hin : In (KeyString "2019", "year"%string) [(KeyString "2019", "year"%string)]).
      { left. reflexivity. }
      specialize (Hup Hin).
      apply not_uppercase_2019.
      exact Hup.
  - intros H. discriminate H.
Qed.