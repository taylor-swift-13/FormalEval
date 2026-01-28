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

Lemma char_y_lowercase : (("a" <=? "y")%char && ("y" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_e_lowercase : (("a" <=? "e")%char && ("e" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_l_lowercase : (("a" <=? "l")%char && ("l" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_o_lowercase : (("a" <=? "o")%char && ("o" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_w_lowercase : (("a" <=? "w")%char && ("w" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma is_lowercase_yellow : is_lowercase "yellow".
Proof.
  unfold is_lowercase. simpl.
  constructor. exact char_y_lowercase.
  constructor. exact char_e_lowercase.
  constructor. exact char_l_lowercase.
  constructor. exact char_l_lowercase.
  constructor. exact char_o_lowercase.
  constructor. exact char_w_lowercase.
  constructor.
Qed.

Definition test_dict : dictionary := 
  [(KeyString "yellow", "color"%string)].

Example problem_95_test1 :
  problem_95_spec test_dict true.
Proof.
  unfold problem_95_spec, test_dict.
  split.
  - intros _. reflexivity.
  - intros _.
    left.
    intros k v H.
    destruct H as [H | H].
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_yellow.
    + destruct H.
Qed.