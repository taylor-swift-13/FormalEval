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

Lemma char_S_uppercase : (("A" <=? "S")%char && ("S" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_T_uppercase : (("A" <=? "T")%char && ("T" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_A_uppercase : (("A" <=? "A")%char && ("A" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_E_uppercase : (("A" <=? "E")%char && ("E" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_Z_uppercase : (("A" <=? "Z")%char && ("Z" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_I_uppercase : (("A" <=? "I")%char && ("I" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_P_uppercase : (("A" <=? "P")%char && ("P" <=? "Z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma is_uppercase_STATE : is_uppercase "STATE".
Proof.
  unfold is_uppercase. simpl.
  constructor. exact char_S_uppercase.
  constructor. exact char_T_uppercase.
  constructor. exact char_A_uppercase.
  constructor. exact char_T_uppercase.
  constructor. exact char_E_uppercase.
  constructor.
Qed.

Lemma is_uppercase_ZIP : is_uppercase "ZIP".
Proof.
  unfold is_uppercase. simpl.
  constructor. exact char_Z_uppercase.
  constructor. exact char_I_uppercase.
  constructor. exact char_P_uppercase.
  constructor.
Qed.

Definition test_dict : dictionary := 
  [(KeyString "STATE", "NC"%string); (KeyString "ZIP", "12345"%string)].

Example problem_95_test1 :
  problem_95_spec test_dict true.
Proof.
  unfold problem_95_spec, test_dict.
  split.
  - intros _. reflexivity.
  - intros _.
    right.
    intros k v H.
    destruct H as [H | [H | H]].
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_STATE.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_ZIP.
    + destruct H.
Qed.