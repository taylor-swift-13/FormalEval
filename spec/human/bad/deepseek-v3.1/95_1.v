Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

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

(* check_dict_case 函数的规约 *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

(* 辅助引理：检查单字符字符串是否在小写范围内 *)
Lemma char_p_lowercase : is_lowercase "p".
Proof.
  unfold is_lowercase.
  simpl.
  constructor; simpl; reflexivity.
  constructor.
Qed.

Lemma char_b_lowercase : is_lowercase "b".
Proof.
  unfold is_lowercase.
  simpl.
  constructor; simpl; reflexivity.
  constructor.
Qed.

(* 测试用例证明 *)
Example test_case_1 : problem_95_spec [(KeyString "p", "pineapple"); (KeyString "b", "banana")] true.
Proof.
  unfold problem_95_spec.
  simpl.
  split.
  - intros [H | H].
    + reflexivity.
    + reflexivity.
  - intros H.
    left.
    intros k v HIn.
    simpl in HIn.
    destruct HIn as [HIn | HIn].
    + inversion HIn.
      * subst. apply char_p_lowercase.
      * subst. apply char_b_lowercase.
    + contradiction.
Qed.