Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* 定义字符串是否为小写的谓词: 只要不包含大写字母即可 (兼容非字母字符如下划线) *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("A" <=? c)%char && (c <=? "Z")%char) = false) (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词: 只要不包含小写字母即可 (兼容非字母字符如下划线) *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("a" <=? c)%char && (c <=? "z")%char) = false) (list_ascii_of_string s).

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

Example test_problem_95 : problem_95_spec 
  [ (KeyString "FIRST_NAME", "John");
    (KeyString "LAST_NAME", "DOE");
    (KeyString "AGE", "35");
    (KeyString "CITY", "NK");
    (KeyString "INCOME", "$50,000") ] true.
Proof.
  unfold problem_95_spec.
  simpl.
  split.
  - intros _. reflexivity.
  - intros _.
    right.
    intros k v H_in.
    (* Use repeat loop to handle each element in the list *)
    repeat (destruct H_in as [H_in | H_in]; [
      inversion H_in; subst; simpl; unfold is_uppercase; simpl;
      repeat (constructor; try (vm_compute; reflexivity))
    | ]).
    contradiction.
Qed.