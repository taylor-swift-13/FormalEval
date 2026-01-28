Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 定义字符串到 ascii 列表的转换 *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: list_ascii_of_string rest
  end.

(* 判断字符 c 是否在区间 [low, high] *)
Definition char_between (low high : ascii) (c : ascii) : bool :=
  let nl := nat_of_ascii low in
  let nh := nat_of_ascii high in
  let nc := nat_of_ascii c in
  (Nat.leb nl nc) && (Nat.leb nc nh).

(* 定义字符串是否为小写的谓词 *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => char_between "a"%char "z"%char c = true) (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词 *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => char_between "A"%char "Z"%char c = true) (list_ascii_of_string s).

(* 键的类型 *)
Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

(* 字典类型 *)
Definition dictionary := list (KeyType * string).

Definition problem_95_pre (d : dictionary) : Prop := True.

(* 规格说明 *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

(* 下面证明字符串 "p" 是小写 *)
Lemma p_is_lowercase : is_lowercase "p".
Proof.
  unfold is_lowercase.
  simpl.
  constructor.
  - unfold char_between, Nat.leb.
    simpl.
    reflexivity.
  - constructor.
Qed.

(* 证明字符串 "b" 是小写 *)
Lemma b_is_lowercase : is_lowercase "b".
Proof.
  unfold is_lowercase.
  simpl.
  constructor.
  - unfold char_between, Nat.leb.
    simpl.
    reflexivity.
  - constructor.
Qed.

Example test_case_1 :
  problem_95_spec [ (KeyString "p", "pineapple"); (KeyString "b", "banana") ] true.
Proof.
  unfold problem_95_spec.
  simpl.
  split; intros _.
  - reflexivity.
  - left.
    intros k v HIn.
    destruct k as [s|].
    + simpl in HIn.
      destruct HIn as [Heq | [Heq | []]]; subst s.
      * exact p_is_lowercase.
      * exact b_is_lowercase.
    + simpl in HIn; contradiction.
Qed.