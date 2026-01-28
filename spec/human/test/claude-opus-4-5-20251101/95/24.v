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
  [(KeyString "first_name", "John"%string); 
   (KeyString "Last_Name", "Dooe"%string); 
   (KeyString "Age", "35"%string); 
   (KeyString "city", "New York"%string); 
   (KeyString "Income", "$50,000"%string); 
   (KeyString "FIRST_NAME", "Jane"%string); 
   (KeyString "1", "36"%string); 
   (KeyString "Incyellowome", "INCOMEJohn"%string)].

Lemma not_lowercase_Last_Name : ~ is_lowercase "Last_Name".
Proof.
  unfold is_lowercase. simpl.
  intro H.
  inversion H.
  simpl in H2.
  discriminate H2.
Qed.

Lemma not_uppercase_first_name : ~ is_uppercase "first_name".
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
  - intros [Hall_lower | Hall_upper].
    + exfalso.
      assert (H: In (KeyString "Last_Name", "Dooe"%string) 
        [(KeyString "first_name", "John"%string); 
         (KeyString "Last_Name", "Dooe"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "city", "New York"%string); 
         (KeyString "Income", "$50,000"%string); 
         (KeyString "FIRST_NAME", "Jane"%string); 
         (KeyString "1", "36"%string); 
         (KeyString "Incyellowome", "INCOMEJohn"%string)]).
      { simpl. right. left. reflexivity. }
      specialize (Hall_lower (KeyString "Last_Name") "Dooe"%string H).
      apply not_lowercase_Last_Name.
      exact Hall_lower.
    + exfalso.
      assert (H: In (KeyString "first_name", "John"%string) 
        [(KeyString "first_name", "John"%string); 
         (KeyString "Last_Name", "Dooe"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "city", "New York"%string); 
         (KeyString "Income", "$50,000"%string); 
         (KeyString "FIRST_NAME", "Jane"%string); 
         (KeyString "1", "36"%string); 
         (KeyString "Incyellowome", "INCOMEJohn"%string)]).
      { simpl. left. reflexivity. }
      specialize (Hall_upper (KeyString "first_name") "John"%string H).
      apply not_uppercase_first_name.
      exact Hall_upper.
  - intros H. discriminate H.
Qed.