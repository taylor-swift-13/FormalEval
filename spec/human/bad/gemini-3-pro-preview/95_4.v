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

Example test_problem_95 : problem_95_spec [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")] false.
Proof.
  unfold problem_95_spec.
  simpl.
  split.
  - intros [H_lower | H_upper].
    + (* Case: All keys are lowercase. We disprove this using "Name". *)
      assert (In (KeyString "Name", "John") [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")]) as Hin.
      { simpl. left. reflexivity. }
      specialize (H_lower (KeyString "Name") "John" Hin).
      simpl in H_lower.
      unfold is_lowercase in H_lower.
      (* "Name" starts with 'N' (78). 'a' (97) <= 78 is false. *)
      inversion H_lower; subst.
      simpl in H2.
      vm_compute in H2.
      discriminate.
    + (* Case: All keys are uppercase. We disprove this using "Name". *)
      assert (In (KeyString "Name", "John") [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")]) as Hin.
      { simpl. left. reflexivity. }
      specialize (H_upper (KeyString "Name") "John" Hin).
      simpl in H_upper.
      unfold is_uppercase in H_upper.
      (* "Name" starts with 'N' (ok), then 'a' (bad). *)
      inversion H_upper; subst. (* 'N' is upper, H2 is true *)
      inversion H3; subst.      (* 'a' is not upper *)
      simpl in H2.
      vm_compute in H2.
      discriminate.
  - intros H_contra.
    discriminate.
Qed.