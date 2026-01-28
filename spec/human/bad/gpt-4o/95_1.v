Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.

(* Helper function to convert a string to a list of ascii characters *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Predicate to check if a string is lowercase *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (andb (leb "a" c) (leb c "z")) = true) (list_ascii_of_string s).

(* Predicate to check if a string is uppercase *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (andb (leb "A" c) (leb c "Z")) = true) (list_ascii_of_string s).

(* Inductive type for KeyType *)
Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

(* Define the dictionary type *)
Definition dictionary := list (KeyType * string).

(* Precondition function *)
Definition problem_95_pre (d : dictionary) : Prop := True.

(* Specification function *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

(* Example proof for the test case *)
Example check_dict_case_example : problem_95_spec [(KeyString "p", "pineapple"); (KeyString "b", "banana")] true.
Proof.
  unfold problem_95_spec.
  simpl.
  split; intro H.
  - left. intros k v H_in.
    destruct H_in as [H_in | [H_in | []]]; inversion H_in; subst; simpl.
    + unfold is_lowercase. apply Forall_cons; [reflexivity | apply Forall_nil].
    + unfold is_lowercase. apply Forall_cons; [reflexivity | apply Forall_nil].
  - left. intros k v H_in.
    destruct H_in as [H_in | [H_in | []]]; inversion H_in; subst; simpl.
    + unfold is_lowercase. apply Forall_cons; [reflexivity | apply Forall_nil].
    + unfold is_lowercase. apply Forall_cons; [reflexivity | apply Forall_nil].
Qed.