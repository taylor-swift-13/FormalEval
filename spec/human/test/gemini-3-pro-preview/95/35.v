Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition is_char_lowercase (c : ascii) : bool :=
  (("a" <=? c)%char && (c <=? "z")%char).

Definition is_char_uppercase (c : ascii) : bool :=
  (("A" <=? c)%char && (c <=? "Z")%char).

Definition is_lowercase (s : string) : Prop :=
  let chars := list_ascii_of_string s in
  (existsb is_char_lowercase chars && forallb (fun c => negb (is_char_uppercase c)) chars) = true.

Definition is_uppercase (s : string) : Prop :=
  let chars := list_ascii_of_string s in
  (existsb is_char_uppercase chars && forallb (fun c => negb (is_char_lowercase c)) chars) = true.

Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

Definition dictionary := list (KeyType * string).

Definition problem_95_pre (d : dictionary) : Prop := True.

Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

Example test_problem_95 : problem_95_spec 
  [(KeyString "first_name", "John"); 
   (KeyString "last_name", "Doe"); 
   (KeyString "age", "35"); 
   (KeyString "city", "New York"); 
   (KeyString "income", "$50,000"); 
   (KeyString "ageage", "Dooe")] 
  true.
Proof.
  unfold problem_95_spec.
  simpl.
  split.
  - intros _. reflexivity.
  - intros _.
    left.
    intros k v H_in.
    simpl in H_in.
    repeat (destruct H_in as [H_eq | H_in]; 
            [ inversion H_eq; subst; vm_compute; reflexivity 
            | ]).
    contradiction.
Qed.