Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("a" <=? c)%char && (c <=? "z")%char) = true) (list_ascii_of_string s).

Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("A" <=? c)%char && (c <=? "Z")%char) = true) (list_ascii_of_string s).

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

Definition test_dict2 : dictionary := 
  [(KeyString "first_name", "John"%string); 
   (KeyString "Age", "35"%string); 
   (KeyString "city", "New York"%string); 
   (KeyString "Income", "$50,000"%string); 
   (KeyString "FIRST_NAME", "Jane"%string)].

Lemma not_lowercase_Age : ~ is_lowercase "Age".
Proof.
  unfold is_lowercase. simpl.
  intro H.
  inversion H.
  simpl in H1.
  discriminate.
Qed.

Lemma not_uppercase_first_name : ~ is_uppercase "first_name".
Proof.
  unfold is_uppercase. simpl.
  intro H.
  inversion H.
  simpl in H1.
  discriminate.
Qed.

Example problem_95_test2 :
  problem_95_spec test_dict2 false.
Proof.
  unfold problem_95_spec, test_dict2.
  split.
  - intros [Hlow | Hup].
    + exfalso.
      assert (H: In (KeyString "Age", "35"%string) 
        [(KeyString "first_name", "John"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "city", "New York"%string); 
         (KeyString "Income", "$50,000"%string); 
         (KeyString "FIRST_NAME", "Jane"%string)]).
      { right. left. reflexivity. }
      specialize (Hlow (KeyString "Age") "35"%string H).
      apply not_lowercase_Age. exact Hlow.
    + exfalso.
      assert (H: In (KeyString "first_name", "John"%string) 
        [(KeyString "first_name", "John"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "city", "New York"%string); 
         (KeyString "Income", "$50,000"%string); 
         (KeyString "FIRST_NAME", "Jane"%string)]).
      { left. reflexivity. }
      specialize (Hup (KeyString "first_name") "John"%string H).
      apply not_uppercase_first_name. exact Hup.
  - intros H. discriminate.
Qed.