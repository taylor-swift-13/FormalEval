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

Lemma is_lowercase_first_name : is_lowercase "first_name".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Lemma is_lowercase_last_name : is_lowercase "last_name".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Lemma is_lowercase_age : is_lowercase "age".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Lemma is_lowercase_city : is_lowercase "city".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Lemma is_lowercase_income : is_lowercase "income".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Definition test_dict : dictionary := 
  [(KeyString "first_name", "John"%string); 
   (KeyString "last_name", "Doe"%string); 
   (KeyString "age", "35"%string); 
   (KeyString "city", "New York"%string); 
   (KeyString "income", "$50,000"%string)].

Example problem_95_test1 :
  problem_95_spec test_dict true.
Proof.
  unfold problem_95_spec, test_dict.
  split.
  - intros _. reflexivity.
  - intros _.
    left.
    intros k v H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_first_name.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_last_name.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_age.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_city.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_income.
    + destruct H.
Qed.