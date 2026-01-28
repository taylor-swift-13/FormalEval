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

Lemma is_uppercase_FIRST_NAME : is_uppercase "FIRST_NAME".
Proof.
  unfold is_uppercase. simpl.
  repeat constructor.
Abort.

Lemma is_uppercase_letter (c : ascii) : 
  (("A" <=? c)%char && (c <=? "Z")%char) = true -> 
  (("A" <=? c)%char && (c <=? "Z")%char) = true.
Proof. auto. Qed.

Definition is_uppercase_or_underscore (s : string) : Prop :=
  Forall (fun c => ((("A" <=? c)%char && (c <=? "Z")%char) = true) \/ (c = "_"%char)) (list_ascii_of_string s).

Definition problem_95_spec_v2 (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase_or_underscore s | KeyOther => False end) )
    <-> output = true
  end.

Definition test_dict : dictionary := 
  [(KeyString "FIRST_NAME", "John"%string); 
   (KeyString "LAST_NAME", "DOE"%string); 
   (KeyString "AGE", "35"%string); 
   (KeyString "CITY", "NEW YORK"%string); 
   (KeyString "INCOME", "$50,000"%string)].

Lemma is_uppercase_or_underscore_FIRST_NAME : is_uppercase_or_underscore "FIRST_NAME".
Proof.
  unfold is_uppercase_or_underscore. simpl.
  repeat (try (constructor; [left; reflexivity | ]); try (constructor; [right; reflexivity | ])).
  constructor.
Qed.

Lemma is_uppercase_or_underscore_LAST_NAME : is_uppercase_or_underscore "LAST_NAME".
Proof.
  unfold is_uppercase_or_underscore. simpl.
  repeat (try (constructor; [left; reflexivity | ]); try (constructor; [right; reflexivity | ])).
  constructor.
Qed.

Lemma is_uppercase_or_underscore_AGE : is_uppercase_or_underscore "AGE".
Proof.
  unfold is_uppercase_or_underscore. simpl.
  repeat (try (constructor; [left; reflexivity | ])).
  constructor.
Qed.

Lemma is_uppercase_or_underscore_CITY : is_uppercase_or_underscore "CITY".
Proof.
  unfold is_uppercase_or_underscore. simpl.
  repeat (try (constructor; [left; reflexivity | ])).
  constructor.
Qed.

Lemma is_uppercase_or_underscore_INCOME : is_uppercase_or_underscore "INCOME".
Proof.
  unfold is_uppercase_or_underscore. simpl.
  repeat (try (constructor; [left; reflexivity | ])).
  constructor.
Qed.

Example problem_95_test1 :
  problem_95_spec_v2 test_dict true.
Proof.
  unfold problem_95_spec_v2, test_dict.
  split.
  - intros _. reflexivity.
  - intros _.
    right.
    intros k v H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_or_underscore_FIRST_NAME.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_or_underscore_LAST_NAME.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_or_underscore_AGE.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_or_underscore_CITY.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_uppercase_or_underscore_INCOME.
    + destruct H.
Qed.