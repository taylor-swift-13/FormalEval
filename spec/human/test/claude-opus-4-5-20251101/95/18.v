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
  [(KeyString "firstName", "John"%string); 
   (KeyString "LASTNAME", "DOE"%string); 
   (KeyString "Age", "35"%string); 
   (KeyString "Income", "$50,000"%string)].

Lemma not_lowercase_firstName : ~ is_lowercase "firstName".
Proof.
  unfold is_lowercase. simpl.
  intro H.
  inversion H. subst.
  inversion H3. subst.
  inversion H5. subst.
  inversion H7. subst.
  inversion H9. subst.
  inversion H11. subst.
  inversion H13. subst.
  inversion H15. subst.
  simpl in H14.
  discriminate.
Qed.

Lemma not_uppercase_firstName : ~ is_uppercase "firstName".
Proof.
  unfold is_uppercase. simpl.
  intro H.
  inversion H. subst.
  simpl in H2.
  discriminate.
Qed.

Lemma not_lowercase_LASTNAME : ~ is_lowercase "LASTNAME".
Proof.
  unfold is_lowercase. simpl.
  intro H.
  inversion H. subst.
  simpl in H2.
  discriminate.
Qed.

Lemma not_uppercase_Age : ~ is_uppercase "Age".
Proof.
  unfold is_uppercase. simpl.
  intro H.
  inversion H. subst.
  inversion H3. subst.
  simpl in H4.
  discriminate.
Qed.

Example problem_95_test2 :
  problem_95_spec test_dict2 false.
Proof.
  unfold problem_95_spec, test_dict2.
  split.
  - intros [Hlow | Hup].
    + exfalso.
      assert (H: In (KeyString "LASTNAME", "DOE"%string) 
        [(KeyString "firstName", "John"%string); 
         (KeyString "LASTNAME", "DOE"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "Income", "$50,000"%string)]).
      { right. left. reflexivity. }
      specialize (Hlow (KeyString "LASTNAME") "DOE"%string H).
      apply not_lowercase_LASTNAME. exact Hlow.
    + exfalso.
      assert (H: In (KeyString "Age", "35"%string) 
        [(KeyString "firstName", "John"%string); 
         (KeyString "LASTNAME", "DOE"%string); 
         (KeyString "Age", "35"%string); 
         (KeyString "Income", "$50,000"%string)]).
      { right. right. left. reflexivity. }
      specialize (Hup (KeyString "Age") "35"%string H).
      apply not_uppercase_Age. exact Hup.
  - intros H. discriminate.
Qed.