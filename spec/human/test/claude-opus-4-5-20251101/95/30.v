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

Lemma char_y_lowercase : (("a" <=? "y")%char && ("y" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_e_lowercase : (("a" <=? "e")%char && ("e" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_l_lowercase : (("a" <=? "l")%char && ("l" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_o_lowercase : (("a" <=? "o")%char && ("o" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma char_w_lowercase : (("a" <=? "w")%char && ("w" <=? "z")%char)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma is_lowercase_yellow : is_lowercase "yellow".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Lemma is_lowercase_yell : is_lowercase "yell".
Proof.
  unfold is_lowercase. simpl.
  repeat constructor.
Qed.

Definition test_dict : dictionary := 
  [(KeyString "yellow", "color"%string); (KeyString "yell", "clor"%string)].

Example problem_95_test1 :
  problem_95_spec test_dict true.
Proof.
  unfold problem_95_spec, test_dict.
  split.
  - intros _. reflexivity.
  - intros _.
    left.
    intros k v H.
    destruct H as [H | [H | H]].
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_yellow.
    + injection H as Hk Hv.
      rewrite <- Hk.
      exact is_lowercase_yell.
    + destruct H.
Qed.