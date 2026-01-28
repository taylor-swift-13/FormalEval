Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("a"%char <=? c)%char && (c <=? "z"%char)%char) = true) (list_ascii_of_string s).

Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("A"%char <=? c)%char && (c <=? "Z"%char)%char) = true) (list_ascii_of_string s).

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

Example problem_95_test_1 :
  problem_95_spec
    [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros [Hlower | Hupper].
    + specialize (Hlower (KeyString "Name") "John").
      assert (Hin: In ((KeyString "Name"), "John")
        [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")]).
      { simpl. left. reflexivity. }
      specialize (Hlower Hin).
      unfold is_lowercase in Hlower; simpl in Hlower.
      inversion Hlower as [| ? ? Hhd Htl].
      exfalso. vm_compute in Hhd. discriminate Hhd.
    + specialize (Hupper (KeyString "Name") "John").
      assert (Hin: In ((KeyString "Name"), "John")
        [(KeyString "Name", "John"); (KeyString "Age", "36"); (KeyString "City", "Houston")]).
      { simpl. left. reflexivity. }
      specialize (Hupper Hin).
      unfold is_uppercase in Hupper; simpl in Hupper.
      inversion Hupper as [| ? ? Hhd Htl].
      inversion Htl as [| ? ? Hhd2 Htl2].
      exfalso. vm_compute in Hhd2. discriminate Hhd2.
  - intros H. discriminate H.
Qed.