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
    [(KeyString "first_name", "John");
     (KeyString "Age", "35");
     (KeyString "city", "New York");
     (KeyString "Income", "$50,000");
     (KeyString "FIRST_NAME", "Jane")]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros H.
    exfalso.
    destruct H as [Hl | Hu].
    + assert (Hin : In (KeyString "FIRST_NAME", "Jane")
                      [(KeyString "first_name", "John");
                       (KeyString "Age", "35");
                       (KeyString "city", "New York");
                       (KeyString "Income", "$50,000");
                       (KeyString "FIRST_NAME", "Jane")]).
      { simpl. right. right. right. right. left. reflexivity. }
      specialize (Hl (KeyString "FIRST_NAME") "Jane" Hin).
      unfold is_lowercase in Hl; simpl in Hl.
      inversion Hl as [| c l Hhd Htl].
      vm_compute in Hhd.
      discriminate Hhd.
    + assert (Hin : In (KeyString "city", "New York")
                      [(KeyString "first_name", "John");
                       (KeyString "Age", "35");
                       (KeyString "city", "New York");
                       (KeyString "Income", "$50,000");
                       (KeyString "FIRST_NAME", "Jane")]).
      { simpl. right. right. left. reflexivity. }
      specialize (Hu (KeyString "city") "New York" Hin).
      unfold is_uppercase in Hu; simpl in Hu.
      inversion Hu as [| c l Hhd Htl].
      vm_compute in Hhd.
      discriminate Hhd.
  - intros H.
    exfalso.
    inversion H.
Qed.