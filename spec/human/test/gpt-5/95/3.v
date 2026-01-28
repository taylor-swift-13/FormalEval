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
    [(KeyString "p", "pineapple"); (KeyString "5", "banana"); (KeyString "a", "apple")]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros HP.
    destruct HP as [Hlower | Hupper].
    + assert (Hin : In (KeyString "5", "banana")
                     [(KeyString "p", "pineapple"); (KeyString "5", "banana"); (KeyString "a", "apple")]).
      { simpl. right. left. reflexivity. }
      specialize (Hlower _ _ Hin).
      simpl in Hlower. unfold is_lowercase in Hlower. simpl in Hlower.
      inversion Hlower as [| c l Hc Hl]; subst.
      simpl in Hc. vm_compute in Hc. exfalso. discriminate Hc.
    + assert (Hin : In (KeyString "p", "pineapple")
                     [(KeyString "p", "pineapple"); (KeyString "5", "banana"); (KeyString "a", "apple")]).
      { simpl. left. reflexivity. }
      specialize (Hupper _ _ Hin).
      simpl in Hupper. unfold is_uppercase in Hupper. simpl in Hupper.
      inversion Hupper as [| c l Hc Hl]; subst.
      simpl in Hc. vm_compute in Hc. exfalso. discriminate Hc.
  - intros H. exfalso. discriminate H.
Qed.