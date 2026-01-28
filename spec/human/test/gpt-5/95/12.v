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
    [(KeyString "1", "apple"); (KeyString "2", "banana"); (KeyString "3", "cherry")]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros HP. exfalso.
    destruct HP as [Hlower | Hupper].
    + specialize (Hlower (KeyString "1") "apple").
      assert (Hin : In (KeyString "1", "apple")
                [(KeyString "1", "apple"); (KeyString "2", "banana"); (KeyString "3", "cherry")]).
      { simpl. left. reflexivity. }
      specialize (Hlower Hin).
      unfold is_lowercase in Hlower.
      vm_compute in Hlower.
      inversion Hlower as [| c l Hc Hl]. subst.
      vm_compute in Hc. discriminate Hc.
    + specialize (Hupper (KeyString "1") "apple").
      assert (Hin : In (KeyString "1", "apple")
                [(KeyString "1", "apple"); (KeyString "2", "banana"); (KeyString "3", "cherry")]).
      { simpl. left. reflexivity. }
      specialize (Hupper Hin).
      unfold is_uppercase in Hupper.
      vm_compute in Hupper.
      inversion Hupper as [| c l Hc Hl]. subst.
      vm_compute in Hc. discriminate Hc.
  - intros Heq. exfalso. discriminate Heq.
Qed.