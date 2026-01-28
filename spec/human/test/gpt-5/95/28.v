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
    [ (KeyString "first_name", "John");
      (KeyString "Age", "35");
      (KeyString "city", "New York");
      (KeyString "Income", "$50,000");
      (KeyString "FIRST_NAME", "Jane");
      (KeyString "1", "36");
      (KeyString "Incyellowome", "INCOMEJohn") ]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros H.
    destruct H as [Hlower | Hupper].
    + exfalso.
      pose proof (Hlower (KeyString "Age") "35") as HL.
      assert (In (KeyString "Age", "35")
        [ (KeyString "first_name", "John");
          (KeyString "Age", "35");
          (KeyString "city", "New York");
          (KeyString "Income", "$50,000");
          (KeyString "FIRST_NAME", "Jane");
          (KeyString "1", "36");
          (KeyString "Incyellowome", "INCOMEJohn") ]) as Hin.
      { simpl. right. left. reflexivity. }
      specialize (HL Hin).
      unfold is_lowercase in HL; simpl in HL.
      inversion HL as [| ? ? Hc _].
      vm_compute in Hc. discriminate.
    + exfalso.
      pose proof (Hupper (KeyString "first_name") "John") as HU.
      assert (In (KeyString "first_name", "John")
        [ (KeyString "first_name", "John");
          (KeyString "Age", "35");
          (KeyString "city", "New York");
          (KeyString "Income", "$50,000");
          (KeyString "FIRST_NAME", "Jane");
          (KeyString "1", "36");
          (KeyString "Incyellowome", "INCOMEJohn") ]) as Hin.
      { simpl. left. reflexivity. }
      specialize (HU Hin).
      unfold is_uppercase in HU; simpl in HU.
      inversion HU as [| ? ? Hc _].
      vm_compute in Hc. discriminate.
  - intros H. inversion H.
Qed.