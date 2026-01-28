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
      (KeyString "Last_Name", "Dooe");
      (KeyString "Age", "35");
      (KeyString "city", "New York");
      (KeyString "Income", "$50,000");
      (KeyString "FIRST_NAME", "Jane");
      (KeyString "Incyellowome", "INCOMEJohn") ]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros H. exfalso.
    destruct H as [HL | HU].
    + specialize (HL (KeyString "FIRST_NAME") "Jane").
      assert (Hin1 :
        In (KeyString "FIRST_NAME", "Jane")
           [ (KeyString "first_name", "John");
             (KeyString "Last_Name", "Dooe");
             (KeyString "Age", "35");
             (KeyString "city", "New York");
             (KeyString "Income", "$50,000");
             (KeyString "FIRST_NAME", "Jane");
             (KeyString "Incyellowome", "INCOMEJohn") ]).
      { simpl. right. right. right. right. right. left. reflexivity. }
      specialize (HL Hin1).
      simpl in HL.
      unfold is_lowercase in HL; simpl in HL.
      inversion HL as [| ? ? Hc Hl']; clear Hl'.
      vm_compute in Hc. discriminate Hc.
    + specialize (HU (KeyString "first_name") "John").
      assert (Hin2 :
        In (KeyString "first_name", "John")
           [ (KeyString "first_name", "John");
             (KeyString "Last_Name", "Dooe");
             (KeyString "Age", "35");
             (KeyString "city", "New York");
             (KeyString "Income", "$50,000");
             (KeyString "FIRST_NAME", "Jane");
             (KeyString "Incyellowome", "INCOMEJohn") ]).
      { simpl. left. reflexivity. }
      specialize (HU Hin2).
      simpl in HU.
      unfold is_uppercase in HU; simpl in HU.
      inversion HU as [| ? ? Hc Hl']; clear Hl'.
      vm_compute in Hc. discriminate Hc.
  - intros H. exfalso. discriminate H.
Qed.