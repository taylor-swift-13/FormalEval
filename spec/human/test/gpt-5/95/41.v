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
    [(KeyString "firstName", "John");
     (KeyString "LASTNAME", "DOE");
     (KeyString "Age", "D");
     (KeyString "cItY", "new yorAgek");
     (KeyString "IncIome", "FIRST_NAME")]
    false.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros H.
    destruct H as [Hlower | Hupper].
    + assert (Hin: In (KeyString "firstName", "John")
        [(KeyString "firstName", "John");
         (KeyString "LASTNAME", "DOE");
         (KeyString "Age", "D");
         (KeyString "cItY", "new yorAgek");
         (KeyString "IncIome", "FIRST_NAME")]) by (simpl; left; reflexivity).
      specialize (Hlower _ _ Hin).
      unfold is_lowercase in Hlower; simpl in Hlower.
      inversion Hlower as [| ? ? Hf Htail1]; subst.
      inversion Htail1 as [| ? ? Hi Htail2]; subst.
      inversion Htail2 as [| ? ? Hr Htail3]; subst.
      inversion Htail3 as [| ? ? Hs Htail4]; subst.
      inversion Htail4 as [| ? ? Ht Htail5]; subst.
      inversion Htail5 as [| ? ? HN _]; subst.
      vm_compute in HN. discriminate.
    + assert (Hin: In (KeyString "firstName", "John")
        [(KeyString "firstName", "John");
         (KeyString "LASTNAME", "DOE");
         (KeyString "Age", "D");
         (KeyString "cItY", "new yorAgek");
         (KeyString "IncIome", "FIRST_NAME")]) by (simpl; left; reflexivity).
      specialize (Hupper _ _ Hin).
      unfold is_uppercase in Hupper; simpl in Hupper.
      inversion Hupper as [| ? ? Hf _]; subst.
      vm_compute in Hf. discriminate.
  - intros Hfalse. inversion Hfalse.
Qed.