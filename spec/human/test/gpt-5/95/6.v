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
    [(KeyString "fruit", "Orange"); (KeyString "taste", "Sweet")]
    true.
Proof.
  unfold problem_95_spec; simpl.
  split.
  - intros _. reflexivity.
  - intros _. left.
    intros k v Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      simpl. unfold is_lowercase; simpl.
      constructor.
      * vm_compute. reflexivity.
      * constructor.
        -- vm_compute. reflexivity.
        -- constructor.
          ++ vm_compute. reflexivity.
          ++ constructor.
             ** vm_compute. reflexivity.
             ** constructor.
                --- vm_compute. reflexivity.
                --- constructor.
    + destruct Hin as [Hin | Hin].
      * inversion Hin; subst.
        simpl. unfold is_lowercase; simpl.
        constructor.
        -- vm_compute. reflexivity.
        -- constructor.
          ** vm_compute. reflexivity.
          ** constructor.
             --- vm_compute. reflexivity.
             --- constructor.
                 +++ vm_compute. reflexivity.
                 +++ constructor.
                     **** vm_compute. reflexivity.
                     **** constructor.
      * inversion Hin.
Qed.