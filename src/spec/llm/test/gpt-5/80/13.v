Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Fixpoint nth_error_string (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String a s', 0 => Some a
  | String _ s', S n' => nth_error_string s' n'
  end.

Definition distinct3 (a b c : ascii) : Prop :=
  a <> b /\ a <> c /\ b <> c.

Definition happy_prop (s : string) : Prop :=
  3 <= String.length s /\
  forall i, i + 2 < String.length s ->
    exists a b c,
      nth_error_string s i = Some a /\
      nth_error_string s (i + 1) = Some b /\
      nth_error_string s (i + 2) = Some c /\
      distinct3 a b c.

Definition is_happy_spec (s : string) (r : bool) : Prop :=
  (r = true /\ happy_prop s) \/ (r = false /\ ~ happy_prop s).

Example test_is_happy_cadbfe: is_happy_spec ("cadbfe"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl. lia.
    + intros i Hi.
      destruct i as [| [| [| [| [| i5]]]]].
      * exists ("c"%char), ("a"%char), ("d"%char).
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        unfold distinct3.
        split.
        { intro H; discriminate H. }
        split.
        { intro H; discriminate H. }
        { intro H; discriminate H. }
      * exists ("a"%char), ("d"%char), ("b"%char).
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        unfold distinct3.
        split.
        { intro H; discriminate H. }
        split.
        { intro H; discriminate H. }
        { intro H; discriminate H. }
      * exists ("d"%char), ("b"%char), ("f"%char).
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        unfold distinct3.
        split.
        { intro H; discriminate H. }
        split.
        { intro H; discriminate H. }
        { intro H; discriminate H. }
      * exists ("b"%char), ("f"%char), ("e"%char).
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        split.
        { simpl. reflexivity. }
        unfold distinct3.
        split.
        { intro H; discriminate H. }
        split.
        { intro H; discriminate H. }
        { intro H; discriminate H. }
      * exfalso. simpl in Hi. lia.
      * exfalso. simpl in Hi. lia.
Qed.