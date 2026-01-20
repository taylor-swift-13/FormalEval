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

Example test_is_happy_long: is_happy_spec ("qwerty112112233445566775565677889900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 6).
    assert (6 + 2 < String.length "qwerty112112233445566775565677889900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string).
    { simpl. lia. }
    specialize (Hall H).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    destruct Hdistinct as [Hab [Hac Hbc]].
    replace (nth_error_string "qwerty112112233445566775565677889900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string 6) with (Some ("1"%char)) in Ha by (simpl; reflexivity).
    inversion Ha; subst a.
    replace (nth_error_string "qwerty112112233445566775565677889900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string 7) with (Some ("1"%char)) in Hb by (simpl; reflexivity).
    inversion Hb; subst b.
    apply Hab.
    reflexivity.
Qed.