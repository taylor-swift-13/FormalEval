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

Lemma nth_error_string_some_lt : forall s n x,
  nth_error_string s n = Some x -> n < String.length s.
Proof.
  intros s n x H.
  induction n as [|n IH] in s, H |- *.
  - destruct s; simpl in H; try discriminate.
    simpl. lia.
  - destruct s; simpl in H; try discriminate.
    apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("aaaaddbbccddeeaabbcaabcccaaabbdddeefffcddeebcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabca9bcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [_ Hall].
    assert (Hlt: 2 < String.length ("aaaaddbbccddeeaabbcaabcccaaabbdddeefffcddeebcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabca9bcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff"%string)).
    { eapply nth_error_string_some_lt.
      simpl. reflexivity. }
    specialize (Hall 0).
    destruct (Hall Hlt) as [a [b [c [Ha [Hb [Hc Habc]]]]]].
    simpl in Ha. inversion Ha; subst.
    simpl in Hb. inversion Hb; subst.
    simpl in Hc. inversion Hc; subst.
    destruct Habc as [Hab _].
    apply Hab. reflexivity.
Qed.