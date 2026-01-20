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

Example test_is_happy_single_a: is_happy_spec ("qwertyuiopasdefghjklzxcvbnmq11223344556677889900112bcabcabaaddbbccddeeaabbccddeebcab7889900wertqwertyuiopasdefghjklzxcvbnmqwertyuiopasdfghjklzxcvbjklzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (i := String.length "qwertyuiopasdefghjklzxcvbnmq"%string).
    assert (i + 2 < String.length "qwertyuiopasdefghjklzxcvbnmq11223344556677889900112bcabcabaaddbbccddeeaabbccddeebcab7889900wertqwertyuiopasdefghjklzxcvbnmqwertyuiopasdfghjklzxcvbjklzxcvb"%string) as Hlt.
    { unfold i; simpl; lia. }
    specialize (Hall i Hlt).
    destruct Hall as [a [b [c [Hi [Hi1 [Hi2 Hdistinct]]]]]].
    simpl in Hi. inversion Hi; subst.
    simpl in Hi1. inversion Hi1; subst.
    simpl in Hi2. inversion Hi2; subst.
    destruct Hdistinct as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.