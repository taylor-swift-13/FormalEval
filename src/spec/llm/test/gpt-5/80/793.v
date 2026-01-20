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

Lemma nth_error_string_Some_length:
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [|ch s' IH]; intros [|n] a Hn; simpl in Hn; try discriminate.
  - inversion Hn; subst. simpl. lia.
  - simpl. apply lt_n_S. eapply IH. exact Hn.
Qed.

Example test_is_happy_long_false: is_happy_spec ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabca11223364455667788990011223344556677889900112233445566778baaddbbccddeeaabbccddeebcab7889900deefff"%string) false.
Proof.
  remember ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabca11223364455667788990011223344556677889900112233445566778baaddbbccddeeaabbccddeebcab7889900deefff"%string) as s eqn:Hs.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hn4: nth_error_string s 4 = Some ("c"%char)).
    { subst s. simpl. reflexivity. }
    apply nth_error_string_Some_length in Hn4.
    specialize (Hall 2).
    simpl in Hall.
    destruct (Hall Hn4) as [a [b [c [H2 [H3 [H4 Hdist]]]]]].
    assert (Heq23: nth_error_string s 2 = nth_error_string s 3).
    { subst s. simpl. reflexivity. }
    rewrite H2 in Heq23.
    rewrite H3 in Heq23.
    inversion Heq23; subst.
    destruct Hdist as [Hneq _].
    apply Hneq. reflexivity.
Qed.