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

Lemma nth_error_string_Some_lt:
  forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s as [|a s' IH]; intros n ch H.
  - simpl in H. discriminate.
  - destruct n as [|n'].
    + simpl. lia.
    + simpl in H. apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long_false:
  is_happy_spec
    ("abcoqwertyuiopasdfaaaddbbccddeeaabbcaabcccaaabbdddeefffcddeeghjklzxcvbnmqwertyuiopasdfghjklzxcvbabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab"%string)
    false.
Proof.
  set (S :=
    "abcoqwertyuiopasdfaaaddbbccddeeaabbcaabcccaaabbdddeefffcddeeghjklzxcvbnmqwertyuiopasdfghjklzxcvbabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab"%string).
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hex: exists ch, nth_error_string S 20 = Some ch).
    { unfold S. simpl. eexists. reflexivity. }
    destruct Hex as [ch20 Hch20].
    assert (Hbound: 18 + 2 < String.length S).
    { apply nth_error_string_Some_lt in Hch20. lia. }
    specialize (Hall 18).
    specialize (Hall Hbound).
    destruct Hall as [a [b [c [H18 [H19 [H20eq Hdistinct]]]]]].
    unfold S in H18, H19. simpl in H18, H19.
    inversion H18; subst a.
    inversion H19; subst b.
    destruct Hdistinct as [Hab _].
    apply Hab. reflexivity.
Qed.