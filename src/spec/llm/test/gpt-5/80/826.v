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

Lemma nth_error_string_Some_length :
  forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s; intros n ch H; simpl in *.
  - discriminate.
  - destruct n; simpl in *.
    + inversion H; lia.
    + eapply IHs in H; lia.
Qed.

Example test_is_happy_long_string:
  is_happy_spec
    ("abcdefgabcdefgcdefgaabababababbabababababcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrnbGgbXWEqwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvbZstuvwxyzabcdefghijklmnopqarstuvwxyzbababab11223344556677889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900abababababababababababababababababababdecfgabcabababababbabababababababababababababababababababdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbddeeffftuvwxyzabbababababababababbcababababababababababababababababababadbababababbabdecfgabcdefgcdefgabcdefg"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (s := "abcdefgabcdefgcdefgaabababababbabababababcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrnbGgbXWEqwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvbZstuvwxyzabcdefghijklmnopqarstuvwxyzbababab11223344556677889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900abababababababababababababababababababdecfgabcabababababbabababababababababababababababababababdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbddeeffftuvwxyzabbababababababababbcababababababababababababababababababadbababababbabdecfgabcdefgcdefgabcdefg"%string) in *.
    assert (Hex20: exists ch, nth_error_string s 20 = Some ch).
    { unfold s; compute; eexists; reflexivity. }
    destruct Hex20 as [ch20 H20].
    assert (Hpre: 18 + 2 < String.length s).
    { eapply nth_error_string_Some_length in H20. lia. }
    specialize (Hall 18 Hpre).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    assert (Hbeq: nth_error_string s 19 = nth_error_string s 20).
    { unfold s; compute; reflexivity. }
    assert (Some b = Some c) as Hbc.
    { rewrite <- Hb, <- Hc. exact Hbeq. }
    inversion Hbc; subst.
    destruct Hdist as [_ [_ Hneqbc]].
    contradiction.
Qed.