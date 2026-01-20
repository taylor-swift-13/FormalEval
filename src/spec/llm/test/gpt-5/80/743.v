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

Example test_is_happy_long_false: is_happy_spec ("abcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbdabcccaaabbd11223344556607788990abcccaaabbd112233112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccd445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900d9eefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdeeffftuvwxyz"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - set (s := "abcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbdabcccaaabbd11223344556607788990abcccaaabbd112233112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccd445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900d9eefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdeeffftuvwxyz"%string).
    change ("abcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbdabcccaaabbd11223344556607788990abcccaaabbd112233112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccd445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900d9eefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdeeffftuvwxyz"%string) with s.
    unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [_ Hall].
    pose (i := 34).
    assert (Hi0: nth_error_string s i = Some "a"%char).
    { subst s i. simpl. reflexivity. }
    assert (Hi2: nth_error_string s (i + 2) = Some "a"%char).
    { subst s i. simpl. reflexivity. }
    assert (nth_lt: forall s0 n0 a0, nth_error_string s0 n0 = Some a0 -> n0 < String.length s0).
    { intros s0 n0 a0 Hn.
      revert n0 a0 Hn.
      induction s0 as [|ch t IH]; intros n0 a0 Hn; simpl in *.
      - inversion Hn.
      - destruct n0.
        + simpl in Hn. inversion Hn. simpl. lia.
        + simpl in Hn. specialize (IH _ _ Hn). lia.
    }
    specialize (Hall i).
    assert (i + 2 < String.length s) by (apply nth_lt with (a0 := "a"%char); exact Hi2).
    specialize (Hall H).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    rewrite Hi0 in Ha. inversion Ha; subst.
    rewrite Hi2 in Hc. inversion Hc; subst.
    destruct Hd as [_ [Hac _]].
    apply Hac. reflexivity.
Qed.