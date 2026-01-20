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

Lemma nth_error_string_Some_lt_length :
  forall s n x, nth_error_string s n = Some x -> n < String.length s.
Proof.
  induction s as [| a s' IH]; intros n x H.
  - simpl in H. discriminate.
  - destruct n as [| n'].
    + simpl in H. inversion H. simpl. lia.
    + simpl in H. apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long:
  is_happy_spec
    ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (Hcond: 2 + 2 < String.length ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff0112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefff"%string)).
    { eapply nth_error_string_Some_lt_length with (x := "c"%char).
      simpl. reflexivity.
    }
    specialize (Hforall 2).
    specialize (Hforall Hcond).
    destruct Hforall as [a1 [b1 [c1 [Ha [Hb [Hc Hd]]]]]].
    simpl in Ha.
    simpl in Hb.
    simpl in Hc.
    inversion Ha; subst.
    inversion Hb; subst.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab.
    reflexivity.
Qed.