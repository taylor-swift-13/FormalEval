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

Lemma nth_error_string_Some_length: forall s n c, nth_error_string s n = Some c -> n < String.length s.
Proof.
  induction s as [|a s' IH]; intros n c H.
  - simpl in H. discriminate.
  - destruct n.
    + simpl in H. inversion H. simpl. lia.
    + simpl in H. apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("abcdefgabcdegfgcdefga113223344556677889900112233445566778899001122334455667abcabcabcabc7abcabcabcabacabcabcabaaddbb1ccddeeaabbccddeebcab7889900defg"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (14 < String.length ("abcdefgabcdegfgcdefga113223344556677889900112233445566778899001122334455667abcabcabcabc7abcabcabcabacabcabcabaaddbb1ccddeeaabbccddeebcab7889900defg"%string)).
    { assert (Hnth: nth_error_string ("abcdefgabcdegfgcdefga113223344556677889900112233445566778899001122334455667abcabcabcabc7abcabcabcabacabcabcabaaddbb1ccddeeaabbccddeebcab7889900defg"%string) 14 = Some "g"%char).
      { simpl. reflexivity. }
      eapply nth_error_string_Some_length. exact Hnth. }
    pose proof (Hforall 12 ltac:(exact H)) as Hex.
    destruct Hex as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    simpl in Ha. inversion Ha; subst.
    simpl in Hb. inversion Hb; subst.
    simpl in Hc. inversion Hc; subst.
    destruct Hdistinct as [_ [Hac _]].
    apply Hac. reflexivity.
Qed.