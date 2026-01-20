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

Example test_is_happy_long_false: is_happy_spec ("abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaaaddbbccddeeaabbcacddeecddeebcab7889900deefff"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 1).
    assert (1 + 2 < String.length "abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaaaddbbccddeeaabbcacddeecddeebcab7889900deefff"%string) by (simpl; lia).
    specialize (Hall H).
    clear H.
    destruct Hall as [x [y [z [Hx [Hy [Hz Hd]]]]]].
    replace (1 + 1) with 2 in Hy by lia.
    replace (1 + 2) with 3 in Hz by lia.
    simpl (nth_error_string "abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaaaddbbccddeeaabbcacddeecddeebcab7889900deefff"%string 2) in Hy.
    simpl (nth_error_string "abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaaaddbbccddeeaabbcacddeecddeebcab7889900deefff"%string 3) in Hz.
    inversion Hy; subst.
    inversion Hz; subst.
    destruct Hd as [_ [_ Hyz]].
    apply Hyz.
    reflexivity.
Qed.