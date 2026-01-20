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

Example test_is_happy_long:
  is_happy_spec
    ("aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccdddcdbabcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffccccddddddee"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 0).
    assert (0 + 2 < String.length
              ("aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccdddcdbabcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffccccddddddee"%string)) by lia.
    specialize (Hall H).
    destruct Hall as [a [b [c [E0 [E1 [E2 Hd]]]]]].
    simpl in E0.
    inversion E0; subst a.
    simpl in E1.
    inversion E1; subst b.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab; reflexivity.
Qed.