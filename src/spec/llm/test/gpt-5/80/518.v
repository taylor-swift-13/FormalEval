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

Lemma nth_error_string_Some_len: forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [| a' s' IH]; intros n a H; simpl in H.
  - discriminate.
  - destruct n.
    + inversion H; simpl; lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("aba11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeeccccddddaaaabbbbccdccddddaaaabbbbccccdddd"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    destruct H as [Hlen Hall].
    assert (Hlt5: 5 < String.length ("aba11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeeccccddddaaaabbbbccdccddddaaaabbbbccccdddd"%string)).
    { apply (nth_error_string_Some_len ("aba11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeeccccddddaaaabbbbccdccddddaaaabbbbccccdddd"%string) 5 ("2"%char)).
      simpl. reflexivity. }
    specialize (Hall 3).
    assert (Hpre: 3 + 2 < String.length ("aba11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeeccccddddaaaabbbbccdccddddaaaabbbbccccdddd"%string)) by (simpl; exact Hlt5).
    specialize (Hall Hpre).
    destruct Hall as (a & b & c & Ha & Hb & Hc & Hdistinct).
    simpl in Ha, Hb.
    inversion Ha; inversion Hb; subst.
    destruct Hdistinct as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.