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

Example test_is_happy_long: is_happy_spec ("aaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddd1122aaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccdddd3344dcababcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeedddddccccbbbbaaaaaaabbbbccccdeeeddddaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcab112233445566775565677889900cabcabcabcabeedddcedddccccaccccbbbbaaabaeeeedddcaaeeababcabcabcabcabcabeedadqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvblzxcvbdddccccalzxcvbdc"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (0 + 2 < String.length ("aaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddd1122aaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccdddd3344dcababcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeedddddccccbbbbaaaaaaabbbbccccdeeeddddaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcab112233445566775565677889900cabcabcabcabeedddcedddccccaccccbbbbaaabaeeeedddcaaeeababcabcabcabcabcabeedadqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvblzxcvbdddccccalzxcvbdc"%string)) as Hlt.
    { simpl; lia. }
    specialize (Hall 0 Hlt).
    destruct Hall as [a0 [b0 [c0 [Ha [Hb [Hc Hd]]]]]].
    simpl in Ha; inversion Ha; subst a0.
    simpl in Hb; inversion Hb; subst b0.
    simpl in Hc; inversion Hc; subst c0.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab; reflexivity.
Qed.