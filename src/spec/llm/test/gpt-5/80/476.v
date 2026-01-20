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

Example test_is_happy_long: is_happy_spec ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeqwertbabcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcababcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdbbaaaaeeeedddccccaaeeeedddccccabcabcabbcabcabcababcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaopasdfghjklzxcvblzxcvbedddccccalzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (i := String.length ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjk"%string)).
    assert (Hi: i + 2 < String.length ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeqwertbabcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcababcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdbbaaaaeeeedddccccaaeeeedddccccabcabcabbcabcabcababcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaopasdfghjklzxcvblzxcvbedddccccalzxcvb"%string)).
    { subst i. simpl. lia. }
    apply Hall in Hi.
    destruct Hi as [a [b [c [E0 [E1 [E2 D]]]]]].
    assert (Eq12: nth_error_string ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeqwertbabcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcababcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdbbaaaaeeeedddccccaaeeeedddccccabcabcabbcabcabcababcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaopasdfghjklzxcvblzxcvbedddccccalzxcvb"%string) i
                    = nth_error_string ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeqwertbabcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcababcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdbbaaaaeeeedddccccaaeeeedddccccabcabcabbcabcabcababcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaopasdfghjklzxcvblzxcvbedddccccalzxcvb"%string) (i + 1)).
    { subst i. simpl. reflexivity. }
    rewrite E0 in Eq12.
    rewrite E1 in Eq12.
    inversion Eq12.
    subst.
    destruct D as [Dab [Dac Dbc]].
    contradiction.
Qed.