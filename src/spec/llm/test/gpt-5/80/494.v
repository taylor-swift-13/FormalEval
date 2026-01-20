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

Fixpoint find_dup (s : string) (i : nat) : option nat :=
  match s with
  | EmptyString => None
  | String a s' =>
    match s' with
    | EmptyString => None
    | String b s'' =>
      if Ascii.eqb a b then Some i else find_dup s' (S i)
    end
  end.

Example test_is_happy_long:
  is_happy_spec
    ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddcccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababaaaaabbbbccccdbcabcabcabcabbcabcabeedddccabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeedddbdccccbbbaaaaabbbdddccccaaeeeedddccccaabcabcabcababcabcabcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddcccabaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvb"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (K := match find_dup ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddcccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababaaaaabbbbccccdbcabcabcabcabbcabcabeedddccabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeedddbdccccbbbaaaaabbbdddccccaaeeeedddccccaabcabcabcababcabcabcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddcccabaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvb"%string) 0 with
                  | Some n => n
                  | None => 0
                  end).
    vm_compute in K.
    set (L := String.length ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddcccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababaaaaabbbbccccdbcabcabcabcabbcabcabeedddccabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeedddbdccccbbbaaaaabbbdddccccaaeeeedddccccaabcabcabcababcabcabcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddcccabaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvb"%string)).
    vm_compute in L.
    assert (K + 2 < L) by lia.
    destruct (Hall K H) as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    assert (Hsame :
      nth_error_string
        ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddcccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababaaaaabbbbccccdbcabcabcabcabbcabcabeedddccabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeedddbdccccbbbaaaaabbbdddccccaaeeeedddccccaabcabcabcababcabcabcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddcccabaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvb"%string) K
      =
      nth_error_string
        ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddcccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababaaaaabbbbccccdbcabcabcabcabbcabcabeedddccabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeedddbdccccbbbaaaaabbbdddccccaaeeeedddccccaabcabcabcababcabcabcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddcccabaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvb"%string) (K + 1)).
    { vm_compute. reflexivity. }
    rewrite Ha in Hsame.
    rewrite Hb in Hsame.
    inversion Hsame; subst.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab.
    reflexivity.
Qed.