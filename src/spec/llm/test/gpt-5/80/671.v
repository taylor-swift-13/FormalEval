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

Example test_is_happy_long: is_happy_spec ("qwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa11223344556677889900112233445566778899b00112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvb"%string) false.
Proof.
  set (s := "qwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa11223344556677889900112233445566778899b00112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvb"%string).
  change (is_happy_spec s false).
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hi: 28 + 2 < String.length s).
    { vm_compute; lia. }
    specialize (Hall 28 Hi).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    assert (E28: nth_error_string s 28 = Some "a"%char).
    { vm_compute; reflexivity. }
    assert (E29: nth_error_string s (28 + 1) = Some "a"%char).
    { vm_compute; reflexivity. }
    rewrite E28 in Ha. inversion Ha; subst a.
    rewrite E29 in Hb. inversion Hb; subst b.
    destruct Hdist as [Hab _].
    apply Hab; reflexivity.
Qed.