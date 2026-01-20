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

Example test_is_happy_long: is_happy_spec ("ababa112233445566778899001122334abcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefg4556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900bababababababababababababababababababababab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (H02 : 0 + 2 < String.length ("ababa112233445566778899001122334abcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefg4556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900bababababababababababababababababababababab"%string)) by lia.
    specialize (Hall 0 H02).
    destruct Hall as [a0 [b0 [c0 [Ha0 [Hb0 [Hc0 Hdist]]]]]].
    simpl in Ha0.
    inversion Ha0; subst a0; clear Ha0.
    simpl in Hc0.
    inversion Hc0; subst c0; clear Hc0.
    destruct Hdist as [_ [Hac _]].
    apply Hac; reflexivity.
Qed.