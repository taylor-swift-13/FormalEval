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

Example test_is_happy_long: is_happy_spec ("11223344556677889900112233445566778899001122334455667abcabcabca11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbddeefffdefgcdefgabcdefg23344556677889900baaaaab11223364455667788990011223344556677889900191223344556677889900cabcabcabaadbbccddeeaabbccddeebcab7889900"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 0).
    assert (0 + 2 < String.length "11223344556677889900112233445566778899001122334455667abcabcabca11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbddeefffdefgcdefgabcdefg23344556677889900baaaaab11223364455667788990011223344556677889900191223344556677889900cabcabcabaadbbccddeeaabbccddeebcab7889900"%string) as Hcond.
    { simpl; lia. }
    specialize (Hall Hcond).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    simpl in Ha.
    simpl in Hb.
    inversion Ha.
    inversion Hb.
    subst.
    destruct Hdist as [Hab _].
    apply Hab.
    reflexivity.
Qed.