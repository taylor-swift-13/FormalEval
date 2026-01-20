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

Lemma nth_error_string_Some_length:
  forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s as [|ch0 s' IH]; intros n ch H.
  - simpl in H. discriminate.
  - destruct n as [|n']; simpl in H.
    + inversion H. simpl. lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_big:
  is_happy_spec
    ("11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab7889901122334455660778899001122334455667788989001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab78899000deefffdefgcdefgabcdefg23344556677889900"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hn2: nth_error_string
      ("11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab7889901122334455660778899001122334455667788989001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab78899000deefffdefgcdefgabcdefg23344556677889900"%string) 2
      = Some ("2"%char)).
    { simpl. reflexivity. }
    pose proof (nth_error_string_Some_length
      ("11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab7889901122334455660778899001122334455667788989001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab78899000deefffdefgcdefgabcdefg23344556677889900"%string) 2 ("2"%char) Hn2) as Hcond.
    specialize (Hall 0).
    specialize (Hall Hcond).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    assert (Hn0: nth_error_string
      ("11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab7889901122334455660778899001122334455667788989001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab78899000deefffdefgcdefgabcdefg23344556677889900"%string) 0
      = Some ("1"%char)).
    { simpl. reflexivity. }
    rewrite Hn0 in Ha.
    inversion Ha; subst a.
    replace (0 + 1) with 1 in Hb by lia.
    assert (Hn1: nth_error_string
      ("11223364455667788990011223344556677889900112abcdefgabcdefgcedefgabcdefgagbcabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab7889901122334455660778899001122334455667788989001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaab7bccddeebcab78899000deefffdefgcdefgabcdefg23344556677889900"%string) 1
      = Some ("1"%char)).
    { simpl. reflexivity. }
    rewrite Hn1 in Hb.
    inversion Hb; subst b.
    replace (0 + 2) with 2 in Hc by lia.
    rewrite Hn2 in Hc.
    inversion Hc; subst c.
    destruct Hdist as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.