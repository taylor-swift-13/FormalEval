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

Definition tail : string :=
  "aaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee4556677889900abcdefgabcdefgcdefgabcagbaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgbbccddeeaabbccddddeeaabbccddeebcab7889900deefff"%string.

Example test_is_happy_long: is_happy_spec ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee4556677889900abcdefgabcdefgcdefgabcagbaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgbbccddeeaabbccddddeeaabbccddeebcab7889900deefff"%string) false.
Proof.
  change ("abcccaaabbd11223344556607788990abcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee4556677889900abcdefgabcdefgcdefgabcagbaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzbababababababababababababababababababababababdecfgabcdefgcdefgabcdefgbbccddeeaabbccddddeeaabbccddeebcab7889900deefff"%string)
    with (String.append "abccc"%string tail).
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (Hlt: 2 + 2 < String.length (String.append "abccc"%string tail)).
    { repeat (unfold String.append; simpl). lia. }
    specialize (Hforall 2 Hlt).
    destruct Hforall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    repeat (unfold String.append in Ha; simpl in Ha).
    repeat (unfold String.append in Hb; simpl in Hb).
    repeat (unfold String.append in Hc; simpl in Hc).
    inversion Ha; inversion Hb; inversion Hc; subst.
    destruct Hdist as [Hab [Hac Hbc]].
    apply Hab; reflexivity.
Qed.