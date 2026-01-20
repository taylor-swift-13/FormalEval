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

Example test_is_happy_this_is_hb: is_happy_spec (" this is hb"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl; lia.
    + intros i Hi.
      destruct i as [|i1].
      * exists (" "%char), ("t"%char), ("h"%char).
        split.
        { simpl; reflexivity. }
        split.
        { simpl; reflexivity. }
        split.
        { simpl; reflexivity. }
        unfold distinct3; repeat split; congruence.
      * destruct i1 as [|i2].
        { exists ("t"%char), ("h"%char), ("i"%char).
          split.
          { simpl; reflexivity. }
          split.
          { simpl; reflexivity. }
          split.
          { simpl; reflexivity. }
          unfold distinct3; repeat split; congruence. }
        { destruct i2 as [|i3].
          { exists ("h"%char), ("i"%char), ("s"%char).
            split.
            { simpl; reflexivity. }
            split.
            { simpl; reflexivity. }
            split.
            { simpl; reflexivity. }
            unfold distinct3; repeat split; congruence. }
          { destruct i3 as [|i4].
            { exists ("i"%char), ("s"%char), (" "%char).
              split.
              { simpl; reflexivity. }
              split.
              { simpl; reflexivity. }
              split.
              { simpl; reflexivity. }
              unfold distinct3; repeat split; congruence. }
            { destruct i4 as [|i5].
              { exists ("s"%char), (" "%char), ("i"%char).
                split.
                { simpl; reflexivity. }
                split.
                { simpl; reflexivity. }
                split.
                { simpl; reflexivity. }
                unfold distinct3; repeat split; congruence. }
              { destruct i5 as [|i6].
                { exists (" "%char), ("i"%char), ("s"%char).
                  split.
                  { simpl; reflexivity. }
                  split.
                  { simpl; reflexivity. }
                  split.
                  { simpl; reflexivity. }
                  unfold distinct3; repeat split; congruence. }
                { destruct i6 as [|i7].
                  { exists ("i"%char), ("s"%char), (" "%char).
                    split.
                    { simpl; reflexivity. }
                    split.
                    { simpl; reflexivity. }
                    split.
                    { simpl; reflexivity. }
                    unfold distinct3; repeat split; congruence. }
                  { destruct i7 as [|i8].
                    { exists ("s"%char), (" "%char), ("h"%char).
                      split.
                      { simpl; reflexivity. }
                      split.
                      { simpl; reflexivity. }
                      split.
                      { simpl; reflexivity. }
                      unfold distinct3; repeat split; congruence. }
                    { destruct i8 as [|i9].
                      { exists (" "%char), ("h"%char), ("b"%char).
                        split.
                        { simpl; reflexivity. }
                        split.
                        { simpl; reflexivity. }
                        split.
                        { simpl; reflexivity. }
                        unfold distinct3; repeat split; congruence. }
                      { exfalso. simpl in Hi. lia. }}}}}}}}
Qed.