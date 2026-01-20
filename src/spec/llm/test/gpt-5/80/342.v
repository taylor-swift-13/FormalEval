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

Example test_is_happy_nOyfaZf: is_happy_spec ("nOyfaZf"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl. lia.
    + intros i Hi.
      simpl in Hi.
      destruct i as [|i1].
      * exists "n"%char, "O"%char, "y"%char.
        split.
        -- simpl. reflexivity.
        -- split.
           ++ simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** unfold distinct3.
                 repeat split.
                 --- destruct (ascii_dec "n"%char "O"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                 --- destruct (ascii_dec "n"%char "y"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                 --- destruct (ascii_dec "O"%char "y"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
      * destruct i1 as [|i2].
        { exists "O"%char, "y"%char, "f"%char.
          split.
          - simpl. reflexivity.
          - split.
            + simpl. reflexivity.
            + split.
              * simpl. reflexivity.
              * unfold distinct3. repeat split.
                -- destruct (ascii_dec "O"%char "y"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                -- destruct (ascii_dec "O"%char "f"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                -- destruct (ascii_dec "y"%char "f"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
        }
        { destruct i2 as [|i3].
          { exists "y"%char, "f"%char, "a"%char.
            split.
            - simpl. reflexivity.
            - split.
              + simpl. reflexivity.
              + split.
                * simpl. reflexivity.
                * unfold distinct3. repeat split.
                  -- destruct (ascii_dec "y"%char "f"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                  -- destruct (ascii_dec "y"%char "a"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                  -- destruct (ascii_dec "f"%char "a"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
          }
          { destruct i3 as [|i4].
            { exists "f"%char, "a"%char, "Z"%char.
              split.
              - simpl. reflexivity.
              - split.
                + simpl. reflexivity.
                + split.
                  * simpl. reflexivity.
                  * unfold distinct3. repeat split.
                    -- destruct (ascii_dec "f"%char "a"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                    -- destruct (ascii_dec "f"%char "Z"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                    -- destruct (ascii_dec "a"%char "Z"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
            }
            { destruct i4 as [|i5].
              { exists "a"%char, "Z"%char, "f"%char.
                split.
                - simpl. reflexivity.
                - split.
                  + simpl. reflexivity.
                  + split.
                    * simpl. reflexivity.
                    * unfold distinct3. repeat split.
                      -- destruct (ascii_dec "a"%char "Z"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                      -- destruct (ascii_dec "a"%char "f"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
                      -- destruct (ascii_dec "Z"%char "f"%char) as [Heq|Hne]; [inversion Heq|exact Hne].
              }
              { exfalso. lia. }
            }
          }
        }
Qed.