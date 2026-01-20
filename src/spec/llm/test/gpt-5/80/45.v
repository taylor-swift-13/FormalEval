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

Example test_is_happy_cabcabc: is_happy_spec ("cabcabc"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl; lia.
    + intros i Hi.
      destruct i as [|i1].
      * simpl in Hi.
        exists ("c"%char). exists ("a"%char). exists ("b"%char).
        split.
        -- simpl; reflexivity.
        -- split.
           ++ simpl; reflexivity.
           ++ split.
              ** simpl; reflexivity.
              ** split.
                 --- intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
                 --- split.
                     +++ intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
                     +++ intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
      * destruct i1 as [|i2].
        -- simpl in Hi.
           exists ("a"%char). exists ("b"%char). exists ("c"%char).
           split; [simpl; reflexivity|].
           split; [simpl; reflexivity|].
           split; [simpl; reflexivity|].
           split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
           split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
           intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
        -- destruct i2 as [|i3].
           --- simpl in Hi.
               exists ("b"%char). exists ("c"%char). exists ("a"%char).
               split; [simpl; reflexivity|].
               split; [simpl; reflexivity|].
               split; [simpl; reflexivity|].
               split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
               split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
               intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
           --- destruct i3 as [|i4].
               ---- simpl in Hi.
                    exists ("c"%char). exists ("a"%char). exists ("b"%char).
                    split; [simpl; reflexivity|].
                    split; [simpl; reflexivity|].
                    split; [simpl; reflexivity|].
                    split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
                    split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
                    intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
               ---- destruct i4 as [|i5].
                    ----- simpl in Hi.
                          exists ("a"%char). exists ("b"%char). exists ("c"%char).
                          split; [simpl; reflexivity|].
                          split; [simpl; reflexivity|].
                          split; [simpl; reflexivity|].
                          split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
                          split; [intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate|].
                          intro H; apply f_equal with (f:=nat_of_ascii) in H; simpl in H; discriminate.
                    ----- simpl in Hi; exfalso; lia.
Qed.