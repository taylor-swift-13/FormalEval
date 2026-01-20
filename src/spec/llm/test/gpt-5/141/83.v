Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.
Open Scope nat_scope.

Definition is_digitb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.

Definition is_upperb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 65 n && Nat.leb n 90.

Definition is_lowerb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 97 n && Nat.leb n 122.

Definition is_alphab (c : ascii) : bool := is_upperb c || is_lowerb c.

Fixpoint count_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if is_digitb c then S (count_digits s') else count_digits s'
  end.

Fixpoint count_char (s : string) (ch : ascii) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if ascii_dec c ch then S (count_char s' ch) else count_char s' ch
  end.

Definition starts_with_alpha (s : string) : Prop :=
  exists c s', s = String c s' /\ is_alphab c = true.

Definition suffix_in_allowed (suf : string) : Prop :=
  suf = "txt" \/ suf = "exe" \/ suf = "dll".

Definition valid_file_name (s : string) : Prop :=
  count_digits s <= 3 /\
  count_char s (ascii_of_nat 46) = 1 /\
  exists pref suf,
    s = pref ++ String (ascii_of_nat 46) EmptyString ++ suf /\
    pref <> EmptyString /\
    starts_with_alpha pref /\
    suffix_in_allowed suf.

Definition file_name_check_spec (file_name : string) (result : string) : Prop :=
  (valid_file_name file_name /\ result = "Yes") \/
  (~ valid_file_name file_name /\ result = "No").

Example file_name_check_example :
  file_name_check_spec "file.dolc" "No".
Proof.
  right.
  split.
  - intro H.
    destruct H as [Hdigits [Hdot [pref [suf [Hsplit [Hnonempty [Hstart Hsuf]]]]]]].
    destruct pref as [| c0 pref0].
    + apply Hnonempty. reflexivity.
    + simpl in Hsplit.
      inversion Hsplit; subst c0; clear Hsplit.
      rename H1 into Htail1.
      destruct pref0 as [| c1 pref1].
      * simpl in Htail1. inversion Htail1.
      * simpl in Htail1.
        inversion Htail1; subst c1; clear Htail1.
        rename H1 into Htail2.
        destruct pref1 as [| c2 pref2].
        -- simpl in Htail2. inversion Htail2.
        -- simpl in Htail2.
           inversion Htail2; subst c2; clear Htail2.
           rename H1 into Htail3.
           destruct pref2 as [| c3 pref3].
           --- simpl in Htail3. inversion Htail3.
           --- simpl in Htail3.
               inversion Htail3; subst c3; clear Htail3.
               rename H1 into Htail4.
               destruct pref3 as [| c4 pref4].
               ---- simpl in Htail4.
                    inversion Htail4; subst; clear Htail4.
                    unfold suffix_in_allowed in Hsuf.
                    destruct Hsuf as [Hsuf | [Hsuf | Hsuf]]; discriminate Hsuf.
               ---- simpl in Htail4.
                    inversion Htail4; subst c4; clear Htail4.
                    rename H1 into Htail5.
                    destruct pref4 as [| c5 pref5].
                    ++++ simpl in Htail5. inversion Htail5.
                    ++++ simpl in Htail5.
                         inversion Htail5; subst c5; clear Htail5.
                         rename H1 into Htail6.
                         destruct pref5 as [| c6 pref6].
                         ***** simpl in Htail6. inversion Htail6.
                         ***** simpl in Htail6.
                               inversion Htail6; subst c6; clear Htail6.
                               rename H1 into Htail7.
                               destruct pref6 as [| c7 pref7].
                               ****** simpl in Htail7. inversion Htail7.
                               ****** simpl in Htail7.
                                      inversion Htail7; subst c7; clear Htail7.
                                      rename H1 into Htail8.
                                      destruct pref7 as [| c8 pref8].
                                      ******* simpl in Htail8. inversion Htail8.
                                      ******* simpl in Htail8.
                                              inversion Htail8; subst c8; clear Htail8.
                                              rename H1 into Htail9.
                                              destruct pref8 as [| c9 pref9].
                                              ******** simpl in Htail9. inversion Htail9.
                                              ******** simpl in Htail9. inversion Htail9.
  - reflexivity.
Qed.