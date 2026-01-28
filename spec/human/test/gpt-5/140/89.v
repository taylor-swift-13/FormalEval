Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

Fixpoint skip_spaces (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: tl =>
      if Ascii.ascii_dec c space then
        skip_spaces tl
      else
        l
  end.

Fixpoint fix_spaces_func (fuel : nat) (l : list ascii) : list ascii :=
  match fuel with
  | 0 => []
  | S n =>
      match l with
      | [] => []
      | c :: tl =>
          if Ascii.ascii_dec c space then
            match tl with
            | [] => [underscore]
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                  dash :: fix_spaces_func n (skip_spaces tl2)
                else
                  underscore :: fix_spaces_func n tl
            end
          else
            c :: fix_spaces_func n tl
      end
  end.

Definition fix_spaces (s : string) : string :=
  let l := list_ascii_of_string s in
  string_of_list_ascii (fix_spaces_func (length l + 1) l).

Definition problem_140_pre (s : string) : Prop := True.
Definition problem_140_spec (s : string) (output : string) : Prop :=
  output = fix_spaces s.

Example test_problem_140_case1:
  problem_140_spec
    "Thihappyw 123 p  spaces  eveThis is  a This This is  a This is  a  tes test  spaceNoSpacesHtry  where   spacees  This is  a sstevery  wher  s is  a Hello r  Woreld tsesst"
    "Thihappyw_123_p-spaces-eveThis_is-a_This_This_is-a_This_is-a-tes_test-spaceNoSpacesHtry-where-spacees-This_is-a_sstevery-wher-s_is-a_Hello_r-Woreld_tsesst".
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  vm_compute.
  reflexivity.
Qed.