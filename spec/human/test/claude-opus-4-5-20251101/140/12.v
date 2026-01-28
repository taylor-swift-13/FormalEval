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

Fixpoint count_spaces (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: tl =>
      if Ascii.ascii_dec c space then
        S (count_spaces tl)
      else
        0
  end.

Fixpoint fix_spaces_func (fuel : nat) (l : list ascii) : list ascii :=
  match fuel with
  | 0 => []
  | S n =>
      match l with
      | [] => []
      | c :: tl =>
          if Ascii.ascii_dec c space then
            let num_spaces := S (count_spaces tl) in
            let rest := skip_spaces tl in
            if Nat.leb 3 num_spaces then
              dash :: fix_spaces_func n rest
            else if Nat.eqb num_spaces 2 then
              underscore :: underscore :: fix_spaces_func n rest
            else
              underscore :: fix_spaces_func n rest
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

Example test_fix_spaces_Testing :
  problem_140_spec "Testing     1  2   3" "Testing-1__2-3".
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  simpl.
  reflexivity.
Qed.