Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

Fixpoint count_spaces (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: tl =>
      if Ascii.ascii_dec c space then
        S (count_spaces tl)
      else
        0
  end.

Fixpoint skip_n_spaces (n : nat) (l : list ascii) : list ascii :=
  match n with
  | 0 => l
  | S m =>
      match l with
      | [] => []
      | c :: tl =>
          if Ascii.ascii_dec c space then
            skip_n_spaces m tl
          else
            l
      end
  end.

Fixpoint repeat_char (c : ascii) (n : nat) : list ascii :=
  match n with
  | 0 => []
  | S m => c :: repeat_char c m
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
            if Nat.leb num_spaces 2 then
              repeat_char underscore num_spaces ++ fix_spaces_func n (skip_n_spaces (num_spaces - 1) tl)
            else
              dash :: fix_spaces_func n (skip_n_spaces (num_spaces - 1) tl)
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

Example test_fix_spaces_spaces_everywhere :
  problem_140_spec "  spaces  eveery  where  " "__spaces__eveery__where__".
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  simpl.
  reflexivity.
Qed.