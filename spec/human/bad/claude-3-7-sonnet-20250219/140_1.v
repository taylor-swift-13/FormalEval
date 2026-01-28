Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

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
  | 0 => [] (* Should not happen if fuel is large enough *)
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
  string_of_list_ascii (fix_spaces_func (length s + 1) (list_ascii_of_string s)).

Definition problem_140_spec (s : string) (output : string) : Prop :=
  output = fix_spaces s.

(* Lemma: list_ascii_of_string (String c s) = c :: list_ascii_of_string s *)
Lemma list_ascii_of_string_cons :
  forall c s,
    list_ascii_of_string (String c s) = c :: list_ascii_of_string s.
Proof.
  reflexivity.
Qed.

(* Lemma: length of list_ascii_of_string s is String.length s *)
Lemma length_list_ascii_of_string :
  forall s,
    length (list_ascii_of_string s) = String.length s.
Proof.
  induction s; simpl.
  - reflexivity.
  - rewrite list_ascii_of_string_cons.
    simpl.
    f_equal.
    apply IHs.
Qed.

(* Lemma: fix_spaces_func is identity on lists with no spaces *)
Lemma fix_spaces_func_no_space_identity :
  forall fuel l,
    (forall c, In c l -> c <> space) ->
    fix_spaces_func fuel l = l.
Proof.
  intros fuel l Hno.
  revert fuel.
  induction l as [| c tl IH]; intros fuel; simpl.
  - reflexivity.
  - destruct fuel; [reflexivity|].
    destruct (Ascii.ascii_dec c space) as [Hc | Hc].
    + exfalso. apply (Hno c). left. assumption.
    + f_equal.
      apply IH.
      intros x Hx.
      apply Hno.
      right; assumption.
Qed.

(* Main test case: fix_spaces "Example" = "Example" *)
Lemma fix_spaces_test_Example :
  fix_spaces "Example" = "Example".
Proof.
  unfold fix_spaces.
  (* length "Example" = 7 *)
  rewrite length_list_ascii_of_string.
  (* Show that list_ascii_of_string "Example" contains no spaces *)
  assert (Hno_space : forall c, In c (list_ascii_of_string "Example") -> c <> space).
  {
    intros c Hin.
    (* list_ascii_of_string "Example" = ["E";"x";"a";"m";"p";"l";"e"] *)
    (* space = " " (ASCII code 32), none of these chars equal that *)
    repeat (destruct Hin as [Heq|Hin]; [subst; discriminate |]).
    contradiction.
  }
  (* fuel = length s + 1 = 7 +1 = 8 *)
  apply fix_spaces_func_no_space_identity with (fuel := 8) in Hno_space.
  now rewrite Hno_space.
Qed.