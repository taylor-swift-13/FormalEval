Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope char_scope.

Definition char_to_bool (c : ascii) : bool :=
  if ascii_dec c "1" then true else false.

Definition bool_to_char (b : bool) : ascii :=
  if b then "1" else "0".

Definition xor_ascii (c1 c2 : ascii) : ascii :=
  bool_to_char (xorb (char_to_bool c1) (char_to_bool c2)).

Definition string_xor_spec (a b result : string) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  let lr := list_ascii_of_string result in
  length lr = length la /\
  forall i, (i < length la)%nat ->
    nth i lr "0" = xor_ascii (nth i la "0") (nth i lb "0").

Fixpoint check_string_xor_list (la lb lr : list ascii) : bool :=
  match la, lb, lr with
  | [], [], [] => true
  | a :: la', b :: lb', r :: lr' =>
      if ascii_dec r (xor_ascii a b) then check_string_xor_list la' lb' lr' else false
  | _, _, _ => false
  end.

Lemma check_string_xor_correct : forall la lb lr,
  check_string_xor_list la lb lr = true ->
  length lr = length la /\
  forall i, (i < length la)%nat ->
    nth i lr "0" = xor_ascii (nth i la "0") (nth i lb "0").
Proof.
  induction la as [|a la' IH]; destruct lb as [|b lb']; destruct lr as [|r lr']; simpl; intros H; try discriminate.
  - split. reflexivity. intros i Hi. lia.
  - destruct (ascii_dec r (xor_ascii a b)) as [Heq | Hneq].
    + apply IH in H. destruct H as [Hlen Hnth].
      split.
      * f_equal. assumption.
      * intros i Hi. destruct i.
        -- subst. reflexivity.
        -- apply Hnth. lia.
    + discriminate.
Qed.

Example test_xor : string_xor_spec "110101001001110101011010100100110101010100101000" "110101001001110101011010100100110101010100101000" "000000000000000000000000000000000000000000000000".
Proof.
  unfold string_xor_spec.
  apply check_string_xor_correct.
  vm_compute.
  reflexivity.
Qed.