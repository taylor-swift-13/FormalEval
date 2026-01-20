Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.

Parameter string_append : string -> string -> string.
Parameter string_in : string -> string -> bool.
Parameter string_eq : string -> string -> bool.
Parameter string_length : string -> nat.

Definition cycpattern_check_spec (a : string) (b : string) (result : bool) : Prop :=
  (string_eq a b = true -> result = true) /\
  (string_eq b "" = true -> result = true) /\
  (forall (i : nat), (i < string_length b)%nat ->
    string_in (string_append (substring i (string_length b - i) b)
                             (substring 0 i b)) a = true -> result = true) /\
  ((string_eq a b = false) ->
   (string_eq b "" = false) ->
   (forall (i : nat), (i < string_length b)%nat ->
    string_in (string_append (substring i (string_length b - i) b)
                             (substring 0 i b)) a = false) -> result = false).

Axiom string_eq_xyzw_xyw_false : string_eq "xyzw" "xyw" = false.
Axiom string_eq_xyw_empty_false : string_eq "xyw" "" = false.
Axiom rotations_of_xyw_not_in_xyzw :
  forall i, (i < string_length "xyw")%nat ->
    string_in (string_append (substring i (string_length "xyw" - i) "xyw")
                             (substring 0 i "xyw")) "xyzw" = false.

Example cycpattern_check_spec_xyzw_xyw_false :
  cycpattern_check_spec "xyzw" "xyw" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  intros H. exfalso. rewrite string_eq_xyzw_xyw_false in H. discriminate.
  split.
  intros H. exfalso. rewrite string_eq_xyw_empty_false in H. discriminate.
  split.
  intros i Hi Hin. exfalso.
  pose proof (rotations_of_xyw_not_in_xyzw i Hi) as Hrot.
  rewrite Hrot in Hin.
  discriminate Hin.
  intros _ _ _. reflexivity.
Qed.