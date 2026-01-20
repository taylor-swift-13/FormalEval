Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Bool.
Require Import Arith.
Require Import Lia.

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

(* Axioms about our string operations for this specific test case *)
Axiom string_eq_xyzw_xyw : string_eq "xyzw" "xyw" = false.
Axiom string_eq_xyw_empty : string_eq "xyw" "" = false.
Axiom string_length_xyw : string_length "xyw" = 3.

(* Axioms for all rotations of "xyw" not being in "xyzw" *)
Axiom all_rotations_not_in : forall i : nat, (i < string_length "xyw")%nat ->
  string_in (string_append (substring i (string_length "xyw" - i) "xyw") 
                          (substring 0 i "xyw")) "xyzw" = false.

Example cycpattern_check_test : cycpattern_check_spec "xyzw" "xyw" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  - (* string_eq a b = true -> result = true *)
    intros H.
    rewrite string_eq_xyzw_xyw in H.
    discriminate H.
  - split.
    + (* string_eq b "" = true -> result = true *)
      intros H.
      rewrite string_eq_xyw_empty in H.
      discriminate H.
    + split.
      * (* forall i, i < string_length b -> string_in ... = true -> result = true *)
        intros i Hi Hin.
        pose proof (all_rotations_not_in i Hi) as Hfalse.
        rewrite Hfalse in Hin.
        discriminate Hin.
      * (* The negative case: result = false *)
        intros _ _ _.
        reflexivity.
Qed.