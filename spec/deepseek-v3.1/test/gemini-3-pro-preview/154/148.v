Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Local Open Scope string_scope.
Local Open Scope nat_scope.

(* Implementations of the abstract parameters using standard library functions *)
Definition string_append : string -> string -> string := String.append.
Definition string_length : string -> nat := String.length.
Definition string_eq : string -> string -> bool := String.eqb.

(* Implementation of string_in using String.index. 
   Returns true if s1 is a substring of s2. *)
Definition string_in (s1 s2 : string) : bool :=
  match String.index 0 s1 s2 with
  | Some _ => true
  | None => false
  end.

(* The specification definition *)
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

(* Helper for verifying non-existence of cyclic patterns computationally *)
Fixpoint check_rotations_false (a b : string) (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => 
    let rot := string_append (substring k (string_length b - k) b) (substring 0 k b) in
    match string_in rot a with
    | true => false
    | false => check_rotations_false a b k
    end
  end.

Lemma check_rotations_false_correct : forall a b n i,
  check_rotations_false a b n = true ->
  (i < n)%nat ->
  string_in (string_append (substring i (string_length b - i) b) (substring 0 i b)) a = false.
Proof.
  induction n; intros.
  - lia.
  - simpl in H.
    destruct (string_in (string_append (substring n (string_length b - n) b) (substring 0 n b)) a) eqn:Hcheck.
    + discriminate.
    + destruct (Nat.eq_dec i n).
      * subst. assumption.
      * apply IHn; try assumption. lia.
Qed.

(* Test case: input = ["vnzrhmweyyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd"; "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd"], output = false *)
Example test_cycpattern_check : cycpattern_check_spec "vnzrhmweyyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  {
    intro H.
    vm_compute in H.
    discriminate.
  }
  split.
  {
    intro H.
    vm_compute in H.
    discriminate.
  }
  split.
  {
    intros i Hi HIn.
    assert (HCheck: check_rotations_false "vnzrhmweyyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" (string_length "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd") = true).
    { vm_compute. reflexivity. }
    assert (HFalse: string_in (string_append (substring i (string_length "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" - i) "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd") (substring 0 i "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd")) "vnzrhmweyyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd" = false).
    { apply check_rotations_false_correct with (n := string_length "vnzrhmweyyvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd"); assumption. }
    rewrite HIn in HFalse. discriminate.
  }
  {
    intros. reflexivity.
  }
Qed.