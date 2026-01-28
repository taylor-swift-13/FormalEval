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

Fixpoint forall_nat (n : nat) (P : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S n' => P n' && forall_nat n' P
  end.

Lemma forall_nat_correct : forall n P, forall_nat n P = true -> forall i, i < n -> P i = true.
Proof.
  induction n; intros P H i Hi.
  - lia.
  - simpl in H. apply andb_true_iff in H. destruct H as [Hn Hrec].
    destruct (Nat.eq_dec i n).
    + subst. assumption.
    + apply IHn; try assumption. lia.
Qed.

Definition check_poly (a b : string) (i : nat) : bool :=
  negb (string_in (string_append (substring i (string_length b - i) b) (substring 0 i b)) a).

Definition valid_check (a b : string) := forall_nat (string_length b) (check_poly a b).

Definition input_a := "vnzrhmwehweyyrnilrxfziojjsvvuvcserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzhdwmnmvznryyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd".
Definition input_b := "vnzrhmwehweyyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzhdwmnmvznryyrnilrxfziojjsvvucserwzggunqinzqkihncxxfchhuxjvlquvdnxlirainugnaolmshzd".

Example test_cycpattern_check : cycpattern_check_spec input_a input_b false.
Proof.
  unfold cycpattern_check_spec.
  split.
  - intro H. vm_compute in H. discriminate.
  - split.
    + intro H. vm_compute in H. discriminate.
    + split.
      * intros i Hi HIn.
        assert (Hchk : valid_check input_a input_b = true) by (vm_compute; reflexivity).
        assert (Hall : check_poly input_a input_b i = true).
        { apply (forall_nat_correct _ _ Hchk). assumption. }
        unfold check_poly in Hall.
        rewrite HIn in Hall. simpl in Hall. discriminate.
      * intros _ _ _. reflexivity.
Qed.