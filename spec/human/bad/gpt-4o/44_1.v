(* Required Coq Libraries *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.
Open Scope string_scope.

Import ListNotations.

(* Helper function to convert a digit character to a natural number *)
Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

(* Specification definition *)
Definition problem_44_pre (x : nat) (base : nat) : Prop := (base >= 2)%nat /\ (base < 10)%nat.

Definition problem_44_spec (x : nat) (base : nat) (output : list ascii) : Prop :=
  let digits := List.map nat_of_digit output in
  (Forall (fun d => d < base) digits) /\
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

(* Helper function to convert a string to a list of ascii characters *)
Definition list_ascii_of_string (s : string) : list ascii :=
  let fix aux n :=
    match n with
    | 0 => []
    | S n' => String.get (length s - n) s :: aux n'
    end
  in aux (length s).

(* Correct version of list_ascii_of_string function *)
Fixpoint string_to_list_ascii (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list_ascii s'
  end.

(* Example proof for change_base(8, 3) = "22" *)
Example test_case_1 : problem_44_pre 8 3 ->
  problem_44_spec 8 3 (string_to_list_ascii "22").
Proof.
  intros [base_ge2 base_lt10].
  unfold problem_44_spec.
  simpl.
  split.
  - (* Check that every digit is less than the base *)
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_nil.
  - (* Verify the representation matches the number *)
    simpl. lia.
Qed.

(* Example proof for change_base(8, 2) = "1000" *)
Example test_case_2 : problem_44_pre 8 2 ->
  problem_44_spec 8 2 (string_to_list_ascii "1000").
Proof.
  intros [base_ge2 base_lt10].
  unfold problem_44_spec.
  simpl.
  split.
  - (* Check that every digit is less than the base *)
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_nil.
  - (* Verify the representation matches the number *)
    simpl. lia.
Qed.

(* Example proof for change_base(7, 2) = "111" *)
Example test_case_3 : problem_44_pre 7 2 ->
  problem_44_spec 7 2 (string_to_list_ascii "111").
Proof.
  intros [base_ge2 base_lt10].
  unfold problem_44_spec.
  simpl.
  split.
  - (* Check that every digit is less than the base *)
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_cons; [lia |].
    apply Forall_nil.
  - (* Verify the representation matches the number *)
    simpl. lia.
Qed.

Close Scope nat_scope.
Close Scope string_scope.
Qed.