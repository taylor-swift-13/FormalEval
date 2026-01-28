Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.Ascii.
Require Import Lia.

Open Scope string_scope.

(* Specification as given *)
Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

(* Define equality test on option ascii *)
Definition eq_option_ascii (a b : option ascii) : bool :=
  match a, b with
  | Some x, Some y => if ascii_dec x y then true else false
  | None, None => true
  | _, _ => false
  end.

(* Use Program Fixpoint to avoid "Cannot guess decreasing argument" error *)
Require Import Program.

Program Fixpoint is_palindrome_aux (s : string) (start len : nat) {measure len} : bool :=
  match len with
  | 0 | 1 => true
  | S (S len') =>
    if eq_option_ascii (String.get start s) (String.get (start + len - 1) s)
    then is_palindrome_aux s (start + 1) (len - 2)
    else false
  end.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.

Definition is_palindrome (s : string) : bool :=
  is_palindrome_aux s 0 (String.length s).

(* Example proof: input = "" with output = true *)

Example problem_48_example_empty :
  problem_48_spec "" true.
Proof.
  unfold problem_48_spec.
  split; intros H.
  - intros i Hi.
    (* length "" = 0, so half length = 0, i < 0 is false *)
    simpl in Hi.
    lia.
  - reflexivity.
Qed.