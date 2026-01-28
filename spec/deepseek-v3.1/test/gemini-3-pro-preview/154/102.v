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

(* Test case: input = ["sisssonamississipit"; "siis"], output = true *)
Example test_cycpattern_check : cycpattern_check_spec "sisssonamississipit" "siis" true.
Proof.
  unfold cycpattern_check_spec.
  split.
  { intros. reflexivity. }
  split.
  { intros. reflexivity. }
  split.
  { intros. reflexivity. }
  {
    intros Hneq Hnotempty Hforall.
    (* We need to show a contradiction because result is true but the premise implies false.
       We show that for i=2, the cyclic pattern "issi" is in the string, contradicting Hforall. *)
    specialize (Hforall 2).
    assert (Hlt : (2 < string_length "siis")%nat).
    { vm_compute. lia. }
    apply Hforall in Hlt.
    vm_compute in Hlt.
    discriminate.
  }
Qed.