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

(* Test case: input = ["xbQkq"; "xbQkq"], output = true *)
Example test_cycpattern_check : cycpattern_check_spec "xbQkq" "xbQkq" true.
Proof.
  (* Unfold the specification to expose the logic *)
  unfold cycpattern_check_spec.
  
  (* The specification is a conjunction of 4 parts *)
  split.
  { (* Case 1: Equality check. 
       "xbQkq" == "xbQkq" is true, result is true.
       true -> true holds trivially. *)
    intro H.
    reflexivity.
  }
  
  split.
  { (* Case 2: Empty check. 
       "xbQkq" == "" is false. 
       false -> true holds trivially. *)
    intro H.
    reflexivity.
  }

  split.
  { (* Case 3: Cyclic pattern check. 
       We need to show result=true follows from the premises.
       Since result is already true in the goal, this is trivial. *)
    intros i Hi HIn.
    reflexivity.
  }

  { (* Case 4: Negative result check. 
       We need to show result=false follows from the premises.
       However, the first premise is (string_eq "xbQkq" "xbQkq" = false).
       Since "xbQkq" == "xbQkq" is true, this premise is false (true = false), 
       creating a contradiction. *)
    intros Hneq Hnotempty Hforall.
    vm_compute in Hneq.
    discriminate.
  }
Qed.