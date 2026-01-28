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

(* Test case: input = ["siss"; "iscracecardeis"], output = false *)
Example test_cycpattern_check : cycpattern_check_spec "siss" "iscracecardeis" false.
Proof.
  (* Unfold the specification to expose the logic *)
  unfold cycpattern_check_spec.
  
  (* The specification is a conjunction of 4 parts: A /\ B /\ C /\ D. *)
  split.
  { (* Case 1: Equality check. 
       "siss" == "iscracecardeis" is false, so the implication holds. *)
    intro H.
    vm_compute in H.
    discriminate.
  }
  
  split.
  { (* Case 2: Empty check. 
       "iscracecardeis" == "" is false, so the implication holds. *)
    intro H.
    vm_compute in H.
    discriminate.
  }

  split.
  { (* Case 3: Cyclic pattern check. 
       We must show that for all valid i, the cyclic string is NOT in "siss". 
       Since the premise assumes it IS in "siss", we derive a contradiction. *)
    intros i Hi HIn.
    (* "iscracecardeis" has length 14. We check i = 0 to 13. 
       Since length of "iscracecardeis" (14) > length of "siss" (4), 
       string_in will always be false. *)
    do 14 (destruct i; [ vm_compute in HIn; discriminate | ]).
    (* i >= 14 *)
    (* This contradicts the length condition i < 14 *)
    vm_compute in Hi. lia.
  }

  { (* Case 4: Negative result check. 
       We need to show result=false follows from the premises. 
       Since result is already false in the goal, this is trivial. *)
    intros Hneq Hnotempty Hforall.
    reflexivity.
  }
Qed.