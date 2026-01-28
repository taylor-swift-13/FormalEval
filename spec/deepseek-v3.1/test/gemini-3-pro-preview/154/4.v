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

(* Test case: input = ["efef"; "fee"], output = true *)
Example test_cycpattern_check : cycpattern_check_spec "efef" "fee" true.
Proof.
  (* Unfold the specification to expose the logic *)
  unfold cycpattern_check_spec.
  
  (* The specification is a conjunction of 4 parts. 
     Since result is true, parts 1, 2, and 3 have the conclusion 'true = true', which is trivial.
     Part 4 has the conclusion 'true = false', so we must prove the premises are contradictory. *)
  split.
  { (* Case 1: Equality check. Conclusion is true = true. *)
    intro H. reflexivity.
  }
  
  split.
  { (* Case 2: Empty check. Conclusion is true = true. *)
    intro H. reflexivity.
  }

  split.
  { (* Case 3: Cyclic pattern check. Conclusion is true = true. *)
    intros i Hi HIn. reflexivity.
  }

  { (* Case 4: Negative result check. 
       We must show that the premises imply a contradiction because result is true.
       Specifically, the premise says "for all rotations, the string is NOT in 'efef'".
       We show that for rotation i=2 ("efe"), it IS in "efef". *)
    intros Hneq Hnotempty Hforall.
    
    (* Check rotation i=2. "fee" length is 3. i=2 is valid. *)
    assert (Hlen : (2 < string_length "fee")%nat).
    { vm_compute. lia. }
    
    (* Apply the hypothesis to i=2 *)
    specialize (Hforall 2 Hlen).
    
    (* Compute the check. Rotation of "fee" by 2 is "efe".
       "efe" is a substring of "efef", so string_in returns true. *)
    vm_compute in Hforall.
    
    (* Hforall is now "true = false", which is a contradiction. *)
    discriminate.
  }
Qed.