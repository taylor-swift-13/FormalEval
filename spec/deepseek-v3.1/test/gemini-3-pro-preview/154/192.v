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

(* Test case: input = ["cbbbaaaaccbbaaaccccabbaaacccccbbaaabbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaaaccccbbaaaccccbbaaabcaccccbbaaaaccccbothmicgloabaaaccccbbaaaccccbbaothmaicgloaaaccccbbaaabcdb"; "cdb"], output = true *)
Example test_cycpattern_check : cycpattern_check_spec "cbbbaaaaccbbaaaccccabbaaacccccbbaaabbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaaaccccbbaaaccccbbaaabcaccccbbaaaaccccbothmicgloabaaaccccbbaaaccccbbaothmaicgloaaaccccbbaaabcdb" "cdb" true.
Proof.
  (* Unfold the specification to expose the logic *)
  unfold cycpattern_check_spec.
  
  (* The result is true, so the first three implications are trivial (True -> True or False -> True),
     and the fourth implication (False -> False) requires proving the premise is False. *)
  split.
  { (* Case 1: Equality check *)
    intros _. reflexivity.
  }
  
  split.
  { (* Case 2: Empty check *)
    intros _. reflexivity.
  }

  split.
  { (* Case 3: Cyclic pattern check *)
    intros _ _ _. reflexivity.
  }

  { (* Case 4: Negative result check. 
       We need to show that the premises imply result=false.
       Since result=true, we must show the premises are contradictory.
       Specifically, the premise says "for all rotations, string is NOT in a".
       We show that rotation 0 ("cdb") IS in a, creating a contradiction. *)
    intros Hneq Hnotempty Hforall.
    
    (* Check rotation i = 0 *)
    specialize (Hforall 0).
    
    (* Prove 0 < length "cdb" (0 < 3) *)
    assert (Hlen: (0 < string_length "cdb")%nat).
    { vm_compute. lia. }
    
    apply Hforall in Hlen.
    (* Hlen is now: string_in "cdb" a = false *)
    
    (* Compute string_in "cdb" a to see it is true *)
    vm_compute in Hlen.
    
    (* true = false is a contradiction *)
    discriminate.
  }
Qed.