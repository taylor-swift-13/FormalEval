Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

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

(* Helpers for proving negative cyclic pattern checks on concrete strings *)
Definition check_not_cyclic_at (a b : string) (i : nat) : bool :=
  negb (string_in (string_append (substring i (string_length b - i) b) 
                                (substring 0 i b)) a).

Definition verify_not_cyclic (a b : string) : bool :=
  forallb (check_not_cyclic_at a b) (seq 0 (string_length b)).

Lemma verify_not_cyclic_correct : forall a b,
  verify_not_cyclic a b = true ->
  forall i, (i < string_length b)%nat ->
  string_in (string_append (substring i (string_length b - i) b) 
                          (substring 0 i b)) a = false.
Proof.
  intros a b H i Hi.
  unfold verify_not_cyclic in H.
  apply forallb_forall with (x := i) in H.
  - unfold check_not_cyclic_at in H.
    destruct (string_in _ _) eqn:E.
    + simpl in H. discriminate.
    + reflexivity.
  - apply in_seq. split; lia.
Qed.

(* Test case: input = ["abab...bbaa"; "bbba...aabc"], output = false *)
Example test_cycpattern_check : cycpattern_check_spec 
  "abababababababababababbbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaa" 
  "bbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaacaccccbbaaaccccbbaaaccccbbaaaccccbbaaabc" 
  false.
Proof.
  (* Unfold the specification to expose the logic *)
  unfold cycpattern_check_spec.
  
  (* We use explicit splits and braces to ensure the goal structure is handled correctly. *)
  split.
  { (* Case 1: Equality check. *)
    intro H.
    vm_compute in H.
    discriminate.
  }
  
  split.
  { (* Case 2: Empty check. *)
    intro H.
    vm_compute in H.
    discriminate.
  }

  split.
  { (* Case 3: Cyclic pattern check. 
       We must show that for all valid i, the cyclic string is NOT in a. 
       We use the helper lemma to verify this computationally. *)
    intros i Hi HIn.
    assert (Hchk: verify_not_cyclic 
      "abababababababababababbbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaa" 
      "bbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaacaccccbbaaaccccbbaaaccccbbaaaccccbbaaabc" 
      = true).
    { vm_compute. reflexivity. }
    pose proof (verify_not_cyclic_correct _ _ Hchk i Hi) as Hfalse.
    rewrite HIn in Hfalse. discriminate.
  }

  { (* Case 4: Negative result check. *)
    intros Hneq Hnotempty Hforall.
    reflexivity.
  }
Qed.