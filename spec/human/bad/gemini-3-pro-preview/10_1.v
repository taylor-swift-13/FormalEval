From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* Helper functions to convert between string and list ascii, 
   required for the palindrome definition provided. *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* Palindrome definition: reversed string equals itself *)
Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_pre : Prop := True.

(* Specification definition: Shortest palindrome that starts with input *)
Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
 forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

(* Test case: input = "", output = "" *)
Example test_problem_10_empty : problem_10_spec "" "".
Proof.
  (* Unfold the specification *)
  unfold problem_10_spec.
  
  (* The specification has a conjunction of 3 parts, break them down *)
  repeat split.
  
  - (* Part 1: Verify prefix "" "" = true *)
    (* In Coq's String.prefix implementation, prefix "" s is always true *)
    simpl.
    reflexivity.
    
  - (* Part 2: Verify palindrome "" *)
    unfold palindrome.
    simpl.
    (* "" converts to [], rev [] is [], which converts back to "" *)
    reflexivity.
    
  - (* Part 3: Verify minimality (length "" <= length p) *)
    intros p [Hprefix Hpalindrome].
    simpl.
    (* The length of "" is 0. Goal is 0 <= String.length p. *)
    (* Using lia (Linear Integer Arithmetic) to solve this inequality reliably *)
    lia.
Qed.