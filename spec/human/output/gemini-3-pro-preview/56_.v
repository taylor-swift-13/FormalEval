Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Inductive definition of correctly bracketed strings *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition definition *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification definition *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Example Proof for Test Case: input = "<>", output = true *)
Example test_correct_bracketing_basic : problem_56_spec "<>" true.
Proof.
  (* Unfold the specification definition *)
  unfold problem_56_spec.
  
  (* Split the iff (<->) into two directions *)
  split.
  
  - (* Direction: true = true -> is_correctly_bracketed "<>" *)
    intros H.
    (* We need to prove is_correctly_bracketed "<>" *)
    (* Recognize that "<>" is structurally equivalent to "<" ++ "" ++ ">" *)
    change "<>" with ("<" ++ "" ++ ">").
    
    (* Apply the nesting constructor *)
    apply cb_nest.
    
    (* Now we need to prove is_correctly_bracketed "" *)
    (* Apply the nil constructor *)
    apply cb_nil.
    
  - (* Direction: is_correctly_bracketed "<>" -> true = true *)
    intros H.
    (* This is trivially true by reflexivity *)
    reflexivity.
Qed.