Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Function definition for finding the longest string *)
Definition longest (input : list string) : option string :=
  match input with
  | [] => None
  | h :: t => Some (fold_left (fun acc s => if Nat.ltb (String.length acc) (String.length s) then s else acc) t h)
  end.

(* Specification of the problem *)
Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s /\ String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s /\ String.length s < String.length out)
  ).

(* Example test case and proof *)
Example test_case_1 : problem_12_spec [] (longest []).
Proof.
  unfold longest. simpl.
  left. split; reflexivity.
Qed.