Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Open Scope string_scope.

(* Definition of match_at as per specification *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Precondition (True as default) *)
Definition problem_18_pre (input substring : string) : Prop := True.

(* Specification definition *)
Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (* All indices in the list are valid matches *)
    (forall i, In i indices -> match_at i input substring) /\
    (* All valid matches are in the list *)
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    (* Output is the count of matches *)
    output = List.length indices.

(* Test case: input = "122", substring = "12mississippi2", output = 0 *)
Example test_problem_18_len_mismatch : problem_18_spec "122" "12mississippi2" 0.
Proof.
  unfold problem_18_spec.
  (* Since the substring is longer than the input, there are no matches. *)
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + (* forall i, In i [] -> ... *)
      intros i H_in.
      inversion H_in.
    + split.
      * (* forall i, ... -> In i [] *)
        intros i H_bound H_match.
        (* Simplify the bound condition: i + length "12mississippi2" <= length "122" *)
        (* length "12mississippi2" = 14, length "122" = 3 *)
        simpl in H_bound.
        (* i + 14 <= 3 is impossible for natural numbers *)
        lia.
      * (* output = length [] *)
        simpl.
        reflexivity.
Qed.