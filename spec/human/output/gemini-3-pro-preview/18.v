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

(* Test case: input = "", substring = "x", output = 0 *)
Example test_problem_18_empty_input : problem_18_spec "" "x" 0.
Proof.
  unfold problem_18_spec.
  (* Since the input is empty and substring "x" has length 1, there are no matches. *)
  (* We propose the empty list of indices. *)
  exists [].
  (* We use explicit splits to avoid ambiguity and ensure correct goal handling *)
  split.
  - (* NoDup [] *)
    apply NoDup_nil.
  - split.
    + (* forall i, In i [] -> match_at ... *)
      (* Since In i [] is False, this is trivial *)
      intros i H_in.
      inversion H_in.
    + split.
      * (* forall i, ... -> In i [] *)
        (* We need to show that no i satisfies the match condition *)
        intros i H_bound H_match.
        (* Simplify the bound condition: i + length "x" <= length "" *)
        (* length "x" = 1, length "" = 0 *)
        simpl in H_bound.
        (* i + 1 <= 0 is impossible for natural numbers *)
        lia.
      * (* output = length [] *)
        simpl.
        reflexivity.
Qed.