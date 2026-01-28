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

(* Test case: input = "zz", substring = "ababao", output = 0 *)
Example test_problem_18_sub_longer : problem_18_spec "zz" "ababao" 0.
Proof.
  unfold problem_18_spec.
  (* Since the substring is longer than the input, there are no matches. *)
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + intros i H_in.
      inversion H_in.
    + split.
      * intros i H_bound H_match.
        (* length "ababao" = 6, length "zz" = 2 *)
        (* i + 6 <= 2 is impossible *)
        simpl in H_bound.
        lia.
      * simpl.
        reflexivity.
Qed.