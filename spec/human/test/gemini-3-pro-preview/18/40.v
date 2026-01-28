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

(* Test case: input = "zz", substring = "efhello worrldssg", output = 0 *)
Example test_problem_18_case_2 : problem_18_spec "zz" "efhello worrldssg" 0.
Proof.
  unfold problem_18_spec.
  (* Since substring length (17) is greater than input length (2), there are no matches. *)
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + (* No indices in empty list *)
      intros i H_in.
      inversion H_in.
    + split.
      * (* Show that any match implies contradiction *)
        intros i H_bound H_match.
        simpl in H_bound.
        (* i + 17 <= 2 is impossible *)
        lia.
      * (* Output check *)
        simpl.
        reflexivity.
Qed.