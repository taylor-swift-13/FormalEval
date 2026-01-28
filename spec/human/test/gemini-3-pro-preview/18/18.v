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

(* Test case: input = "122", substring = "zz", output = 0 *)
Example test_problem_18_122_zz : problem_18_spec "122" "zz" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + intros i H_in. inversion H_in.
    + split.
      * intros i H_bound H_match.
        unfold match_at in H_match.
        destruct H_match as [_ [_ H_eq]].
        simpl in H_bound.
        (* i + 2 <= 3 implies i = 0 or i = 1 *)
        assert (i = 0 \/ i = 1) as H_cases by lia.
        destruct H_cases as [H0 | H1]; subst.
        -- (* Case i = 0 *)
           specialize (H_eq 0).
           assert (0 < 2) as H_lt by lia.
           specialize (H_eq H_lt).
           simpl in H_eq.
           inversion H_eq.
        -- (* Case i = 1 *)
           specialize (H_eq 0).
           assert (0 < 2) as H_lt by lia.
           specialize (H_eq H_lt).
           simpl in H_eq.
           inversion H_eq.
      * simpl. reflexivity.
Qed.