Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

Definition problem_34_pre (input : list string) : Prop := True.

Definition str_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  Sorted str_le output /\
  NoDup output /\
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["a"; "b"; "b"; "c"; "d"; "d"] ["a"; "b"; "c"; "d"].
Proof.
  unfold problem_34_spec.
  split.
  { 
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; simpl; exact I.
    - apply HdRel_cons; simpl; exact I.
    - apply HdRel_cons; simpl; exact I.
  }
  split.
  { 
    repeat apply NoDup_cons.
    all: try (simpl; intuition; discriminate).
    apply NoDup_nil.
  }
  { 
    intro z.
    split; intro H; simpl in *; intuition.
  }
Qed.