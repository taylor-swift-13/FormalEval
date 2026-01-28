Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition problem_34_pre (input : list string) : Prop := True.

Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  Sorted string_le output /\
  NoDup output /\
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["apple"; "banana"; "d"; "orange"] ["apple"; "banana"; "d"; "orange"].
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
    split; intro H; exact H.
  }
Qed.