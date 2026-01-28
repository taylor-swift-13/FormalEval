Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

Definition problem_34_pre (input : list string) : Prop := True.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  Sorted string_le output /\
  NoDup output /\
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["alQd"; "dapple"; "banana"; "oralQdnge"] ["alQd"; "banana"; "dapple"; "oralQdnge"].
Proof.
  unfold problem_34_spec.
  split.
  {
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; vm_compute; exact I.
    - apply HdRel_cons; vm_compute; exact I.
    - apply HdRel_cons; vm_compute; exact I.
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