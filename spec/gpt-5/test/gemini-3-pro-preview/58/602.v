Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope R_scope.

Inductive Data : Type :=
| DStr (s : string)
| DReal (r : R).

Definition data_le (d1 d2 : Data) : Prop := True.

Definition common_spec (l1 l2 out : list Data) : Prop :=
  NoDup out
  /\ Sorted data_le out
  /\ forall x : Data, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [DStr "Ub"; DStr "AxY"; DStr "aPqcq"; DStr "jJgIbabV"; DStr "IQfz"; DStr "iNL"; DStr "oYmsXBI"; DStr "uLVei"; DStr ""] 
    [DReal 45.96597872747401%R; DReal 41.109062991924844%R; DReal (-60.67086433231981)%R; DReal (-35.672903633043234)%R; DReal 70.66502376502925%R] 
    [].
Proof.
  unfold common_spec.
  split.
  - constructor.
  - split.
    + constructor.
    + intros x; split.
      * intros H; inversion H.
      * intros [H1 H2].
        destruct x.
        -- simpl in H2.
           repeat (destruct H2 as [H2 | H2]; [ discriminate | ]).
           contradiction.
        -- simpl in H1.
           repeat (destruct H1 as [H1 | H1]; [ discriminate | ]).
           contradiction.
Qed.