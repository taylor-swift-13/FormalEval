Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.

Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Definition common_spec (l1 : list string) (l2 : list R) (out : list string) : Prop :=
  out = [].

Example test_common_spec : 
  common_spec 
    ["Ub"; "AxY"; "aPqcq"; "jJgIbabV"; "IQfz"; "iNL"; "oYmsXBI"; "uLVei"; ""] 
    [45.96597872747401%R; 41.109062991924844%R; -60.67086433231981%R; -35.672903633043234%R; 70.66502376502925%R; 45.96597872747401%R] 
    [].
Proof.
  unfold common_spec.
  reflexivity.
Qed.