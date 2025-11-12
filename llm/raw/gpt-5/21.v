Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Open Scope R_scope.

Definition rescale_to_unit_spec (numbers : list R) (res : list R) : Prop :=
  2 <= length numbers /\
  exists m M : R,
    m < M /\
    (forall x, In x numbers -> m <= x /\ x <= M) /\
    In m numbers /\
    In M numbers /\
    res = map (fun x => (x - m) * (1 / (M - m))) numbers.