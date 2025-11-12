
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (res : bool) : Prop :=
  res = true <-> exists prefix, 
    prefix ++ _ = operations /\
    let balance := fold_left Z.add prefix 0 in
    balance < 0 /\
    (forall prefix', length prefix' < length prefix -> fold_left Z.add prefix' 0 >= 0).
