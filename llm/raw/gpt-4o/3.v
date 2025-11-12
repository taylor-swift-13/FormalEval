
Require Import List.
Require Import ZArith.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  exists account : Z,
    account = 0 /\
    (forall op : Z, In op operations -> account = account + op) /\
    ((exists op : Z, In op operations /\ account + op < 0 /\ result = true) \/
     (forall op : Z, In op operations -> account + op >= 0 /\ result = false)).
