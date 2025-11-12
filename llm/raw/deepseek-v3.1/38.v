
Require Import List String.
Import ListNotations.

Definition encode_cyclic_spec (s : string) (encoded : string) : Prop :=
  exists groups : list string,
    groups = map (fun i => substring (3 * i) (min 3 (length s - 3 * i)) s)
                 (seq 0 ((length s + 2) / 3)) /\
    encoded = concat (map (fun group => if length group =? 3 then substring 1 2 group ++ substring 0 1 group else group) groups).

Definition decode_cyclic_spec (s : string) (decoded : string) : Prop :=
  exists groups : list string,
    groups = map (fun i => substring (3 * i) (min 3 (length s - 3 * i)) s)
                 (seq 0 ((length s + 2) / 3)) /\
    decoded = concat (map (fun group => if length group =? 3 then substring 2 1 group ++ substring 0 2 group else group) groups).
