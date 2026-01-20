
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Datatypes.
Import ListNotations.

Definition largest_smallest_integers_spec (lst : list Z) (res : option Z * option Z) : Prop :=
  let neg := filter (fun x => Z.ltb x 0) lst in
  let pos := filter (fun x => Z.gtb x 0) lst in
  res =
    (match neg with
     | [] => None
     | _ => Some (fold_left Z.max neg (hd 0 neg))
     end,
     match pos with
     | [] => None
     | _ => Some (fold_left Z.min pos (hd 0 pos))
     end).
