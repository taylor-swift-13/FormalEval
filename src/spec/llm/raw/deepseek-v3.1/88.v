
Require Import List ZArith.
Import ListNotations.

Definition sort_array_spec (array : list Z) (result : list Z) : Prop :=
  Forall (fun x => x >= 0) array /\
  match array with
  | [] => result = []
  | _ => 
      let first := hd 0 array in
      let last := last array 0 in
      (first + last) mod 2 = 1 -> result = sorted_asc array /\
      (first + last) mod 2 = 0 -> result = sorted_desc array
  end.
